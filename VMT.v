(*
  synchronous code gen (dropbox)
  Lustre: dependance inconditionnelle
  Signal: dependance conditionnelle

  x1 = x + 1 when x > 0
  y1 = y + 1 when y > 0
  z = x1 default y1
  t = z + 1
  ===================
  horloge : dependance
  ^x1 : x --> x1
  ^x1 : cx --> x1
  ^x : x --> cx
  ^y1 : y --> y1
  ^y1 : cy --> y1
  ^y : y --> cy
  ^x1 : x1 --> z
  ^y1-^x1 : y1 --> z
  ^z : z --> t
  horloge : update 
   ^x1 : x1 = x+1
   ^y1 : y1 = y+1
   ^x1 : z = x1
   ^y1-^x1 : z = y1
   ^x : cx = (x>0)
   ^y : cy = (y>0)
   ^z : t = z+1
  ===================
  horloges:
     [cx] => ^x
     [cy] => ^y
    ^x1 = ^x * [cx]
    ^y1 = ^y * [cy]
    ^z = ^x1+^y1
    ^t = ^z
    
    resolution => 
      calcul des horloges en fonction d'entrees 
          ou creation d'horloges en entree
      contraintes sur les entrees
          de presence
          de valeur (warning Polychrony)
      plusieurs solutions => choix par le compilateur
      prise en compte des nouvelles equations pour les dependances
  exemple
  
    dep(? integer x; ! integer r;) 
    (|
        i := x when (x > 0)
     | r := x+i
    |) where integer i;

  ==================
  analyse statique: 
    pas de contraintes de valeur sur les entrees (sinon deadlock)
    le programme est-il determiste ? (master clock) - pas une obligation
    recherche de cycles potentiels:
       une solution du systeme d'equations d'horloges n'est pas un modele de la conjonction des etiquettes d'un cycle
    equivalence / inclusion d'horloges
       --> arbre de classes

===================================

Data Control Graph = Clock Hierarchy + Conditional Precedence Graph

Compilation of Polychronous DataFlow equations
https://hal.inria.fr/inria-00540493/document

Synthesis Of Embedded Software Frameworks And Methodologies For Correctness By Construction
*)

Require Import MSetList.

Set Implicit Arguments.

Parameter Var: Type.
Parameter V_eq_dec: forall v w:Var, {v=w}+{v<>w}.
Parameter Data: Type.
Parameter isTrue: Data -> Prop. (* non bool ou true *)
Parameter Mem: Var -> Prop.
Parameter Inp: Var -> Prop. (* contient Mem *)
Parameter Inp_dec: forall v, {Inp v}+{~Inp v}.

Module SV.
  Inductive set : Type := 
    empty
  | sing (v:Var)
  | union (s1 s2: set)
  | inter (s1 s2: set)
  | diff (s1 s2: set)
  | Union {T} (P: T -> Prop) (f: forall v, P v -> set)
  | UNION (P: Var -> Prop) (Q: set) (f: forall v, P v -> set).

  Inductive In v: set -> Prop :=
  | InSing: forall w, v=w -> In v (sing w) 
  | InUnion_l: forall s1 s2, In v s1 -> In v (union s1 s2)
  | InUnion_r: forall s1 s2, In v s2 -> In v (union s1 s2)
  | InInter: forall s1 s2, In v s1 -> In v s2 -> In v (inter s1 s2)
  | InDiff: forall s1 s2, In v s1 -> NotIn v s2 -> In v (diff s1 s2)
  | InGUnion: forall T (P: T -> Prop)  f w (h: P w), In v (f w h) -> In v (Union P f) 
  | InGUNION: forall (P: Var -> Prop) (Q: set) f w (h: P w), In w Q -> In v (f w h) -> In v (UNION P Q f) 
   with NotIn v: set -> Prop :=
  | NotInEmpty: NotIn v empty
  | NotInSing: forall w, v<>w -> NotIn v (sing w) 
  | NotInInter_l: forall s1 s2, NotIn v s1 -> NotIn v (inter s1 s2)
  | NotInInter_r: forall s1 s2, NotIn v s2 -> NotIn v (inter s1 s2)
  | NotInUnion: forall s1 s2, NotIn v s1 -> NotIn v s2 -> NotIn v (union s1 s2)
  | NotInDiff_l: forall s1 s2, NotIn v s1 -> NotIn v (diff s1 s2)
  | NotInDiff_r: forall s1 s2, In v s2 -> NotIn v (diff s1 s2)
  | NotInGUnion: forall T (P: T -> Prop) f, (forall w (h: P w),  NotIn v (f w h)) -> NotIn v (Union P f)
  | NotInGUNION: forall (P: Var -> Prop) (Q: set) f, (forall w (h: P w), NotIn w Q \/ NotIn v (f w h)) -> NotIn v (UNION P Q f).

  Definition is_empty s := forall v, ~In v s.
  Definition subset s1 s2 := forall v, In v s1 -> In v s2.
  Definition disjoint s1 s2 := forall v, not (In v s1 /\ In v s2).
  Definition GUnion (d : set) (f: forall v, In v d -> set) := Union (fun x => In x d) f.
  Definition GUNION (d : set) (s: set) (f: forall v, In v d -> set) := UNION (fun x => In x d) s f.
  Lemma InUnion: forall v s1 s2, In v (union s1 s2) -> {In v s1}+{In v s2}.
  Admitted.
  Lemma NotInLRNotInUnion: forall v s1 s2, ~In v s1 -> ~In v s2 -> ~In v (union s1 s2).
  Admitted.
  Lemma InDiff_l: forall v s1 s2, In v (diff s1 s2) -> In v s1.
  Admitted.
  Lemma In_dec: forall v s, {In v s}+{~In  v s}.
  Admitted.
  Lemma InUnionNotl: forall v s1 s2, In v (union s1 s2) -> ~In v s1 -> In v s2.
  Admitted.
  Lemma NotInLDiff: forall v s1 s2, ~In v s1 -> ~In v (diff s1 s2).
  Admitted.
  Lemma NotIn_l : forall v s, ~In v s -> NotIn v s.
  Admitted.
End SV.

Definition State := Var -> Data.

Inductive Clk (V: SV.set) :=
  isT: forall v, SV.In v V -> Clk V
| CTrue : Clk V.

Definition check {V: SV.set} (env: forall v, SV.In v V -> Data) (c: Clk V) :=
 match c with
    isT is_V => isTrue (env _ is_V)
 | CTrue _ => True
 end.

Definition acheck {V: SV.set} (env: forall v, SV.In v V -> Prop) (c: Clk V) :=
 match c with
    isT is_V => env _ is_V
 | CTrue _ => True
 end.

Lemma acheckOK: forall (V: SV.set) (env: forall v, SV.In v V -> Data) (c: Clk V),
  acheck (fun v iv => isTrue (env v iv)) c -> check env c.
Proof.
  intros.
  destruct c; simpl in *; auto.
Qed.

Class Library := {
  Fname: Type;
  Farity: Fname -> Type;
  Fsem: forall f, (Farity f -> Data) -> Data
}.
Instance Lib: Library.
Admitted.

Inductive Exp :=
  eVar (v: Var)
| eConj (a: SV.set)
| eFun (f: Fname) (a: Farity f -> Exp).

Fixpoint eDep e :=
  match e with
    eVar v => SV.sing v
  | eConj a => a
  | eFun f a => SV.Union (fun _ => True) (fun i _ => eDep (a i ))
  end.

Inductive switch T :=
  sTest (v: Var) (ift: switch T) (iff: switch T)
| sVal (v: T).

Fixpoint sDep {T} (s: switch T) :=
  match s with
    sTest s t f => SV.union (SV.sing s) (SV.union (sDep t) (sDep f)) 
  | sVal v => SV.empty
  end.

(* condition d'acyclicite *)
(* pb: approche compositionnelle donc pb *)
(* pb: conditions dynamiques, dep dynamique *)

Structure Node := {
  ACtrl: SV.set;
  AMode: Type;
  ASelect: switch AMode;
  ASelectDep: SV.subset (sDep ASelect) ACtrl;
  AOut: AMode -> SV.set;
  AValue: forall m o (is_o: SV.In o (AOut m)), Exp;
  ADep m o (is_o: SV.In o (AOut m)) := eDep (AValue is_o);
  AInOut: forall m o (h: SV.In o (AOut m)), ~SV.In o (ADep h);
}.

Require Import Coq.Program.Tactics.

Definition rest {T D1} D2 (f: forall v, SV.In v D1 -> T) (h: SV.subset D2 D1): forall v, SV.In v D2 -> T :=
  fun v in2 => f v (h v in2).

Definition par_out (N1 N2: Node) (m: AMode N1 * AMode N2) := 
  let (m1,m2) := m in
    SV.union
      (SV.diff (AOut N1 m1) (SV.GUnion (ADep N2 m2)))
      (SV.diff (AOut N2 m2) (SV.GUnion (ADep N1 m1))).

Definition par_val (N1 N2: Node) (m: AMode N1 * AMode N2) o:
  forall (is_o: SV.In o (par_out N1 N2 m)), Exp :=
     let (m1,m2) return 
        forall (is_o: SV.In o (par_out N1 N2 m)), Exp
        := m in
     fun (is_o: SV.In o (par_out N1 N2 (m1,m2))) =>
     match SV.In_dec o (AOut N1 m1) with
      left is1 => @AValue N1 m1 o is1
        (fun i i_in => match SV.In_dec i (AOut N2 m2) with
          left o2 => @AValue N2 m2 i o2 (rest V _) 
        | right no2 => V i _
         end)
    | right nis1 =>
      match SV.In_dec o (AOut N2 m2) with
      | left is2 => @AValue N2 m2 o is2
          (fun i i_in => match SV.In_dec i (AOut N1 m1) with
            left o1 => @AValue N1 m1 i o1 (rest V _) 
          | right no1 => V i _
           end)
     | right nis2 => match SV.NotInLRNotInUnion (SV.NotInLDiff nis1) (SV.NotInLDiff nis2) is_o with end
     end
    end.
  

Program Definition par_val (N1 N2: Node) (m: AMode N1 * AMode N2) 
  o: forall (is_o: SV.In o (par_out N1 N2 m))
               (V : forall i, SV.In i (par_dep N1 N2 m is_o) -> Data), Data :=
     let (m1,m2) return 
        forall (is_o: SV.In o (par_out N1 N2 m))
               (V : forall i, SV.In i (par_dep N1 N2 m is_o) -> Data), Data
        := m in
     fun (is_o: SV.In o (par_out N1 N2 (m1,m2)))
               (V : forall i, SV.In i (par_dep N1 N2 (m1,m2) is_o) -> Data) =>
     match SV.In_dec o (AOut N1 m1) with
      left is1 => @AValue N1 m1 o is1
        (fun i i_in => match SV.In_dec i (AOut N2 m2) with
          left o2 => @AValue N2 m2 i o2 (rest V _) 
        | right no2 => V i _
         end)
    | right nis1 =>
      match SV.In_dec o (AOut N2 m2) with
      | left is2 => @AValue N2 m2 o is2
          (fun i i_in => match SV.In_dec i (AOut N1 m1) with
            left o1 => @AValue N1 m1 i o1 (rest V _) 
          | right no1 => V i _
           end)
     | right nis2 => match SV.NotInLRNotInUnion (SV.NotInLDiff nis1) (SV.NotInLDiff nis2) is_o with end
     end
    end.
Next Obligation.
 repeat intro.
 unfold par_dep.
 apply SV.InUnion_l.
 apply SV.InGUNION with i o2; auto.
 apply SV.InGUnion with o is1; auto.
 Qed.
Next Obligation.
 repeat intro.
 apply SV.InUnion_r.
 apply SV.InDiff; auto.
 apply SV.NotIn_l; auto.
 Qed.
Next Obligation.
 repeat intro.
 apply SV.InUnion_l.
 apply SV.InGUNION with i o1; auto.
 apply SV.InGUnion with o is2; auto.
 Qed.
Next Obligation.
 repeat intro.
 apply SV.InUnion_r.
 apply SV.InDiff; auto.
 apply SV.NotIn_l; auto.
 Qed.

Program Definition par (N1 N2: Node) := 
{|
  ACtrl := SV.union (ACtrl N1) (ACtrl N2);
  AMode := AMode N1 * AMode N2;
  ASelect f := (ASelect N1 (rest (D2:=ACtrl N1) f (fun v => @SV.InUnion_l v _ _)), ASelect N2 (rest (D2:=ACtrl N2) f (fun v => @SV.InUnion_r v _ _)));
  AOut := par_out N1 N2;
  ADep := par_dep N1 N2;
  AValue := par_val N1 N2
|}.
Next Obligation.
  intro.
  unfold par_dep, par_out in *.
  destruct (SV.In_dec o (AOut N1 a)).
  apply SV.InUnion in H.
Admitted.

(**********************************************************)

(* x = y default z  *)
Program Definition default2Node (x y z Cy Cz: Var) := {|
  ACtrl := SV.union (SV.sing Cy) (SV.sing Cz);
  AMode := bool;
  ASelect (f: forall v, SV.In v (SV.union (SV.sing Cy) (SV.sing Cz)) -> bool) := f Cy _;
  AOut m := SV.sing x;
  ADep m o h := if m then SV.sing y else SV.sing z;
  AValue m o h V := if m then V y _ else V z _;
  AInOut := _
|}.

(* x = y when z  *)
Program Definition when2Node (x y z Cx: Var) := {|
  ACtrl := SV.sing Cx;
  AMode := bool;
  ASelect (f: forall v, SV.In v (SV.sing Cx) -> bool) := f Cx _;
  AOut m := SV.sing x;
  ADep m o h := if m then SV.sing y else SV.empty;
  AValue m o h V := if m then V x _ else _;
  AInOut := _
|}.

(**********************************************************)

(*
  - hypothese d'acyclicité du produit
  - manque la connaissance statique du fait qu'une fonction calcule une
    certaine variable 
*)


(* 
  Remark1: notification is implicit after action (corresponds to a notifyAll in Java)
  Remark2: the representation depends strongly on your problem: we find both Action and Next
  Remark3: only one action? 
  Remark4: wait/notify cannot test absence => eliminated before
    (absence ==> boolean condition ==> var is true)
*)

Structure Thread := {
  AIn: SV.set;
  AOut: SV.set;
  AInOut: SV.is_empty (SV.inter AIn AOut);
  ADep: forall o, SV.In o AOut -> SV.set;
  ADepIn: forall o (is_o: SV.In o AOut), SV.subset (ADep is_o) AIn;
  ACond: forall o (is_o: SV.In o AOut), Clk (ADep is_o);
  AValue: forall o (is_o: SV.In o AOut) (V : forall i, SV.In i (ADep is_o) -> Data), check V (ACond is_o) -> Data
}.

Class VMT := {
  threadId: Type; (* set of thread identifiers *)
  Init: State; (* initial state of a thread *)
  Next: State  -> State; (* state for the next synchronous step *)
  threads: threadId -> Thread (* associates a thread definition to a thread ident *)
}.

Record Thr_sat (th: Thread) (P: SV.set) (V: forall v, SV.In v P -> Data) := {
  th_oP: forall (ip: SV.subset (AIn th) P) o is_o, check (fun i h => V i (ip i h)) (ACond th is_o) ->
    SV.subset (AOut th) P;
  th_oV: forall (ip: SV.subset (AIn th) P) (gT: check (fun i h => V i (ip i h)) (AGuard th)) o (op: SV.In o (AOut th)),
    V o (th_oP ip gT o op) = AComp (Body th) (fun i is_i =>  V i (ip i is_i)) gT o op 
}.

Record VMT_sat (vmt: VMT) (P: set Var) (V: forall v, P v -> Data) := {
  vmt_sth: forall th, Thr_sat th P V;
  vmt_Pmin: forall v, P v -> ~Inp v -> 
    exists th, 
        AOut th v /\ 
        (forall i, AIn th i -> P i) /\
        forall (ip: forall i, AIn th i -> P i),
          check (fun i h => V i (ip i h)) (AGuard th)
}.

Definition abs_conc (P: set Var) (Va: forall v, P v -> Prop) (V: forall v, P v -> Data) :=
  forall v (h: P v), Va v h -> isTrue (V v h).

Record VMT_compat (vmt: VMT) I (h: Included _ I Inp) (ie: forall i, I i -> Data) (P: set Var) (V: forall v, P v -> Data) := {
  cmp_IP: Included _ I P;
  cmp_PI: Included _ (Intersection _ P Inp) I;
  cmp_IV: forall i (is_i: I i), ie i is_i = V i (cmp_IP is_i);
}.

Require Import Init.Wf.

(*
  resultat de l'analyse statique en amont:
    - la presence de toute var est determinee par la presence et la valeur des entrees
    - la valeur d'une garde est determinee par la presence et la valeur des entrees
    - presence des entrees et garde vraie => presence des sorties
*)

Record Thr_abs (th: Thread) (P: set Var) (V: forall v, P v -> Prop) := {
  th_aP: forall (ip: forall i, AIn th i -> P i), acheck (fun i h => V i (ip i h)) (AGuard th) ->
    forall o, AOut th o -> P o;
  th_aV: forall (ip: forall i, AIn th i -> P i) (gT: acheck (fun i h => V i (ip i h)) (AGuard th)) o (op: AOut th o),
    V o (th_aP ip gT o op) = AAbsComp (Body th) (fun i is_i =>  V i (ip i is_i)) gT o op 
}.

Record VMT_abs (vmt: VMT) (P: set Var) (V: forall v, P v -> Prop) := {
  vmt_ath: forall th, Thr_abs th P V;
  vmt_amin: forall v, P v -> ~Inp v -> 
    exists th, 
        AOut th v /\ 
        (forall i, AIn th i -> P i) /\
        forall (ip: forall i, AIn th i -> P i),
          acheck (fun i h => V i (ip i h)) (AGuard th)
}.

Axiom AbsComp: forall (vmt: VMT) (p: @threadId vmt) (V: forall i, AIn (threads p) i  -> bool) (a: Action) o (is_o: AOut (threads p) o), bool -> Prop.

Record VMT_State := {
  presence
  valeur
  waiting
  terminated
}.

Record VMT_CC (vmt: VMT) := {
  wf_dec: forall (P: set Var) (Va: forall i, P i -> Prop) (V: forall i, P i -> Data),
    abs_conc P Va V -> forall th i (ip: P i), 
    Wait (threads th) i -> 
      { p | Notify (threads p) i /\  
        (forall j, AIn (threads p) j -> P j) /\
        forall (p_in: forall j, AIn (threads p) j -> P j),
          check (fun i i_in => V i (p_in i i_in)) (AGuard (threads p))
      };
  wf_dep (P: set Var) V := fun th1 th2 => exists i, 
    exists (pi: P i),
      Wait (threads th2) i /\
      Notify (threads th1) i /\
      (forall i, AIn (threads th1) i -> P i) /\
      forall (p_in: forall j, AIn (threads th1) j -> P j),
        acheck (fun i i_in => V i (p_in i i_in))  (AGuard (threads th1));
  wf_acy: forall P V, VMT_abs vmt P V -> forall th, Acc (wf_dep P V) th
}.

(*
Record VMT_CC (vmt: VMT) I (h: Included _ I Inp) (ie: forall i, I i -> Data) := {
  wf_P: set Var;
  wf_IP: Included _ (Intersection _ Inp wf_P) I;
  wf_isT: forall th c ic, wf_P c -> AGuard th = isT (AIn th) c ic -> Prop;
  wf_Pok: forall th
    (ip: forall i, AIn th i -> wf_P i),
    (forall c ic (g: AGuard th = isT (AIn th) c ic),
        wf_isT th (ip c ic) g) -> 
          forall o, AOut th o -> wf_P o;
  wf_dec: forall th i (ip: wf_P i), 
    Wait (threads th) i -> 
      { p | Notify (threads p) i /\  
        (forall j, AIn (threads p) j -> wf_P j) /\
        (forall c ic (g: AGuard (threads p) = isT (AIn (threads p)) c ic) 
          (ip: wf_P c),
          wf_isT (threads p) ip g)
      };
  wf_dep := fun th1 th2 => exists i, 
    exists (pi: wf_P i),
    exists w:Wait (threads th2) i, th1 = proj1_sig (wf_dec _ pi w);
  wf_acy: forall th, Acc wf_dep th
}.
*)

Record VMT_WF (vmt:VMT) := {
  wf_cc:> VMT_CC vmt
}.

(*
 https://coq.inria.fr/library/Coq.Init.Wf.html
*)
Import EqNotations.
Require Import Coq.Program.Tactics.

Program Fixpoint getIValue In (h: Included _ In Inp) (ie: forall v, In v -> Data) vmt (wf: VMT_WF vmt) th (acy :  Acc (wf_dep (wf_cc wf h ie)) th) i  (is_i: AIn (Body (threads th)) i) : option Data :=
   match Inp_dec i with
     left is_inp =>  Some (ie i (wf_IP wcc (Intersection_intro _ _ _ _ is_inp is_p)))
   | right not_inp => 
      let is_waited := WaitIn (threads th) is_i not_inp in
      let pni :=  wf_dec wcc th i is_p is_waited in
      let p := proj1_sig pni in
      let '(conj n (conj inP gT)) := proj2_sig pni in
      let env := fun j j_in => getIValue wf (Acc_inv acy (ex_intro _ i (ex_intro _ is_p (ex_intro _ (WaitIn (threads th) is_i not_inp) eq_refl)))
) j j_in _ in
      AComp (Body (threads p)) 
        env
         (match AGuard (threads (proj1_sig pni)) as g return _=g -> check env g with
            isT _ c ic =>  fun e =>  (*gT c ic e (inP c ic)*)   (*isTrue (env c ic)*) _
          | _ => fun e => I
         end eq_refl)
        i (NotifyOut (threads p) i n)
   end.
Next Obligation.
  unfold check.
  match goal with
    |- match ?c with _ => _ end => case_eq c
  end.
Qed.


Program Fixpoint getIValue In (h: Included _ In Inp) (ie: forall v, In v -> Data) vmt (wf: VMT_WF vmt) th (acy :  Acc (wf_dep (wf_cc wf h ie)) th) i  (is_i: AIn (Body (threads th)) i) (is_p: wf_P (wf_cc wf h ie) i):  Data :=
  let wcc := wf_cc wf h ie in
   match Inp_dec i with
     left is_inp =>  ie i (wf_IP wcc (Intersection_intro _ _ _ _ is_inp is_p))
   | right not_inp => 
      let is_waited := WaitIn (threads th) is_i not_inp in
      let pni :=  wf_dec wcc th i is_p is_waited in
      let p := proj1_sig pni in
      let '(conj n (conj inP gT)) := proj2_sig pni in
      let env := fun j j_in => getIValue wf (Acc_inv acy (ex_intro _ i (ex_intro _ is_p (ex_intro _ (WaitIn (threads th) is_i not_inp) eq_refl)))
) j j_in _ in
      AComp (Body (threads p)) 
        env
         (match AGuard (threads (proj1_sig pni)) as g return _=g -> check env g with
            isT _ c ic =>  fun e =>  (*gT c ic e (inP c ic)*)   (*isTrue (env c ic)*) _
          | _ => fun e => I
         end eq_refl)
        i (NotifyOut (threads p) i n)
   end.
Next Obligation.
  unfold check.
  match goal with
    |- match ?c with _ => _ end => case_eq c
  end.
Qed.

Definition getOValue (env: forall v, Inp v -> Data) vmt (wf: VMT_WF vmt) th (acy :  Acc (wf_dep wf) th) o (is_o: AOut (Body (threads th)) o) : Data :=
  AComp (Body (threads th)) (getIValue env acy) o is_o.

Definition  isActive vmt (wf: VMT_WF vmt) (th: threadId vmt) : bool.
        
Structure TS := { (* transition system for the semantics *)
  LState: Type; 
  LInit: LState;
  LTrans: LState -> LState -> Prop
}.

Inductive cstate := (* control state of a thread *)
   csWait  (* waiting for notifications *)
| csRun  (* after all notifies have been received *)
| csEnd (* after step computation *).

Structure state(vmt:VMT) := mk_state {
  vmState: State vmt;
  ctState: threadId vmt -> cstate;
  notified: threadId vmt -> set (threadId vmt)
}.

(* transitions from st1 to st2 *)

(* the thread id waits for termination of its predecessors (they are all in the csEnd state) 
   so id makes a transition from csInit to csRun
   local states are unchanged
   control states of other threads are unchanged
*)
Record TrWait (vmt:VMT) (st1: state vmt) (st2: state vmt) id := {
  w_atInit: ctState _ st1 id = csWait;
  w_notified: Included _ (Wait _ _ (threads vmt id)) (notified vmt st1 id);
  w_state: vmState _ st2 = vmState _ st1;
  w_id_ctrl: ctState _ st2 id = csRun;
  w_others: forall id', id' <> id -> ctState _ st2 id' = ctState _ st1 id'
}.

(* the thread id makes a transition from csRun to csEnd if its guard is true.
    its local state is updated according to the action.
   states of other threads are unchanged
*)
Record TrComp(vmt:VMT) (st1: state vmt) (st2: state vmt) id := {
  c_atRun: ctState _ st1 id = csRun;
  c_guard: Guard _ _ (threads vmt id) (vmState _ st1);
  c_action:  vmState _ st2 = Comp _ _ (threads vmt id) (vmState _ st1) c_guard;
  c_id_ctrl: ctState _ st2 id = csEnd;
  c_others: forall id', id' <> id -> ctState _ st2 id' = ctState _ st1 id';
  c_notify: forall id', In _ (Notify _ _ (threads vmt id)) id' -> notified _ st2 id' = Add _ (notified _ st1 id') id;
  c_not_notified:  forall id', not (In _ (Notify _ _ (threads vmt id)) id') -> notified _ st2 id' = notified _ st1 id';
}.

(*
  the thread is ready but the guard is false: the control state becomes csEnd
*)
Record TrNoComp(vmt:VMT) (st1: state vmt) (st2: state vmt) id := {
  nc_atRun: ctState _ st1 id = csRun;
  nc_guard: not (Guard _ _ (threads vmt id) (vmState _ st1));
  nc_action:  vmState _ st2 = vmState _ st1;
  nc_id_ctrl: ctState _ st2 id = csEnd;
  nc_others: forall id', id' <> id -> ctState _ st2 id' = ctState _ st1 id';
  nc_notify: forall id', In _ (Notify _ _ (threads vmt id)) id' -> notified _ st2 id' = Add _ (notified _ st1 id') id;
  nc_not_notified:  forall id', not (In _ (Notify _ _ (threads vmt id)) id') -> notified _ st2 id' = notified _ st1 id';
}.

(*
  if all the states are in csEnd, all the threads make the Next transition in a synchronous way
Remark1: Next transitions could be made asynchronously
Remark2: if a thread does not run, the whole system is blocked
  the next step is considered only if all the threads have made a step
*)
Record TrNext(vmt:VMT) (st1: state vmt) (st2: state vmt) := {
  n_all_at_end: forall id, ctState _ st1 id = csEnd;
  n_restart: forall id, ctState _ st2 id = csWait;
  n_notified: forall id, notified _ st2 id = Empty_set _;
  n_next: vmState _ st2 = Next _ (vmState _ st1)
}.

(*
  the whole system makes one of the four kinds of transitions
*)
Inductive trans (vmt:VMT) (st1: state vmt) (st2: state vmt): Prop :=
  trWait: forall id, TrWait vmt st1 st2 id -> trans vmt st1 st2
 | trComp: forall id, TrComp vmt st1 st2 id -> trans vmt st1 st2
 | trNoComp: forall id, TrNoComp vmt st1 st2 id -> trans vmt st1 st2
 | trNext: TrNext vmt st1 st2 -> trans vmt st1 st2.

(* we get the semantics of VMT as a TS *)
Definition VMT2TS (vmt: VMT) := {|
  LState := state vmt;
  LInit := mk_state _ (Init vmt) (fun _ => csWait) (fun _ => Empty_set _);
  LTrans := trans vmt
|}.

(*
  Remark: Input/Output are not considered here. The structure of a Thread should be made more precise for that
  If we add input/output, TS should be replaced by STS (synchronous transition system) which is an LTS where labels model input/output
*)
