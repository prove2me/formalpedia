-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.normState_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:42:43.504242+00:00
-- url     : https://prove2.me/submissions/83dc02e3-46a5-4ac6-8732-f46811d2e603

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Square_increment_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_terminalLoop_runs
import Theorems.Thm_KoanaKPaths_Machine_copyMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveInts_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_powerMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_repeatInts_exec
import Theorems.Thm_KoanaKPaths_Machine_transferArray_exec
import Theorems.Thm_KoanaKPaths_Main_denseLayer_correct
import Theorems.Thm_KoanaKPaths_Main_graphLayer_natAbs
import Theorems.Thm_KoanaKPaths_Main_graphNorm_width
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

namespace KoanaKPaths.Machine.Native
open NLogN
variable {S P : ℕ} {I : List Sym} {iprog : Fin P→IStmt S P} {p q : IStmt S P} {s s1 s2 : IState S} {c d : ℕ}

lemma mono (h : IRuns I iprog p s s1 c) (hc : c ≤ d) : IRuns I iprog p s s1 d := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht.trans hc,h⟩
lemma of_exec (h : IExec I iprog p s s1 c) : IRuns I iprog p s s1 c := ⟨c,le_rfl,h⟩


lemma seq (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog q s1 s2 d) :
    IRuns I iprog (.seq p q) s s2 (c+d) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d',Nat.add_le_add hc hd,.seq h1 h2⟩





end KoanaKPaths.Machine.Native

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S P : ℕ}



































lemma nbits_eq_bits (n : ℕ) : nbits n = Nat.bits n := by
  induction n using Nat.binaryRec' with
  | zero => simp [nbits]
  | bit b n hn ih =>
    have hne : Nat.bit b n ≠ 0 := by
      intro hz
      cases b <;> simp_all [Nat.bit]
    rw [nbits,dif_neg hne,Nat.bit_mod_two,Nat.bit_div_two,ih,Nat.bits_append_bit n b hn]
    cases b <;> rfl

















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S : ℕ}



@[simp] lemma upd_G_self (s : IState S) (i : Fin S) (L : List Item) : (s.upd i L).G i = L := by
  simp [IState.upd]
@[simp] lemma upd_G_ne (s : IState S) {i j : Fin S} (h : j ≠ i) (L : List Item) :
    (s.upd i L).G j = s.G j := by simp [IState.upd,h]
@[simp] lemma upd_same (s : IState S) (i : Fin S) : s.upd i (s.G i) = s := by
  cases s
  simp [IState.upd]

@[simp] lemma upd_upd (s : IState S) (i : Fin S) (L M : List Item) :
    (s.upd i L).upd i M = s.upd i M := by
  cases s
  simp [IState.upd,Function.update_idem]


















lemma copyMarks_exec (I : List Sym) (src dst tmp : Fin S)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : IState S) (m : ℕ) (tail : List Item) (ht : cls tail.head? ≠ Cls.mark)
    (hs : s.G src = List.replicate m .mark ++ tail) (hx : s.G tmp = []) :
    IExec I Fin.elim0 (copyMarks src dst tmp) s
      (s.upd dst (List.replicate m .mark ++ s.G dst)) (65*m+60) := by
  let s1 := (((s.upd src tail).upd dst (List.replicate m .mark ++ s.G dst)).upd tmp
    (List.replicate m .mark ++ s.G tmp))
  have hd := copyMoveMarks_exec I src dst tmp hsd hst hdt s m tail ht hs
  have hm := moveMarks_exec I tmp src (Ne.symm hst) s1 m [] (by decide) (by simp [s1,hx])
  have he : (s1.upd tmp []).upd src (List.replicate m .mark ++ s1.G src) =
      s.upd dst (List.replicate m .mark ++ s.G dst) := by
    cases s
    simp only [s1,IState.upd]
    congr 1
    funext t
    by_cases ha : t=src <;> by_cases hb : t=dst <;> by_cases hc : t=tmp <;> simp_all
  have hrun := IExec.seq hd hm
  rw [he] at hrun
  change IExec I Fin.elim0 (copyMarks src dst tmp) s _ ((33*m+30)+(32*m+30)) at hrun
  convert hrun using 1 <;> omega

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}





lemma cls_int (z : ℤ) :
    cls (some (.int z)) = Cls.zero ∨ cls (some (.int z)) = Cls.pos ∨
      cls (some (.int z)) = Cls.neg := by
  by_cases hz : z=0
  · simp [cls,hz]
  · by_cases hn : z<0 <;> simp [cls,hz,hn]



lemma moveIntsCost_le (xs : List ℤ) (w : ℕ) (hw : ∀ z ∈ xs, zsz z ≤ w) :
    moveIntsCost xs ≤ (76*w+131)*xs.length+30 := by
  unfold moveIntsCost
  have h : (xs.map (fun z => 2*moveCost (zsz z)+49)).sum ≤ (76*w+131)*xs.length := by
    induction xs with
    | nil => simp
    | cons z xs ih =>
      have hz := hw z (by simp)
      have hr := ih (fun x hx => hw x (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      unfold moveCost at *
      nlinarith
  omega
































end KoanaKPaths.Machine

end

section

namespace KoanaKPaths.Machine
open NLogN
variable {S P : ℕ}



lemma liftClosed_exec (I : List Sym) (prog : Fin P → IStmt S P)
    {p : IStmt S 0} {s s' : IState S} {c : ℕ}
    (h : IExec I Fin.elim0 p s s' c) : IExec I prog (liftClosed p) s s' c := by
  induction h with
  | skip s => exact .skip s
  | op h => exact .op h
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | iteT h _ ih => exact .iteT h ih
  | iteF h _ ih => exact .iteF h ih
  | loopT h _ _ ih1 ih2 => exact .loopT h ih1 ih2
  | loopF h => exact .loopF h
  | call => exact Fin.elim0 ‹Fin 0›

lemma liftClosed_runs (I : List Sym) (prog : Fin P → IStmt S P)
    {p : IStmt S 0} {s s' : IState S} {c : ℕ}
    (h : IRuns I Fin.elim0 p s s' c) : IRuns I prog (liftClosed p) s s' c := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht,liftClosed_exec I prog h⟩

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}







lemma growMarksCost_identity (m d : ℕ) :
    growMarksCost m d+97*m=97*m*2^d+91*d+30 := by
  induction d generalizing m with
  | zero => simp [growMarksCost]; omega
  | succ d ih =>
    simp only [growMarksCost]
    have hh := ih (2*m)
    rw [pow_succ]
    nlinarith

lemma growMarksCost_le (m d : ℕ) : growMarksCost m d ≤ (97*m+121)*2^d := by
  have h := growMarksCost_identity m d
  have hd : d ≤ 2^d := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hp : 1 ≤ 2^d := Nat.one_le_pow d 2 (by omega)
  nlinarith






lemma powerMarks_cost (d : ℕ) : 1+(65*d+60)+growMarksCost 1 d ≤ 400*2^d := by
  have hg := growMarksCost_le 1 d
  have hd : d ≤ 2^d := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hp : 1 ≤ 2^d := Nat.one_le_pow d 2 (by omega)
  nlinarith

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 400000
open scoped BigOperators
namespace KoanaKPaths.ExteriorCoordinates


























lemma subsetOrder_length (k : ℕ) : (subsetOrder k).length = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [subsetOrder,ih,pow_succ]; omega







lemma coefficientList_length {k : ℕ} (A : Coordinates k) : (coefficientList A).length = 2^k := by
  simp [coefficientList,subsetOrder_length]



lemma zipWith_same_map {α β γ δ : Type} (L : List α) (f : α → β) (g : α → γ) (h : β → γ → δ) :
    List.zipWith h (L.map f) (L.map g) = L.map (fun x => h (f x) (g x)) := by
  induction L <;> simp_all













lemma subsetOrder_last (k : ℕ) : (subsetOrder k).getLast? = some Finset.univ := by
  induction k with
  | zero => simp [subsetOrder]
  | succ k ih =>
    have hu : upperSet (Finset.univ : Finset (Fin k)) = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro r
      refine Fin.lastCases ?_ (fun x => ?_) r
      · simp [upperSet]
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_map.mpr ⟨x,Finset.mem_univ x,rfl⟩
    have hn : (subsetOrder k).map upperSet ≠ [] := by
      have hl := subsetOrder_length k
      intro he
      have := congrArg List.length he
      simp only [List.length_map,List.length_nil] at this
      have hp : 0 < 2^k := by positivity
      omega
    rw [subsetOrder,List.getLast?_append_of_ne_nil _ hn,List.getLast?_map,ih]
    simp [hu]

lemma coefficientList_last {k : ℕ} (A : Coordinates k) :
    (coefficientList A).getLast? = some (A Finset.univ) := by
  simp [coefficientList,List.getLast?_map,subsetOrder_last]

lemma coefficientList_add {k : ℕ} (A B : Coordinates k) :
    coefficientList (A+B) = List.zipWith (·+·) (coefficientList A) (coefficientList B) := by
  simp only [coefficientList,zipWith_same_map]
  rfl



lemma coefficientList_zero (k : ℕ) : coefficientList (0 : Coordinates k) = List.replicate (2^k) 0 := by
  change (subsetOrder k).map (fun _ => (0 : ℤ)) = _
  simp [List.map_const,subsetOrder_length]







end KoanaKPaths.ExteriorCoordinates

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]

lemma zsz_le_iff (z : ℤ) (w : ℕ) : zsz z ≤ w ↔ z.natAbs<2^w := by
  rw [zsz_eq_size,Nat.size_le]













lemma moveIntsCost_bound (xs : List ℤ) (w : ℕ) (h : ∀ z∈xs, zsz z≤w) :
    moveIntsCost xs ≤ 200*(w+1)*(xs.length+1) := by
  have hh := moveIntsCost_le xs w h
  nlinarith



lemma addIntCost_formula (L : ℕ) : addIntCost L=297*L+393 := by
  simp only [addIntCost,addMagCost,subMagCost,zipCost,moveCost]
  ring

















end KoanaKPaths.Machine.Wedge

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}








lemma itemState_ext {s t : IState S} (hG : ∀ i, s.G i=t.G i) (hip : s.ip=t.ip)
    (hout : s.out=t.out) : s=t := by
  cases s with
  | mk G ip o =>
    cases t with
    | mk H jp p =>
      have hh : G=H := funext hG
      cases hh
      cases hip
      cases hout
      rfl

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Square









attribute [local simp] Value Arg X Y W Q R T

lemma zsz_mul_le (x y : ℤ) (u v : ℕ) (hx : zsz x≤u) (hy : zsz y≤v) : zsz (x*y)≤u+v := by
  apply (Wedge.zsz_le_iff _ _).mpr
  rw [Int.natAbs_mul]
  have hx' := (Wedge.zsz_le_iff x u).mp hx
  have hy' := (Wedge.zsz_le_iff y v).mp hy
  calc
    _ ≤ x.natAbs*2^v := Nat.mul_le_mul_left _ (Nat.le_of_lt hy')
    _ < 2^u*2^v := Nat.mul_lt_mul_of_pos_right hx' (by positivity)
    _ = _ := (pow_add _ _ _).symm



lemma program_runs (I : List Sym) (s : IState NS) (x : ℤ) (tail : List Item) (w : ℕ)
    (hs : s.G Value=.int x::tail) (hw : zsz x≤w) :
    IRuns I Fin.elim0 program s (s.upd Value (.int (x*x)::tail)) (10000*(w+1)^2) := by
  let s1 := s.upd Arg (.int x::s.G Arg)
  let s2 := (s1.upd Value tail).upd Arg (.int x::s1.G Arg)
  let s3 := s2.upd Arg (.int (x*x)::s.G Arg)
  let s4 := (s3.upd Arg (s.G Arg)).upd Value (.int (x*x)::tail)
  have h1 : IExec I Fin.elim0 (.op (.dup Value Arg)) s s1 (dupCost (zsz x)+17) := .op (.dup (by decide) hs)
  have h2 : IExec I Fin.elim0 (.op (.mv Value Arg)) s1 s2 (2*moveCost (zsz x)+19) := by
    exact .op (.mv (by decide) (by simp [s1,hs]))
  have h3 : IRuns I Fin.elim0 (smul Arg X Y W Q R T) s2 s3 (smulCost (zsz x+zsz x)) := by
    have hh := NLogN.smul_runs (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (A := Arg) (X := X) (Y := Y) (W := W) (Q := Q) (R := R) (T := T) (by decide)
      s2 x x (s.G Arg) (by simp [s2,s1])
    exact hh
  have h4 : IExec I Fin.elim0 (.op (.mv Arg Value)) s3 s4 (2*moveCost (zsz (x*x))+19) := by
    simpa only [s4,s3,s2,s1,upd_G_ne _ (show Value≠Arg by decide),upd_G_self] using
      (IExec.op (IOp.Step.mv (I := I) (s := s3) (i := Arg) (j := Value) (by decide)
        (by simp [s3])) : IExec I Fin.elim0 _ _ _ _)
  have he : s4=s.upd Value (.int (x*x)::tail) := by
    cases s
    simp only [s4,s3,s2,s1,IState.upd]
    congr 1
    funext i
    by_cases hV : i=Value <;> by_cases hA : i=Arg <;> simp_all
  have hrun := Native.seq (Native.of_exec h1) (Native.seq (Native.of_exec h2)
    (Native.seq h3 (Native.of_exec h4)))
  change IRuns I Fin.elim0 program s _ _ at hrun
  rw [he] at hrun
  apply Native.mono hrun
  have hxx := zsz_mul_le x x w w hw hw
  have hsm : smulCost (zsz x+zsz x)≤8000*(w+1)^2 := by
    unfold smulCost
    nlinarith
  simp only [dupCost,zipCost,moveCost]
  nlinarith

end KoanaKPaths.Machine.Square

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}









lemma clearInts_exec (I : List Sym) (src : Fin S) (s : IState S) (xs : List ℤ) (tail : List Item)
    (ht : ¬ (cls tail.head?=Cls.zero ∨ cls tail.head?=Cls.pos ∨ cls tail.head?=Cls.neg))
    (hs : s.G src=xs.map Item.int ++ tail) :
    IExec I Fin.elim0 (clearInts src) s (s.upd src tail) (clearIntsCost xs) := by
  induction xs generalizing s with
  | nil =>
    have he : s.upd src tail=s := by rw [← show s.G src=tail from by simpa using hs]; exact upd_same _ _
    rw [he]
    exact IExec.loopF (by simpa [IState.cl,hs] using ht)
  | cons x xs ih =>
    let s1 := s.upd src (xs.map Item.int ++ tail)
    have h1 : IExec I Fin.elim0 (.op (.drop src)) s s1 (2*zsz x+2) := .op (.drop (by simpa using hs))
    have hh : decide (s.cl src=Cls.zero ∨ s.cl src=Cls.pos ∨ s.cl src=Cls.neg)=true := by
      simp only [IState.cl,hs,List.map_cons,List.cons_append,List.head?_cons,decide_eq_true_eq]
      exact cls_int x
    have hrun := IExec.loopT hh h1 (ih s1 (by simp [s1]))
    change IExec I Fin.elim0 (clearInts src) s _ _ at hrun
    simp only [s1,upd_upd] at hrun
    convert hrun using 1
    simp only [clearIntsCost,List.map_cons,List.sum_cons]
    omega









end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates

lemma arrayFold_coeff {k : ℕ} (as : List (Coordinates k)) (a : Coordinates k) :
    (as.map coefficientList).foldl (List.zipWith (·+·)) (coefficientList a) =
      coefficientList (a+as.sum) := by
  induction as generalizing a with
  | nil => simp
  | cons b as ih =>
    simp only [List.map_cons,List.foldl_cons,List.sum_cons]
    rw [← coefficientList_add,ih]
    congr 1
    exact add_assoc _ _ _

lemma arraySum_coeff {k : ℕ} (as : List (Coordinates k)) :
    arraySum k (as.map coefficientList)=coefficientList as.sum := by
  unfold arraySum
  rw [← coefficientList_zero,arrayFold_coeff,zero_add]



lemma sum_finRange {A : Type} [AddCommMonoid A] (n : ℕ) (f : Fin n→A) :
    ((List.finRange n).map f).sum=∑ i, f i := by
  rw [← List.sum_toFinset _ (List.nodup_finRange n),List.toFinset_finRange]








lemma denseOutput_correct {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (a : Fin ℓ) :
    denseOutput arcs σ R a=coefficientList (graphOutput arcs σ R a) := by
  unfold denseOutput
  simp only [denseLayer_correct]
  have hm : (List.finRange n).map (fun v => coefficientList (graphLayer arcs σ R k v a)) =
      ((List.finRange n).map (fun v => graphLayer arcs σ R k v a)).map coefficientList := by
    simp only [List.map_map,Function.comp_def]
  rw [hm,arraySum_coeff,sum_finRange]
  rfl





end KoanaKPaths.Main

end

section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates

lemma natAbs_sum_le {α : Type} (s : Finset α) (f : α→ℤ) :
    (∑ x∈s, f x).natAbs ≤ ∑ x∈s, (f x).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)












lemma layerRadius_le_exp (n k ℓ : ℕ) : layerRadius n k ℓ≤2^(n+k+ℓ+3) := by
  have hp : layerRadius n k ℓ≤(n+1)*(k+1)*(ℓ+1) := by
    unfold layerRadius
    nlinarith [Nat.zero_le (n*k),Nat.zero_le (n*ℓ),Nat.zero_le (k*ℓ)]
  have hn : n+1≤2^(n+1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hk : k+1≤2^(k+1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hl : ℓ+1≤2^(ℓ+1) := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    _ ≤ (n+1)*(k+1)*(ℓ+1) := hp
    _ ≤ 2^(n+1)*2^(k+1)*2^(ℓ+1) := Nat.mul_le_mul (Nat.mul_le_mul hn hk) hl
    _ = _ := by rw [← pow_add,← pow_add]; congr 1; omega





end KoanaKPaths.Main

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Norm




attribute [local simp] Src Value Tmp Wedge.R Square.Value



lemma takeTop_exec (I : List Sym) (s : IState NS) (xs : List ℤ) (x : ℤ) (tail : List Item)
    (hs : s.G Src=(xs++[x]).map Item.int ++ .mark::tail) :
    IExec I Fin.elim0 takeTop s
      ((s.upd Src tail).upd Value (.int x::s.G Value))
      (moveIntsCost (xs++[x])+(2*moveCost (zsz x)+19)+clearIntsCost xs.reverse+3) := by
  let s1 := s.upd Tmp (.mark::s.G Tmp)
  let s2 := (s1.upd Src (.mark::tail)).upd Tmp ((xs++[x]).reverse.map Item.int ++ s1.G Tmp)
  let s3 := s2.upd Src tail
  let s4 := (s3.upd Tmp (xs.reverse.map Item.int ++ .mark::s.G Tmp)).upd Value (.int x::s3.G Value)
  let s5 := s4.upd Tmp (.mark::s.G Tmp)
  let s6 := s5.upd Tmp (s.G Tmp)
  have h1 : IExec I Fin.elim0 (.op (.mark Tmp)) s s1 1 := .op (.mark)
  have h2 : IExec I Fin.elim0 (moveInts Src Tmp) s1 s2 (moveIntsCost (xs++[x])) :=
    moveInts_exec I Src Tmp (by decide) s1 (xs++[x]) (.mark::tail) (by simp [cls]) (by simp [s1,hs])
  have h3 : IExec I Fin.elim0 (.op (.unmark Src)) s2 s3 1 := by
    exact .op (.unmark (by simp [s2]))
  have h4 : IExec I Fin.elim0 (.op (.mv Tmp Value)) s3 s4 (2*moveCost (zsz x)+19) := by
    have hm := IExec.op (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.mv (I := I) (s := s3) (i := Tmp) (j := Value) (by decide)
      (show s3.G Tmp=.int x::(xs.reverse.map Item.int ++ .mark::s.G Tmp) by
        simp [s3,s2,s1,List.reverse_append,List.map_append]))
    simpa only [s4,s3,s2,s1,upd_G_ne _ (show Value≠Src by decide),upd_G_ne _ (show Value≠Tmp by decide)] using
      (hm : IExec I Fin.elim0 _ _ _ _)
  have h5 : IExec I Fin.elim0 (clearInts Tmp) s4 s5 (clearIntsCost xs.reverse) :=
    clearInts_exec I Tmp s4 xs.reverse (.mark::s.G Tmp) (by simp [cls]) (by simp [s4])
  have h6 : IExec I Fin.elim0 (.op (.unmark Tmp)) s5 s6 1 := by exact .op (.unmark (by simp [s5]))
  have he : s6=(s.upd Src tail).upd Value (.int x::s.G Value) := by
    cases s
    simp only [s6,s5,s4,s3,s2,s1,IState.upd]
    congr 1
    funext i
    by_cases hS : i=Src <;> by_cases hV : i=Value <;> by_cases hT : i=Tmp <;> simp_all
  have hrun := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 (IExec.seq h5 h6))))
  change IExec I Fin.elim0 takeTop s _ _ at hrun
  rw [he] at hrun
  convert hrun using 1 <;> omega

end KoanaKPaths.Machine.Norm

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main





lemma graphNorm_nonneg {n k ℓ : ℕ} (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    0≤ ∑ a : Fin ℓ, (graphOutput arcs σ R a Finset.univ)^2 :=
  Finset.sum_nonneg (fun a _ => sq_nonneg _)



lemma denseTrial_cast {n k ℓ : ℕ} (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    (denseTrial arcs σ R : ℤ)=∑ a : Fin ℓ, (graphOutput arcs σ R a Finset.univ)^2 := by
  unfold denseTrial
  simp only [denseOutput_correct,ExteriorCoordinates.coefficientList_last,Option.getD_some]
  rw [sum_finRange]
  exact Int.toNat_of_nonneg (graphNorm_nonneg arcs σ R)

lemma denseTrial_width {n k ℓ : ℕ} (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    zsz (denseTrial arcs σ R : ℤ)≤ trialWidth n k ℓ := by
  rw [denseTrial_cast]
  exact graphNorm_width arcs σ R

lemma trialWidth_polynomial (n k : ℕ) : trialWidth n k k≤20*(1+n+k)^2 := by
  unfold trialWidth outputExponent
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (n*k)]

end KoanaKPaths.Main

namespace KoanaKPaths.Machine.Norm
lemma clearIntsCost_bound (xs : List ℤ) (w : ℕ) (h : ∀ x∈xs, zsz x≤ w) :
    clearIntsCost xs≤(2*w+32)*xs.length+30 := by
  unfold clearIntsCost
  have hh : (xs.map (fun x => 2*zsz x+32)).sum≤(2*w+32)*xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  omega

lemma takeTop_cost_bound (xs : List ℤ) (x : ℤ) (w : ℕ)
    (h : ∀ z∈xs++[x], zsz z≤ w) :
    moveIntsCost (xs++[x])+(2*moveCost (zsz x)+19)+clearIntsCost xs.reverse+3≤
      1000*(w+1)*(xs.length+2) := by
  have hm := Wedge.moveIntsCost_bound (xs++[x]) w h
  have hc := clearIntsCost_bound xs.reverse w (by simpa using fun z hz => h z (by simp [hz]))
  have hx := h x (by simp)
  simp only [List.length_append,List.length_singleton,List.length_reverse] at hm hc
  unfold moveCost
  nlinarith

end KoanaKPaths.Machine.Norm

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls







lemma zsz_nat_le (n : ℕ) : zsz (n : ℤ)≤ n := by
  rw [Wedge.zsz_eq_size,Int.natAbs_natCast]
  exact Nat.size_le.mpr Nat.lt_two_pow_self








end KoanaKPaths.Machine.Controls

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main



lemma wordWidth_pos (n k : ℕ) : 1≤ wordWidth n k := by
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]





lemma row_word_width (n k r : ℕ) (hr : r≤ k) : zsz (r : ℤ)≤ wordWidth n k := by
  have hz := Controls.zsz_nat_le r
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]





end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main






lemma Core.upd {n k : ℕ} {s : IState NS} {ω : Fin (trialBits n k)→Bool}
    {arcs : List (Fin n × Fin n)} {p : ℕ} (h : Core s ω arcs p) (j : Fin NS)
    (hj : j∉coreRegisters) (xs : List Item) : Core (s.upd j xs) ω arcs p := by
  intro r hr
  have hne : r≠j := by rintro rfl; exact hj hr
  simpa [IState.upd,hne] using h r hr

lemma Core.at {n k : ℕ} {s : IState NS} {ω : Fin (trialBits n k)→Bool}
    {arcs : List (Fin n × Fin n)} {p : ℕ} (h : Core s ω arcs p) (j : Fin NS)
    (hj : j∈coreRegisters) : s.G j=coreStack ω arcs p j := h j hj

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
open scoped BigOperators
namespace KoanaKPaths.Main
universe u
variable {M : Type u} [AddCommMonoid M] {m : ℕ}



lemma finPrefix_zero (f : Fin m→M) : finPrefix f 0=0 := by simp [finPrefix]

lemma finPrefix_full (f : Fin m→M) : finPrefix f m=∑ j, f j := by
  have h : Finset.univ.filter (fun j : Fin m => j.val< m)=Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro j _
    exact j.isLt
  rw [finPrefix,h]

lemma finPrefix_succ (f : Fin m→M) (i : ℕ) (hi : i< m) :
    finPrefix f (i+1)=finPrefix f i+f ⟨i,hi⟩ := by
  classical
  have hset : Finset.univ.filter (fun j : Fin m => j.val< i+1)=
      insert ⟨i,hi⟩ (Finset.univ.filter (fun j : Fin m => j.val< i)) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    constructor
    · intro h
      by_cases hj : j.val=i
      · exact Or.inl (Fin.ext hj)
      · exact Or.inr (by omega)
    · rintro (rfl|h)
      · change i< i+1
        omega
      · omega
  have hnot : (⟨i,hi⟩ : Fin m)∉Finset.univ.filter (fun j : Fin m => j.val< i) := by simp
  simp only [finPrefix,hset,Finset.sum_insert hnot]
  exact add_comm _ _

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
attribute [local simp] D HC DC Aux



lemma zeroArray_exec (I : List Sym) (dst : Fin NS)
    (hD : dst≠D) (hC : dst≠HC) (hN : dst≠DC) (hA : dst≠Aux)
    (s : IState NS) (d : ℕ) (td : List Item) (ht : cls td.head?≠Cls.mark)
    (hd : s.G D=List.replicate d .mark ++ td) (hc : s.G HC=[]) (hn : s.G DC=[]) (ha : s.G Aux=[]) :
    IExec I Fin.elim0 (zeroArray dst) s
      (s.upd dst (List.replicate (2^d) (.int 0) ++ .mark::s.G dst))
      ((1+(65*d+60)+growMarksCost 1 d)+33*2^d+31) := by
  let s0 := s.upd dst (.mark::s.G dst)
  let s1 := s0.upd HC (List.replicate (2^d) .mark)
  let s2 := (s1.upd HC []).upd dst (List.replicate (2^d) (.int 0) ++ .mark::s.G dst)
  have h0 : IExec I Fin.elim0 (.op (.mark dst)) s s0 1 := .op (.mark)
  have h1 : IExec I Fin.elim0 (powerMarks D HC DC Aux) s0 s1 (1+(65*d+60)+growMarksCost 1 d) :=
    powerMarks_exec I D HC DC Aux (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s0 d td ht (by simp [s0,Ne.symm hD,hd]) (by simp [s0,Ne.symm hC,hc])
      (by simp [s0,Ne.symm hN,hn]) (by simp [s0,Ne.symm hA,ha])
  have h2 : IExec I Fin.elim0 (repeatInts HC dst 0) s1 s2 (33*2^d+30) := by
    have h := repeatInts_exec I HC dst (Ne.symm hC) 0 s1 (2^d) [] (by simp [cls]) (by simp [s1])
    simpa [s2,s1,s0,hC,Wedge.zsz_eq_size] using h
  have he : s2=s.upd dst (List.replicate (2^d) (.int 0) ++ .mark::s.G dst) := by
    apply itemState_ext
    · intro i
      by_cases hi : i=dst
      · subst i; simp [s2,s1,s0]
      by_cases hH : i=HC
      · subst i; simp [s2,s1,s0,hc,Ne.symm hC]
      simp [s2,s1,s0,IState.upd,Function.update_apply,hi,hH]
    · rfl
    · rfl
  have h := IExec.seq h0 (IExec.seq h1 h2)
  rw [he] at h
  change IExec I Fin.elim0 (zeroArray dst) s _ _ at h
  convert h using 1 <;> omega

lemma zeroArray_cost (d : ℕ) :
    (1+(65*d+60)+growMarksCost 1 d)+33*2^d+31≤500*2^d := by
  have h := powerMarks_cost d
  have hp : 1≤2^d := Nat.one_le_pow d 2 (by omega)
  omega

end KoanaKPaths.Machine.Wedge

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates



lemma terminalPrefix_width {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (a : Fin k) (u : ℕ) :
    ∀ x∈coefficientList (terminalPrefix arcs σ R a u), zsz x≤ Machine.Trial.wordWidth n k := by
  intro x hx
  obtain ⟨S,_,rfl⟩ := List.mem_map.mp hx
  let Q := Finset.univ.filter (fun v : Fin n => v.val< u)
  have h : (terminalPrefix arcs σ R a u S).natAbs≤ n*(layerRadius n k k)^k := by
    calc
      _ ≤ ∑ v∈Q, (graphLayer arcs σ R k v a S).natAbs := by
        simp only [terminalPrefix,finPrefix,Finset.sum_apply]
        exact natAbs_sum_le Q _
      _ ≤ ∑ _v∈Q, (layerRadius n k k)^k := Finset.sum_le_sum (fun v _ => graphLayer_natAbs arcs σ R k v a S)
      _ = Q.card*(layerRadius n k k)^k := by simp
      _ ≤ n*(layerRadius n k k)^k := Nat.mul_le_mul_right _ (by simpa using Q.card_le_univ)
  have hr := Nat.pow_le_pow_left (layerRadius_le_exp n k k) k
  rw [←pow_mul] at hr
  have hn : n≤2^n := Nat.le_of_lt Nat.lt_two_pow_self
  have hh := h.trans (Nat.mul_le_mul hn hr)
  rw [←pow_add] at hh
  have hw : zsz (terminalPrefix arcs σ R a u S)≤ n+(n+k+k+3)*k+1 := by
    apply (Machine.Wedge.zsz_le_iff _ _).mpr
    rw [pow_succ]
    have hp : 0<2^(n+(n+k+k+3)*k) := by positivity
    omega
  unfold Machine.Trial.wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (n*k),Nat.zero_le (k*k)]

lemma terminalPrefix_full {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (a : Fin k) : terminalPrefix arcs σ R a n=graphOutput arcs σ R a :=
  finPrefix_full _



lemma normPrefix_bounds {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (i : ℕ) :
    0≤ normPrefix arcs σ R i ∧ zsz (normPrefix arcs σ R i)≤ Machine.Trial.wordWidth n k := by
  have h0 : 0≤ normPrefix arcs σ R i := by
    unfold normPrefix finPrefix
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hle : normPrefix arcs σ R i≤(denseTrial arcs σ R : ℤ) := by
    unfold normPrefix finPrefix
    rw [denseTrial_cast]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have hw := denseTrial_width arcs σ R
  have hw' := trialWidth_polynomial n k
  have hsz : zsz (normPrefix arcs σ R i)≤ zsz (denseTrial arcs σ R : ℤ) := by
    apply (Machine.Wedge.zsz_le_iff _ _).mpr
    have hAbs : (normPrefix arcs σ R i).natAbs≤(denseTrial arcs σ R : ℤ).natAbs := by
      apply Int.ofNat_le.mp
      rw [Int.natAbs_of_nonneg h0,Int.natAbs_of_nonneg (Int.natCast_nonneg _)]
      exact hle
    exact hAbs.trans_lt ((Machine.Wedge.zsz_le_iff _ _).mp le_rfl)
  refine ⟨h0,hsz.trans (hw.trans (hw'.trans ?_))⟩
  unfold Machine.Trial.wordWidth
  omega

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Norm


attribute [local simp] Wedge.R Sum TransferTmp Src Value Square.Value Accumulate.Acc



lemma addArray_runs (I : List Sym) (s : IState NS) (xs : List ℤ) (x q : ℤ)
    (accTail sumTail : List Item) (w : ℕ)
    (hAcc : s.G Accumulate.Acc=(xs++[x]).map Item.int ++ .mark::accTail)
    (hSum : s.G Sum=.int q::sumTail)
    (hw : ∀ z∈xs++[x], zsz z≤ w) (hq : zsz q≤ w) :
    IRuns I Fin.elim0 addArray s
      ((s.upd Accumulate.Acc accTail).upd Sum (.int (x*x+q)::sumTail))
      (20000*(w+1)^2*(xs.length+2)) := by
  let s0 := (s.upd Accumulate.Acc accTail).upd Src ((xs++[x]).map Item.int ++ .mark::s.G Src)
  let s1 := ((s0.upd Src (s.G Src)).upd Value (.int x::s.G Value))
  let s2 := s1.upd Value (.int (x*x)::s.G Value)
  let s3 := ((s2.upd Value (s.G Value)).upd Sum sumTail).upd Sum (.int (x*x+q)::sumTail)
  have h0 : IExec I Fin.elim0 (transferArray Accumulate.Acc Src TransferTmp) s s0 (2*moveIntsCost (xs++[x])+4) :=
    transferArray_exec I Accumulate.Acc Src TransferTmp (by decide) (by decide) (by decide) s _ accTail hAcc
  have h1 : IExec I Fin.elim0 takeTop s0 s1
      (moveIntsCost (xs++[x])+(2*moveCost (zsz x)+19)+clearIntsCost xs.reverse+3) := by
    have h := takeTop_exec I s0 xs x (s.G Src) (by simp [s0])
    simpa [s1,s0] using h
  have hx := hw x (by simp)
  have h2 : IRuns I Fin.elim0 Square.program s1 s2 (10000*(w+1)^2) :=
    Square.program_runs I s1 x (s.G Value) w (by simp [s1]) hx
  have h3 : IExec I Fin.elim0 (.op (.add Value Sum Sum)) s2 s3
      (addIntCost (zsz (x*x)+zsz q)) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.add (s := s2) (i := Value) (j := Sum) (k := Sum) (a := x*x) (b := q)
        (Li := s.G Value) (Lj := sumTail) (by decide) (by simp [s2]) (by simp [s2,s1,s0,hSum]))
    simpa [s3,s2] using h
  have he : s3=(s.upd Accumulate.Acc accTail).upd Sum (.int (x*x+q)::sumTail) := by
    apply itemState_ext
    · intro r
      by_cases hA : r=20 <;> by_cases hS : r=79 <;> by_cases hV : r=70 <;> by_cases hR : r=1 <;>
        simp [s3,s2,s1,s0,IState.upd,Function.update_apply,hA,hS,hV,hR]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.seq (Native.of_exec h1) (Native.seq h2 (Native.of_exec h3)))
  rw [he] at h
  change IRuns I Fin.elim0 addArray s _ _ at h
  apply Native.mono h
  have hm := Wedge.moveIntsCost_bound (xs++[x]) w hw
  have ht := takeTop_cost_bound xs x w hw
  have hxx := Square.zsz_mul_le x x w w hx hx
  have ha : addIntCost (zsz (x*x)+zsz q)≤1000*(w+1) := by
    rw [Wedge.addIntCost_formula]
    omega
  simp only [List.length_append,List.length_singleton] at hm
  nlinarith [Nat.zero_le (w*w*xs.length)]

end KoanaKPaths.Machine.Norm

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
attribute [local simp] PredecessorCounter Predecessor StateIndex Accumulate.Acc VerticesTemplate LabelTmp
  Wedge.D Wedge.HC Wedge.DC Wedge.Aux Norm.Sum





lemma normState_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n)) (a : Fin k)
    (atail sumTail : List Item) (hCore : Core s ω arcs k)
    (hA : s.G StateIndex=.int (a.val : ℤ)::atail) (hCount : s.G PredecessorCounter=[])
    (hSum : s.G Norm.Sum=.int (normPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a.val)::sumTail) :
    IRuns I Wedge.prog normState s
      ((s.upd StateIndex (.int ((a.val+1 : ℕ) : ℤ)::atail)).upd Norm.Sum
        (.int (normPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (a.val+1))::sumTail))
      (normStateCost n k) := by
  let C := terminalPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a n
  let xs := coefficientList C
  let x := C Finset.univ
  let q := normPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a.val
  let s0 := s.upd Accumulate.Acc (List.replicate (2^k) (.int 0) ++ .mark::s.G Accumulate.Acc)
  let s1 := s0.upd Predecessor (.int 0::s.G Predecessor)
  let s2 := s1.upd PredecessorCounter (List.replicate n .mark)
  let s3 := terminalLoopState s2 ω arcs a n (s.G Predecessor) (s.G Accumulate.Acc)
  let s4 := s3.upd Predecessor (s.G Predecessor)
  let s5 := (s4.upd Accumulate.Acc (s.G Accumulate.Acc)).upd Norm.Sum (.int (x*x+q)::sumTail)
  let s6 := s5.upd StateIndex (.int ((a.val+1 : ℕ) : ℤ)::atail)
  have h0 : IRuns I Wedge.prog (liftClosed (Wedge.zeroArray Accumulate.Acc)) s s0 (500*2^k) := by
    have h := liftClosed_exec I Wedge.prog (Wedge.zeroArray_exec I Accumulate.Acc
      (by decide) (by decide) (by decide) (by decide) s k [] (by simp [cls])
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 3 (by decide))
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 10 (by decide))
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 11 (by decide))
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 12 (by decide)))
    exact Native.mono (Native.of_exec h) (Wedge.zeroArray_cost k)
  have h1 : IExec I Wedge.prog (.op (.const Predecessor 0)) s0 s1 2 := by
    simpa [s1,s0,Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := Wedge.prog) (IOp.Step.const (s := s0) (i := Predecessor) 0))
  have h2 : IExec I Wedge.prog (liftClosed (copyMarks VerticesTemplate PredecessorCounter LabelTmp)) s1 s2 (65*n+60) := by
    have h := liftClosed_exec I Wedge.prog (copyMarks_exec I VerticesTemplate PredecessorCounter LabelTmp
      (by decide) (by decide) (by decide) s1 n [] (by simp [cls])
      (by simpa [s1,s0,coreStack,NS,Wedge.NS] using hCore.at 59 (by decide))
      (by simpa [s1,s0,coreStack,NS,Wedge.NS] using hCore.at 89 (by decide)))
    simpa [s2,s1,s0,hCount] using h
  have hCP : Core s2 ω arcs k :=
    ((hCore.upd Accumulate.Acc (by decide) _).upd Predecessor (by decide) _).upd PredecessorCounter (by decide) _
  have h3 : IRuns I Wedge.prog terminalLoop s2 s3 ((terminalCellCost n k+31)*n+30) :=
    terminalLoop_runs I s2 ω arcs a atail (s.G Predecessor) (s.G Accumulate.Acc) hCP
      (by simp [s2,s1,s0,hA]) (by simp [s2,s1,s0]) (by simp [s2])
      (by simp [s2,s1,s0,terminalPrefix,finPrefix_zero,coefficientList_zero,List.map_replicate])
  have h4 : IExec I Wedge.prog (.op (.drop Predecessor)) s3 s4 (2*zsz (n : ℤ)+2) :=
    .op (.drop (by simp [s3,terminalLoopState]))
  have hxlast : xs.dropLast++[x]=xs := List.dropLast_append_getLast? x (by simp [xs,x,coefficientList_last])
  have hxw := terminalPrefix_width arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a n
  have h5 : IRuns I Wedge.prog (liftClosed Norm.addArray) s4 s5
      (20000*(wordWidth n k+1)^2*(xs.dropLast.length+2)) := by
    have h := liftClosed_runs I Wedge.prog (Norm.addArray_runs I s4 xs.dropLast x q
      (s.G Accumulate.Acc) sumTail (wordWidth n k)
      (by simp [hxlast,s4,s3,terminalLoopState,xs,C])
      (by simp [s4,s3,terminalLoopState,s2,s1,s0,hSum,q])
      (by simpa only [hxlast] using hxw) (normPrefix_bounds arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a.val).2)
    exact h
  have h6 : IRuns I Wedge.prog (liftClosed (Square.increment StateIndex)) s5 s6 (13000*(wordWidth n k+1)^2) :=
    liftClosed_runs I Wedge.prog (Square.increment_runs I StateIndex (by decide) s5 a.val (wordWidth n k) atail
      (by simp [s5,s4,s3,terminalLoopState,s2,s1,s0,hA]) (wordWidth_pos n k) (row_word_width n k a.val (by omega)))
  have hsum : x*x+q=normPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (a.val+1) := by
    unfold normPrefix
    rw [finPrefix_succ _ a.val a.isLt]
    simp only [x,C,terminalPrefix_full,q,normPrefix,pow_two]
    exact add_comm _ _
  have hpost : s6=(s.upd StateIndex (.int ((a.val+1 : ℕ) : ℤ)::atail)).upd Norm.Sum
      (.int (normPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (a.val+1))::sumTail) := by
    rw [←hsum]
    apply itemState_ext
    · intro r
      by_cases h80 : r=80 <;> by_cases h91 : r=91 <;> by_cases h20 : r=20 <;> by_cases h79 : r=79 <;> by_cases h83 : r=83 <;>
        simp [s6,s5,s4,s3,terminalLoopState,s2,s1,s0,IState.upd,Function.update_apply,h80,h91,h20,h79,h83,hCount]
    · rfl
    · rfl
  have h := Native.seq h0 (Native.seq (Native.of_exec h1) (Native.seq (Native.of_exec h2)
    (Native.seq h3 (Native.seq (Native.of_exec h4) (Native.seq h5 h6)))))
  rw [hpost] at h
  change IRuns I Wedge.prog normState s _ _ at h
  apply Native.mono h
  have hlen : xs.dropLast.length+1=2^k := by
    have hh := congrArg List.length hxlast
    simpa [xs,coefficientList_length] using hh
  have hnw : zsz (n : ℤ)≤ wordWidth n k := by
    have hh := Controls.zsz_nat_le n
    unfold wordWidth; nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]
  have hpow : 1≤2^k := Nat.one_le_pow k 2 (by omega)
  unfold normStateCost
  nlinarith [Nat.zero_le ((wordWidth n k)^2*2^k)]

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (a : Fin k)
  (atail sumTail : List.{0} NLogN.Item) (hCore : @KoanaKPaths.Machine.Trial.Core n k s ω arcs k)
  (hA :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.StateIndex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val k a))) atail))
  (hCount :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PredecessorCounter)
      (@List.nil.{0} NLogN.Item))
  (hSum :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Norm.Sum)
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@KoanaKPaths.Main.normPrefix n k arcs
            (@Prod.fst.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                  Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                (KoanaKPaths.Main.trialEquiv n k) ω))
            (@Prod.snd.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                  Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                (KoanaKPaths.Main.trialEquiv n k) ω))
            (@Fin.val k a)))
        sumTail)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.normState s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.StateIndex
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@Nat.cast.{0} Int instNatCastInt
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val k a)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          atail))
      KoanaKPaths.Machine.Norm.Sum
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@KoanaKPaths.Main.normPrefix n k arcs
            (@Prod.fst.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                  Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                (KoanaKPaths.Main.trialEquiv n k) ω))
            (@Prod.snd.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                  Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                (KoanaKPaths.Main.trialEquiv n k) ω))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val k a)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        sumTail))
    (KoanaKPaths.Machine.Trial.normStateCost n k) := by
  exact @KoanaKPaths.Machine.Trial.normState_runs
