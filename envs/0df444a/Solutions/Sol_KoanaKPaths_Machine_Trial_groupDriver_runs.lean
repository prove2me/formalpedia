-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.groupDriver_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:43:36.089435+00:00
-- url     : https://prove2.me/submissions/ef2d700f-ed0f-4b54-af57-e1bc9773e161

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
import Theorems.Thm_KoanaKPaths_Machine_Trial_groupFold_runs
import Theorems.Thm_KoanaKPaths_Machine_copyMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveInts_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_transferArray_exec
import Theorems.Thm_KoanaKPaths_Main_denseLayer_correct
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

lemma zsz_add_le (x y : ℤ) (w : ℕ) (hx : zsz x≤w) (hy : zsz y≤w) : zsz (x+y)≤w+1 := by
  apply (zsz_le_iff _ _).mpr
  have hx' := (zsz_le_iff x w).mp hx
  have hy' := (zsz_le_iff y w).mp hy
  have ha := Int.natAbs_add_le x y
  rw [pow_succ]
  omega











lemma moveIntsCost_bound (xs : List ℤ) (w : ℕ) (h : ∀ z∈xs, zsz z≤w) :
    moveIntsCost xs ≤ 200*(w+1)*(xs.length+1) := by
  have hh := moveIntsCost_le xs w h
  nlinarith





















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

lemma denseTrial_correct {n k ℓ : ℕ} (hk : 1≤k) (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    denseTrial arcs σ R=(sketchFrobSq (walkTensor n arcs k) σ R k).toNat := by
  unfold denseTrial
  simp only [denseOutput_correct,coefficientList_last,Option.getD_some]
  rw [sum_finRange,graph_dp_sketch hk]

lemma denseTrial_eq_trialNumerator {n k : ℕ} (hk : 1≤k) (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k k) :
    denseTrial arcs σ R=trialNumerator (walkTensor n arcs k) (σ,R) :=
  denseTrial_correct hk arcs σ R

end KoanaKPaths.Main

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




end KoanaKPaths.Machine.Norm

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main









lemma Ready.upd {n k : ℕ} {s : IState NS} {arcs : List (Fin n × Fin n)} (h : Ready (k := k) s arcs)
    (j : Fin NS) (hj : j∉readyRegisters) (xs : List Item) : Ready (k := k) (s.upd j xs) arcs := by
  intro r hr
  have hne : r≠j := by rintro rfl; exact hj hr
  simpa [IState.upd,hne] using h r hr



end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
lemma trialNumerator_word_width {n k : ℕ} (ω : Fin (trialBits n k)→Bool)
    (arcs : List (Fin n × Fin n)) (hk : 1≤ k) :
    zsz (trialNumerator (walkTensor n arcs k) (trialEquiv n k ω) : ℤ)≤ wordWidth n k := by
  rw [←denseTrial_eq_trialNumerator hk]
  have h := denseTrial_width arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2
  have hp := trialWidth_polynomial n k
  unfold wordWidth
  omega
end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
open NLogN
namespace KoanaKPaths.Machine.Wedge
lemma sum_word_width (xs : List ℤ) (w : ℕ) (hw : ∀ x∈xs, zsz x≤ w) : zsz xs.sum≤ w+xs.length := by
  induction xs with
  | nil => simp [zsz_eq_size]
  | cons x xs ih =>
    have hx := hw x (by simp)
    have ht := ih (fun y hy => hw y (by simp [hy]))
    have h := zsz_add_le x xs.sum (w+xs.length) (by omega) ht
    simpa only [List.sum_cons,List.length_cons,Nat.add_assoc] using h
end KoanaKPaths.Machine.Wedge

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}



lemma reverseArray_exec (I : List Sym) (src tmp aux : Fin S)
    (hst : src≠tmp) (hsa : src≠aux) (hta : tmp≠aux)
    (s : IState S) (xs : List ℤ) (tail : List Item)
    (hs : s.G src=xs.map Item.int ++ .mark::tail) :
    IExec I Fin.elim0 (reverseArray src tmp aux) s
      (s.upd src (xs.reverse.map Item.int ++ .mark::tail)) (3*moveIntsCost xs+6) := by
  let s0 := (s.upd src tail).upd tmp (xs.map Item.int ++ .mark::s.G tmp)
  let s1 := s0.upd src (.mark::tail)
  let s2 := (s1.upd tmp (.mark::s.G tmp)).upd src (xs.reverse.map Item.int ++ .mark::tail)
  let s3 := s2.upd tmp (s.G tmp)
  have h0 : IExec I Fin.elim0 (transferArray src tmp aux) s s0 (2*moveIntsCost xs+4) :=
    transferArray_exec I src tmp aux hst hsa hta s xs tail hs
  have h1 : IExec I Fin.elim0 (.op (.mark src)) s0 s1 1 := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt S 0)) (IOp.Step.mark (s := s0) (i := src))
    simpa [s1,s0,hst] using h
  have h2 : IExec I Fin.elim0 (moveInts tmp src) s1 s2 (moveIntsCost xs) := by
    have h := moveInts_exec I tmp src (Ne.symm hst) s1 xs (.mark::s.G tmp)
      (by simp [cls]) (by simp [s1,s0,Ne.symm hst])
    simpa [s2,s1] using h
  have h3 : IExec I Fin.elim0 (.op (.unmark tmp)) s2 s3 1 :=
    .op (.unmark (by simp [s2,Ne.symm hst]))
  have he : s3=s.upd src (xs.reverse.map Item.int ++ .mark::tail) := by
    apply itemState_ext
    · intro i
      by_cases hS : i=src
      · subst i; simp [s3,s2,s1,s0,hst]
      by_cases hT : i=tmp
      · subst i; simp [s3,s2,s1,s0,Ne.symm hst]
      simp [s3,s2,s1,s0,IState.upd,Function.update_apply,hS,hT]
    · rfl
    · rfl
  have h := IExec.seq h0 (IExec.seq h1 (IExec.seq h2 h3))
  rw [he] at h
  change IExec I Fin.elim0 (reverseArray src tmp aux) s _ _ at h
  convert h using 1 <;> omega

lemma reverseArray_cost (xs : List ℤ) (w : ℕ) (hw : ∀ x∈xs, zsz x≤ w) :
    3*moveIntsCost xs+6≤1000*(w+1)*(xs.length+1) := by
  have h := Wedge.moveIntsCost_bound xs w hw
  nlinarith

end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main


attribute [local simp] GroupTemplate OuterCopyTmp GroupCounter TrialCounter TrialTemplate GroupCopyTmp Coins Balanced.Records Balanced.Restore





lemma groupDriver_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (arcs : List (Fin n × Fin n)) (oss : List (List (Fin (trialBits n k)→Bool)))
    (m : ℕ) (tail : List Item) (hk : 1≤ k) (hr : Ready (k := k) s arcs)
    (hlen : ∀ os∈oss, os.length=m)
    (hQ : s.G GroupTemplate=List.replicate oss.length .mark) (hCount : s.G GroupCounter=[])
    (ht : s.G TrialTemplate=List.replicate m .mark) (hc : s.G TrialCounter=[])
    (hx : s.G GroupCopyTmp=[]) (hy : s.G OuterCopyTmp=[]) (hRestore : s.G Balanced.Restore=[])
    (hCoins : s.G Coins=groupsStream oss++tail) :
    IRuns I Wedge.prog groupDriver s
      ((s.upd Coins tail).upd Balanced.Records ((groupSums arcs oss).map Item.int ++ .mark::s.G Balanced.Records))
      (groupDriverCost n k arcs.length m oss.length) := by
  let xs := groupSums arcs oss
  let s0 := s.upd Balanced.Records (.mark::s.G Balanced.Records)
  let s1 := s0.upd GroupCounter (List.replicate oss.length .mark)
  let s2 := groupFoldState s1 arcs oss tail
  let s3 := s2.upd Balanced.Records (xs.map Item.int ++ .mark::s.G Balanced.Records)
  have h0 : IExec I Wedge.prog (.op (.mark Balanced.Records)) s s0 1 := .op (.mark)
  have h1 : IExec I Wedge.prog (liftClosed (copyMarks GroupTemplate GroupCounter OuterCopyTmp)) s0 s1
      (65*oss.length+60) := by
    have h := liftClosed_exec I Wedge.prog (copyMarks_exec I GroupTemplate GroupCounter OuterCopyTmp
      (by decide) (by decide) (by decide) s0 oss.length [] (by simp [cls]) (by simp [s0,hQ]) (by simp [s0,hy]))
    simpa [s1,s0,hCount] using h
  have hr1 : Ready (k := k) s1 arcs := (hr.upd Balanced.Records (by decide) _).upd GroupCounter (by decide) _
  have h2 : IRuns I Wedge.prog groupFold s1 s2
      ((groupNativeCost n k arcs.length m+31)*oss.length+30) :=
    groupFold_runs I s1 arcs oss m tail hk hr1 hlen (by simp [s1]) (by simp [s1,s0,ht])
      (by simp [s1,s0,hc]) (by simp [s1,s0,hx]) (by simp [s1,s0,hRestore]) (by simp [s1,s0,hCoins])
  have hxwidth : ∀ x∈xs, zsz x≤ wordWidth n k+m := by
    intro x hxm
    obtain ⟨os,hos,rfl⟩ := List.mem_map.mp hxm
    have hw : ∀ y∈numerators arcs os, zsz y≤ wordWidth n k := by
      intro y hym
      obtain ⟨ω,hω,rfl⟩ := List.mem_map.mp hym
      exact trialNumerator_word_width ω arcs hk
    have hh := Wedge.sum_word_width (numerators arcs os) (wordWidth n k) hw
    simpa [numerators,hlen os hos] using hh
  have h3 : IRuns I Wedge.prog (liftClosed (reverseArray Balanced.Records GroupCopyTmp OuterCopyTmp)) s2 s3
      (1000*(wordWidth n k+m+1)*(oss.length+1)) := by
    have h := liftClosed_exec I Wedge.prog (reverseArray_exec I Balanced.Records GroupCopyTmp OuterCopyTmp
      (by decide) (by decide) (by decide) s2 xs.reverse (s.G Balanced.Records)
      (by simp [s2,groupFoldState,s1,s0,xs]))
    have hb := reverseArray_cost xs.reverse (wordWidth n k+m) (by simpa using hxwidth)
    have hlenxs : xs.length=oss.length := by simp [xs,groupSums]
    simp only [List.length_reverse,hlenxs] at hb
    apply Native.mono (Native.of_exec (show IExec I Wedge.prog _ s2 s3 _ from by simpa [s3] using h)) hb
  have hpost : s3=(s.upd Coins tail).upd Balanced.Records (xs.map Item.int ++ .mark::s.G Balanced.Records) := by
    apply itemState_ext
    · intro r
      by_cases h100 : r=100 <;> by_cases h52 : r=52 <;> by_cases h107 : r=107 <;>
        simp [s3,s2,groupFoldState,s1,s0,IState.upd,Function.update_apply,h100,h52,h107,hCount]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.seq (Native.of_exec h1) (Native.seq h2 h3))
  rw [hpost] at h
  change IRuns I Wedge.prog groupDriver s _ _ at h
  apply Native.mono h
  unfold groupDriverCost
  nlinarith

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n)))
  (oss : List.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))) (m : Nat) (tail : List.{0} NLogN.Item)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hr : @KoanaKPaths.Machine.Trial.Ready n k s arcs)
  (hlen :
    ∀ (os : List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)),
      @Membership.mem.{0, 0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))
          (List.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)))
          (@List.instMembership.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))) oss os →
        @Eq.{1} Nat (@List.length.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool) os) m)
  (hQ :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.GroupTemplate)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)) oss)
        NLogN.Item.mark))
  (hCount :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.GroupCounter)
      (@List.nil.{0} NLogN.Item))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.TrialTemplate)
      (@List.replicate.{0} NLogN.Item m NLogN.Item.mark))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.TrialCounter)
      (@List.nil.{0} NLogN.Item))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.GroupCopyTmp)
      (@List.nil.{0} NLogN.Item))
  (hy :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.OuterCopyTmp)
      (@List.nil.{0} NLogN.Item))
  (hRestore :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Restore)
      (@List.nil.{0} NLogN.Item))
  (hCoins :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@KoanaKPaths.Machine.Trial.groupsStream n k oss) tail)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.groupDriver s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins tail)
      KoanaKPaths.Machine.Balanced.Records
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@KoanaKPaths.Machine.Trial.groupSums n k arcs oss))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark
          (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Records))))
    (KoanaKPaths.Machine.Trial.groupDriverCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs) m
      (@List.length.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)) oss)) := by
  exact @KoanaKPaths.Machine.Trial.groupDriver_runs
