-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.laterCell_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:45:20.387004+00:00
-- url     : https://prove2.me/submissions/0a056024-eab6-47ea-8c2a-9f07ffc71f0b

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
import Theorems.Thm_KoanaKPaths_Machine_GraphArray_laterArray_runs
import Theorems.Thm_KoanaKPaths_Machine_Square_increment_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_predecessors_runs
import Theorems.Thm_KoanaKPaths_Machine_copyMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_powerMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_repeatInts_exec
import Theorems.Thm_KoanaKPaths_Main_denseLayer_correct
import Theorems.Thm_KoanaKPaths_Main_graphLayer_natAbs
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

@[simp] lemma castSuccEmb_apply {k : ℕ} (r : Fin k) :
    Fin.castSuccOrderEmb.toEmbedding r = r.castSucc := rfl

lemma last_not_lower {k : ℕ} (S : Finset (Fin k)) : Fin.last k ∉ lowerSet S := by
  intro h
  change Fin.last k ∈ S.map Fin.castSuccOrderEmb.toEmbedding at h
  obtain ⟨r,_,hr⟩ := Finset.mem_map.mp h
  exact Fin.castSucc_ne_last r hr

lemma lower_card {k : ℕ} (S : Finset (Fin k)) : (lowerSet S).card = S.card := by simp [lowerSet]
lemma upper_card {k : ℕ} (S : Finset (Fin k)) : (upperSet S).card = S.card+1 := by
  simp [upperSet,last_not_lower,lower_card]

lemma sort_lower {k : ℕ} (S : Finset (Fin k)) : (lowerSet S).sort = S.sort.map Fin.castSucc := by
  exact (Finset.map_sort Fin.castSuccOrderEmb.toEmbedding S (· ≤ ·) (· ≤ ·)
    (fun a _ b _ => by rfl)).symm

lemma sort_upper {k : ℕ} (S : Finset (Fin k)) :
    (upperSet S).sort = S.sort.map Fin.castSucc ++ [Fin.last k] := by
  have hsorted : (S.sort.map Fin.castSucc ++ [Fin.last k]).SortedLT := by
    apply List.Pairwise.sortedLT
    rw [List.pairwise_append]
    refine ⟨(S.sortedLT_sort.pairwise.map Fin.castSucc (fun a b h => Fin.strictMono_castSucc h)),by simp,?_⟩
    intro a ha b hb
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp ha
    have hb' : b=Fin.last k := by simpa using hb
    subst b
    exact r.isLt
  apply (upperSet S).sortedLT_sort.eq_of_mem_iff hsorted
  intro r
  simp only [Finset.mem_sort,upperSet,lowerSet,Finset.mem_insert,Finset.mem_map,
    List.mem_append,List.mem_map,List.mem_singleton,Finset.mem_sort]
  change (r=Fin.last k ∨ ∃ a ∈ S, a.castSucc=r) ↔ (∃ a ∈ S, a.castSucc=r) ∨ r=Fin.last k
  exact or_comm

lemma idxOf_map_inj {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (L : List α) (a : α) :
    (L.map f).idxOf (f a) = L.idxOf a := by
  induction L with
  | nil => simp
  | cons b L ih =>
    by_cases h : b=a
    · subst b; simp
    · simp [List.idxOf_cons,h,hf.ne h,ih]

lemma lower_rank {k : ℕ} (S : Finset (Fin k)) (r : Fin k) :
    (lowerSet S).sort.idxOf r.castSucc = S.sort.idxOf r := by
  rw [sort_lower,idxOf_map_inj Fin.castSucc (Fin.castSucc_injective k)]

lemma upper_rank {k : ℕ} (S : Finset (Fin k)) (r : Fin k) (hr : r ∈ S) :
    (upperSet S).sort.idxOf r.castSucc = S.sort.idxOf r := by
  rw [sort_upper,List.idxOf_append_of_mem]
  · exact idxOf_map_inj Fin.castSucc (Fin.castSucc_injective k) _ _
  · exact List.mem_map.mpr ⟨r,by simpa using hr,rfl⟩

lemma upper_last_rank {k : ℕ} (S : Finset (Fin k)) :
    (upperSet S).sort.idxOf (Fin.last k) = S.card := by
  rw [sort_upper,List.idxOf_append_of_notMem]
  · simp
  · intro h
    obtain ⟨r,_,hr⟩ := List.mem_map.mp h
    exact Fin.castSucc_ne_last r hr

lemma lower_erase {k : ℕ} (S : Finset (Fin k)) (r : Fin k) :
    (lowerSet S).erase r.castSucc = lowerSet (S.erase r) := by
  exact (Finset.map_erase Fin.castSuccOrderEmb.toEmbedding S r).symm

lemma upper_erase {k : ℕ} (S : Finset (Fin k)) (r : Fin k) :
    (upperSet S).erase r.castSucc = upperSet (S.erase r) := by
  unfold upperSet
  rw [Finset.erase_insert_of_ne (Ne.symm (Fin.castSucc_ne_last r)),lower_erase]

lemma upper_erase_last {k : ℕ} (S : Finset (Fin k)) :
    (upperSet S).erase (Fin.last k) = lowerSet S := by simp [upperSet,last_not_lower]

lemma subsetOrder_length (k : ℕ) : (subsetOrder k).length = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [subsetOrder,ih,pow_succ]; omega

lemma wedge_finset {k : ℕ} (A : Coordinates k) (v : Fin k → ℤ) (S : Finset (Fin k)) :
    wedgeRight A v S = ∑ r ∈ S,
      (-1 : ℤ)^(S.card-1+S.sort.idxOf r)*A (S.erase r)*v r := by
  unfold wedgeRight
  have h := Finset.sum_coe_sort (M := ℤ) S (fun r : Fin k =>
    (-1 : ℤ)^(S.card-1+S.sort.idxOf r)*A (S.erase r)*v r)
  convert h using 1 <;> rfl

lemma wedge_lower {k : ℕ} (A : Coordinates (k+1)) (v : Fin (k+1) → ℤ) (S : Finset (Fin k)) :
    wedgeRight A v (lowerSet S) =
      wedgeRight (fun T => A (lowerSet T)) (fun r => v r.castSucc) S := by
  rw [wedge_finset,wedge_finset]
  let F : Fin (k+1) → ℤ := fun r =>
    (-1 : ℤ)^((lowerSet S).card-1+(lowerSet S).sort.idxOf r)*A ((lowerSet S).erase r)*v r
  calc
    _ = ∑ r ∈ S.map Fin.castSuccOrderEmb.toEmbedding, F r := by rfl
    _ = ∑ r ∈ S, F (Fin.castSuccOrderEmb.toEmbedding r) :=
      Finset.sum_map (M := ℤ) S Fin.castSuccOrderEmb.toEmbedding F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      dsimp only [F]
      rw [castSuccEmb_apply,lower_card,lower_rank,lower_erase]

lemma wedge_upper {k : ℕ} (A : Coordinates (k+1)) (v : Fin (k+1) → ℤ) (S : Finset (Fin k)) :
    wedgeRight A v (upperSet S) = v (Fin.last k)*A (lowerSet S) -
      wedgeRight (fun T => A (upperSet T)) (fun r => v r.castSucc) S := by
  let F : Fin (k+1) → ℤ := fun r =>
    (-1 : ℤ)^((upperSet S).card-1+(upperSet S).sort.idxOf r)*A ((upperSet S).erase r)*v r
  have hsum : wedgeRight A v (upperSet S) = F (Fin.last k)+∑ r ∈ lowerSet S, F r := by
    have hw := wedge_finset A v (upperSet S)
    calc
      _ = ∑ r ∈ upperSet S, F r := by convert hw using 1 <;> rfl
      _ = _ := Finset.sum_insert (last_not_lower S)
  have hlast : F (Fin.last k) = v (Fin.last k)*A (lowerSet S) := by
    dsimp only [F]
    rw [upper_card,upper_last_rank,upper_erase_last]
    rw [show S.card+1-1+S.card = 2*S.card by omega,pow_mul]
    norm_num
    ring
  have hrest : (∑ r ∈ lowerSet S, F r) =
      -wedgeRight (fun T => A (upperSet T)) (fun r => v r.castSucc) S := by
    have hm : (∑ r ∈ lowerSet S, F r) = ∑ r ∈ S, F r.castSucc := by
      convert (Finset.sum_map (M := ℤ) S Fin.castSuccOrderEmb.toEmbedding F) using 1 <;> rfl
    rw [hm,wedge_finset,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp only [F]
    rw [upper_card,upper_rank S r hr,upper_erase]
    have hc : 0 < S.card := Finset.card_pos.mpr ⟨r,hr⟩
    have hp (j : ℕ) : S.card+1-1+j = (S.card-1+j)+1 := by omega
    rw [hp,pow_succ]
    ring
  rw [hsum,hlast,hrest]
  rfl

lemma coefficientList_length {k : ℕ} (A : Coordinates k) : (coefficientList A).length = 2^k := by
  simp [coefficientList,subsetOrder_length]

lemma coefficientList_split {k : ℕ} (A : Coordinates (k+1)) :
    coefficientList A = coefficientList (fun S => A (lowerSet S)) ++
      coefficientList (fun S => A (upperSet S)) := by
  simp [coefficientList,subsetOrder,List.map_map,Function.comp_def]

lemma zipWith_same_map {α β γ δ : Type} (L : List α) (f : α → β) (g : α → γ) (h : β → γ → δ) :
    List.zipWith h (L.map f) (L.map g) = L.map (fun x => h (f x) (g x)) := by
  induction L <;> simp_all

theorem wedgeList_correct (k : ℕ) (A : Coordinates k) (v : List ℤ) :
    wedgeList k (coefficientList A) v =
      coefficientList (wedgeRight A (fun r => v.getD r.val 0)) := by
  induction k with
  | zero => simp [wedgeList,coefficientList,subsetOrder,wedgeRight]
  | succ k ih =>
    have hlen : (coefficientList (fun S => A (lowerSet S))).length = 2^k := coefficientList_length _
    simp only [wedgeList,coefficientList_split A]
    rw [List.take_left' hlen,List.drop_left' hlen,ih,ih]
    rw [coefficientList_split]
    congr 1
    · apply List.map_congr_left
      intro S _
      exact (wedge_lower A (fun r => v.getD r.val 0) S).symm
    · simp only [coefficientList]
      rw [zipWith_same_map]
      apply List.map_congr_left
      intro S _
      exact (wedge_upper A (fun r => v.getD r.val 0) S).symm



















lemma coefficientList_zero (k : ℕ) : coefficientList (0 : Coordinates k) = List.replicate (2^k) 0 := by
  change (subsetOrder k).map (fun _ => (0 : ℤ)) = _
  simp [List.map_const,subsetOrder_length]







end KoanaKPaths.ExteriorCoordinates

end

section

set_option maxHeartbeats 1000000
namespace KoanaKPaths.ExteriorCoordinates



lemma wedgeList_congr_vector (d : ℕ) (A v w : List ℤ)
    (h : ∀ j<d, v.getD j 0 = w.getD j 0) : wedgeList d A v = wedgeList d A w := by
  induction d generalizing A with
  | zero => rfl
  | succ d ih =>
    simp only [wedgeList]
    rw [ih _ (fun j hj => h j (by omega)),ih _ (fun j hj => h j (by omega)),h d (by omega)]

lemma wedgeReverse_eq_wedgeList (vs A : List ℤ) :
    wedgeReverse vs A = wedgeList vs.length A vs.reverse := by
  induction vs generalizing A with
  | nil => rfl
  | cons z vs ih =>
    simp only [wedgeReverse,List.length_cons,wedgeList,List.reverse_cons]
    have hg : ∀ j<vs.length, (vs.reverse++[z]).getD j 0 = vs.reverse.getD j 0 := by
      intro j hj
      exact List.getD_append _ _ _ _ (by simpa using hj)
    rw [wedgeList_congr_vector vs.length _ _ _ hg,wedgeList_congr_vector vs.length _ _ _ hg]
    rw [← ih,← ih]
    have hl : (vs.reverse++[z]).getD vs.length 0 = z := by
      rw [List.getD_append_right _ _ _ _ (by simp),List.length_reverse,Nat.sub_self]
      rfl
    rw [hl]



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

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Main

lemma trialEquiv_label {n k : ℕ} (ω : Fin (trialBits n k)→Bool) (v : Fin n) (r : Fin k) :
    (trialEquiv n k ω).1 v r=ω (trialIndexEquiv n k (.inl (v,r))) := rfl





lemma trialIndex_label {n k : ℕ} (v : Fin n) (r : Fin k) :
    (trialIndexEquiv n k (.inl (v,r))).val=v.val*k+r.val := by
  change r.val+k*v.val=v.val*k+r.val
  ring









end KoanaKPaths.Main

end

section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates





lemma labelList_get {n k : ℕ} (σ : Labels n k) (v : Fin n) (r : Fin k) :
    (labelList σ v).getD r.val 0=sgn (σ v r) := by
  rw [List.getD_eq_getElem _ _ (by simpa [labelList] using r.isLt)]
  simp [labelList]
















end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main







lemma signsOf_get {n k : ℕ} (ω : Fin (trialBits n k)→Bool) (j : Fin (trialBits n k)) :
    (signsOf ω).getD j.val 1=sgn (ω j) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [signsOf,List.length_ofFn] using j.isLt)]
  simp only [signsOf,List.getElem_ofFn]

lemma labelBlock_ofFn (xs : List ℤ) (k v r m : ℕ) :
    labelBlock xs k v r m=List.ofFn (fun i : Fin m => xs.getD (v*k+(r+i.val)) 1) := by
  induction m generalizing r with
  | zero => rfl
  | succ m ih =>
    rw [labelBlock,List.ofFn_succ]
    congr 1
    rw [ih]
    apply congrArg List.ofFn
    funext i
    congr 1
    simp only [Fin.val_succ]
    omega

lemma labelBlock_decodes {n k : ℕ} (ω : Fin (trialBits n k)→Bool) (v : Fin n) :
    labelBlock (signsOf ω) k v.val 0 k=labelList (trialEquiv n k ω).1 v := by
  rw [labelBlock_ofFn]
  unfold labelList
  rw [← List.ofFn_eq_map]
  apply congrArg List.ofFn
  funext r
  have h := signsOf_get ω (trialIndexEquiv n k (.inl (v,r)))
  rw [trialIndex_label] at h
  simpa only [Nat.zero_add,trialEquiv_label] using h



end KoanaKPaths.Machine.Trial

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

lemma sgn_natAbs (b : Bool) : (sgn b).natAbs=1 := by cases b <;> norm_num [sgn]










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
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates



lemma predecessorTerm_natAbs {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v : Fin n)
    (q : Fin n × Fin k) (S : Finset (Fin k)) :
    (predecessorTerm arcs σ R p i a v q S).natAbs≤(layerRadius n k k)^p := by
  unfold predecessorTerm
  split_ifs
  · simpa only [Pi.smul_apply,smul_eq_mul,Int.natAbs_mul,sgn_natAbs,one_mul] using
      graphLayer_natAbs arcs σ R p q.1 q.2 S
  · simp

lemma predecessorSum_natAbs {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v : Fin n)
    (Q : Finset (Fin n × Fin k)) (S : Finset (Fin k)) :
    ((∑ q∈Q, predecessorTerm arcs σ R p i a v q) S).natAbs≤ n*k*(layerRadius n k k)^p := by
  classical
  simp only [Finset.sum_apply]
  calc
    _ ≤ ∑ q∈Q, (predecessorTerm arcs σ R p i a v q S).natAbs := natAbs_sum_le Q _
    _ ≤ ∑ _q∈Q, (layerRadius n k k)^p := Finset.sum_le_sum
      (fun q _ => predecessorTerm_natAbs arcs σ R p i a v q S)
    _ = Q.card*(layerRadius n k k)^p := by simp
    _ ≤ n*k*(layerRadius n k k)^p := Nat.mul_le_mul_right _ (by
      simpa only [Fintype.card_prod,Fintype.card_fin] using Q.card_le_univ)

lemma predecessorSum_width {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v : Fin n)
    (Q : Finset (Fin n × Fin k)) (S : Finset (Fin k)) :
    NLogN.zsz ((∑ q∈Q, predecessorTerm arcs σ R p i a v q) S)≤
      n+k+(n+k+k+3)*p+1 := by
  have hr := Nat.pow_le_pow_left (layerRadius_le_exp n k k) p
  rw [← pow_mul] at hr
  have hn : n≤2^n := Nat.le_of_lt Nat.lt_two_pow_self
  have hk : k≤2^k := Nat.le_of_lt Nat.lt_two_pow_self
  have hnk := Nat.mul_le_mul hn hk
  rw [← pow_add] at hnk
  have h := (predecessorSum_natAbs arcs σ R p i a v Q S).trans (Nat.mul_le_mul hnk hr)
  rw [← pow_add] at h
  apply (Machine.Wedge.zsz_le_iff _ _).mpr
  rw [pow_succ]
  have hp : 0<2^(n+k+(n+k+k+3)*p) := by positivity
  omega

lemma predecessorSum_width_polynomial {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (hp : p≤ k) (i : Fin (k-1)) (a : Fin k) (v : Fin n)
    (Q : Finset (Fin n × Fin k)) (S : Finset (Fin k)) :
    NLogN.zsz ((∑ q∈Q, predecessorTerm arcs σ R p i a v q) S)≤100*(1+n+k)^2 := by
  have h := predecessorSum_width arcs σ R p i a v Q S
  have hmul := Nat.mul_le_mul_left (n+k+k+3) hp
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (n*k),Nat.zero_le (k*k)]

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates



lemma predSet_zero (n k : ℕ) : predSet n k 0 0=∅ := by ext q; simp [predSet]



lemma predSet_full (n k : ℕ) : predSet n k n 0=Finset.univ := by
  ext q; simp [predSet,q.1.isLt]



lemma predSum_zero {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v : Fin n) :
    predSum arcs σ R p i a v 0 0=0 := by simp [predSum,predSet_zero]


lemma predSum_width {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (hp : p≤ k) (i : Fin (k-1)) (a : Fin k) (v : Fin n) (u b : ℕ) :
    ∀ x∈coefficientList (predSum arcs σ R p i a v u b), NLogN.zsz x≤100*(1+n+k)^2 := by
  intro x hx
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hx
  exact predecessorSum_width_polynomial arcs σ R p hp i a v _ S

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates

lemma predSum_full {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v : Fin n) :
    predSum arcs σ R p i a v n 0=∑ u : Fin n, if (u,v)∈arcs.toFinset then
      ∑ b : Fin k, sgn (R.2 i a (b,v)) • graphLayer arcs σ R p u b else 0 := by
  simp only [predSum,predSet_full,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  by_cases ha : (u,v)∈arcs.toFinset <;> simp [predecessorTerm,ha]

lemma later_array_decodes {n k : ℕ} (ω : Fin (trialBits n k)→Bool)
    (arcs : List (Fin n × Fin n)) (i : Fin (k-1)) (v : Fin n) (a : Fin k) :
    wedgeReverse (labelBlock (signsOf ω) k v.val 0 k).reverse
      (coefficientList (predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (i.val+1) i a v n 0))=
      denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (i.val+2) v a := by
  rw [labelBlock_decodes,wedgeReverse_eq_wedgeList]
  have hlen : (labelList (trialEquiv n k ω).1 v).length=k := by simp [labelList]
  rw [List.length_reverse,hlen,List.reverse_reverse,wedgeList_correct,denseLayer_correct]
  simp only [labelList_get,graphLayer, i.isLt, dif_pos, predSum_full]

end KoanaKPaths.Machine.Trial

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
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
attribute [local simp] PredecessorCounter PreviousCounter Predecessor Accumulate.Acc Vertex StateIndex LayerIndex
  VerticesTemplate LabelTmp Wedge.D Wedge.V Wedge.HC Wedge.DC Wedge.Aux GraphArray.Current





lemma laterCell_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n))
    (i : Fin (k-1)) (a : Fin k) (v : Fin n) (vt atail it vtail : List Item)
    (hCore : Core s ω arcs (i.val+1))
    (hV : s.G Vertex=.int (v.val : ℤ)::vt) (hA : s.G StateIndex=.int (a.val : ℤ)::atail)
    (hI : s.G LayerIndex=.int (i.val : ℤ)::it)
    (hCount : s.G PredecessorCounter=[]) (hPC : s.G PreviousCounter=[])
    (hvec : s.G Wedge.V=(labelBlock (signsOf ω) k v.val 0 k).reverse.map Item.int ++ vtail) :
    IRuns I Wedge.prog laterCell s
      ((s.upd StateIndex (.int ((a.val+1 : ℕ) : ℤ)::atail)).upd GraphArray.Current
        ((denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (i.val+2) v a).map Item.int ++ .mark::s.G GraphArray.Current))
      (laterCellCost n k arcs.length) := by
  let vs := (labelBlock (signsOf ω) k v.val 0 k).reverse
  let C := predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (i.val+1) i a v n 0
  let s0 := s.upd Accumulate.Acc (List.replicate (2^k) (.int 0) ++ .mark::s.G Accumulate.Acc)
  let s1 := s0.upd Predecessor (.int 0::s.G Predecessor)
  let s2 := s1.upd PredecessorCounter (List.replicate n .mark)
  let s3 := predecessorsState s2 ω arcs (i.val+1) i a v n (s.G Predecessor) (s.G Accumulate.Acc)
  let s4 := s3.upd Predecessor (s.G Predecessor)
  let s5 := (s4.upd Accumulate.Acc (s.G Accumulate.Acc)).upd GraphArray.Current
    ((wedgeReverse vs (coefficientList C)).map Item.int ++ .mark::s.G GraphArray.Current)
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
  have hCP : Core s2 ω arcs (i.val+1) :=
    ((hCore.upd Accumulate.Acc (by decide) _).upd Predecessor (by decide) _).upd PredecessorCounter (by decide) _
  have h3 : IRuns I Wedge.prog predecessors s2 s3
      ((predecessorVertexCost n k arcs.length+31)*n+30) := by
    exact predecessors_runs I s2 ω arcs (i.val+1) (by omega) i a v vt atail it (s.G Predecessor) (s.G Accumulate.Acc) hCP
      (by simp [s2,s1,s0,hV]) (by simp [s2,s1,s0,hA]) (by simp [s2,s1,s0,hI])
      (by simp [s2,s1,s0]) (by simp [s2]) (by simp [s2,s1,s0,hPC])
      (by simp [s2,s1,s0,predSum_zero,coefficientList_zero,List.map_replicate])
  have h4 : IExec I Wedge.prog (.op (.drop Predecessor)) s3 s4 (2*zsz (n : ℤ)+2) :=
    .op (.drop (by simp [s3,predecessorsState]))
  have hlen : vs.length=k := by simp [vs,labelBlock_decodes,labelList]
  have hsgn : ∀ x∈vs, x=1 ∨ x= -1 := by
    intro x hx
    have hh : x∈labelList (trialEquiv n k ω).1 v := by simpa [vs,labelBlock_decodes] using hx
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hh
    cases h : (trialEquiv n k ω).1 v r <;> simp [sgn,h]
  have h5 : IRuns I Wedge.prog GraphArray.laterArray s4 s5
      (1000000*(k+2)^2*(wordWidth n k+k+2)*2^k) := by
    have h := GraphArray.laterArray_runs I s4 vs (coefficientList C) (wordWidth n k)
      [] vtail (s.G Accumulate.Acc) (by simp [cls])
      (by simpa [s4,s3,predecessorsState,s2,s1,s0,hlen,coreStack,NS,Wedge.NS] using hCore.at 3 (by decide))
      (by simp [s4,s3,predecessorsState,s2,s1,s0,hvec,vs]) hsgn
      (by simp [s4,s3,predecessorsState,C])
      (by rw [coefficientList_length,hlen])
      (predSum_width arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (i.val+1) (by omega) i a v n 0)
      (by simpa [s4,s3,predecessorsState,s2,s1,s0,coreStack,NS,Wedge.NS] using hCore.at 10 (by decide))
      (by simpa [s4,s3,predecessorsState,s2,s1,s0,coreStack,NS,Wedge.NS] using hCore.at 11 (by decide))
      (by simpa [s4,s3,predecessorsState,s2,s1,s0,coreStack,NS,Wedge.NS] using hCore.at 12 (by decide))
    simpa [s5,s4,s3,predecessorsState,s2,s1,s0,hlen] using h
  have h6 : IRuns I Wedge.prog (liftClosed (Square.increment StateIndex)) s5 s6 (13000*(wordWidth n k+1)^2) :=
    liftClosed_runs I Wedge.prog (Square.increment_runs I StateIndex (by decide) s5 a.val (wordWidth n k) atail
      (by simp [s5,s4,s3,predecessorsState,s2,s1,s0,hA]) (wordWidth_pos n k) (row_word_width n k a.val (by omega)))
  have hpost : s6=(s.upd StateIndex (.int ((a.val+1 : ℕ) : ℤ)::atail)).upd GraphArray.Current
      ((denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (i.val+2) v a).map Item.int ++ .mark::s.G GraphArray.Current) := by
    have hwedge := later_array_decodes ω arcs i v a
    apply itemState_ext
    · intro r
      by_cases h80 : r=80
      · subst r; simp [s6,s5,s4,s3,predecessorsState,s2,s1,s0,IState.upd]
      by_cases h91 : r=91
      · subst r; simp [s6,s5,s4,s3,predecessorsState,s2,s1,s0,IState.upd,hCount]
      by_cases h20 : r=20
      · subst r; simp [s6,s5,s4,s3,predecessorsState,s2,s1,s0,IState.upd]
      by_cases h22 : r=22
      · subst r; simp [s6,s5,s4,s3,predecessorsState,s2,s1,s0,IState.upd,vs,C,hwedge,GraphArray.Current]
      by_cases h83 : r=83
      · subst r; simp [s6,s5,s4,s3,predecessorsState,s2,s1,s0,IState.upd]
      simp [s6,s5,s4,s3,predecessorsState,s2,s1,s0,IState.upd,Function.update_apply,h80,h91,h20,h22,h83]
    · rfl
    · rfl
  have h := Native.seq h0 (Native.seq (Native.of_exec h1) (Native.seq (Native.of_exec h2)
    (Native.seq h3 (Native.seq (Native.of_exec h4) (Native.seq h5 h6)))))
  rw [hpost] at h
  change IRuns I Wedge.prog laterCell s _ _ at h
  apply Native.mono h
  have hnW : zsz (n : ℤ)≤ wordWidth n k := by
    have hh := Controls.zsz_nat_le n
    unfold wordWidth; nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]
  have hpow : 1≤2^k := Nat.one_le_pow k 2 (by omega)
  have hbig : 2^k≤(k+2)^2*(wordWidth n k+k+2)*2^k := by
    have hb : 1≤(k+2)^2*(wordWidth n k+k+2) := Nat.succ_le_of_lt (by positivity)
    simpa only [one_mul] using Nat.mul_le_mul_right (2^k) hb
  unfold laterCellCost
  nlinarith

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n)))
  (i :
    Fin
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (a : Fin k) (v : Fin n) (vt atail it vtail : List.{0} NLogN.Item)
  (hCore :
    @KoanaKPaths.Machine.Trial.Core n k s ω arcs
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Fin.val
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          i)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hV :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val n v))) vt))
  (hA :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.StateIndex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val k a))) atail))
  (hI :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LayerIndex)
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@Fin.val
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              i)))
        it))
  (hCount :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PredecessorCounter)
      (@List.nil.{0} NLogN.Item))
  (hPC :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PreviousCounter)
      (@List.nil.{0} NLogN.Item))
  (hvec :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Wedge.V)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.reverse.{0} Int
            (KoanaKPaths.Machine.Trial.labelBlock (@KoanaKPaths.Machine.Trial.signsOf n k ω) k (@Fin.val n v)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)))
        vtail)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.laterCell s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.StateIndex
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@Nat.cast.{0} Int instNatCastInt
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val k a)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          atail))
      KoanaKPaths.Machine.GraphArray.Current
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@KoanaKPaths.Main.denseLayer n k k arcs
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
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Fin.val
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                i)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            v a))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark
          (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.GraphArray.Current))))
    (KoanaKPaths.Machine.Trial.laterCellCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs)) := by
  exact @KoanaKPaths.Machine.Trial.laterCell_runs
