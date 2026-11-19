-- Prove2me | solution 1 for KoanaKPaths.Main.denseLayer_correct
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.778345+00:00
-- url     : https://prove2.me/submissions/452204fb-d679-446e-8615-c0200f157214

import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
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















lemma coefficientList_add {k : ℕ} (A B : Coordinates k) :
    coefficientList (A+B) = List.zipWith (·+·) (coefficientList A) (coefficientList B) := by
  simp only [coefficientList,zipWith_same_map]
  rfl

lemma coefficientList_smul {k : ℕ} (z : ℤ) (A : Coordinates k) :
    coefficientList (z • A) = (coefficientList A).map (z*·) := by
  simp [coefficientList,List.map_map,Function.comp_def]

lemma coefficientList_zero (k : ℕ) : coefficientList (0 : Coordinates k) = List.replicate (2^k) 0 := by
  change (subsetOrder k).map (fun _ => (0 : ℤ)) = _
  simp [List.map_const,subsetOrder_length]

lemma lower_eq_empty {k : ℕ} (S : Finset (Fin k)) : lowerSet S = ∅ ↔ S=∅ := by
  simp [lowerSet]

lemma upper_ne_empty {k : ℕ} (S : Finset (Fin k)) : upperSet S ≠ ∅ := by
  simp [upperSet]

lemma coefficientList_unit (k : ℕ) : coefficientList (unit k) = 1::List.replicate (2^k-1) 0 := by
  induction k with
  | zero => simp [coefficientList,subsetOrder,unit]
  | succ k ih =>
    rw [coefficientList_split]
    have hl : (fun S : Finset (Fin k) => unit (k+1) (lowerSet S)) = unit k := by
      funext S
      simp [unit,lower_eq_empty]
    have hu : (fun S : Finset (Fin k) => unit (k+1) (upperSet S)) = (0 : Coordinates k) := by
      funext S
      simp [unit,upper_ne_empty]
    rw [hl,hu,ih,coefficientList_zero]
    simp only [List.cons_append,← List.replicate_add]
    congr 2
    rw [pow_succ]
    have hp : 0 < 2^k := by positivity
    omega

end KoanaKPaths.ExteriorCoordinates

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

lemma labelList_get {n k : ℕ} (σ : Labels n k) (v : Fin n) (r : Fin k) :
    (labelList σ v).getD r.val 0=sgn (σ v r) := by
  rw [List.getD_eq_getElem _ _ (by simpa [labelList] using r.isLt)]
  simp [labelList]

lemma sum_finRange {A : Type} [AddCommMonoid A] (n : ℕ) (f : Fin n→A) :
    ((List.finRange n).map f).sum=∑ i, f i := by
  rw [← List.sum_toFinset _ (List.nodup_finRange n),List.toFinset_finRange]

lemma sum_flatMap {α A : Type} [AddCommMonoid A] (xs : List α) (f : α→List A) :
    (xs.flatMap f).sum=((xs.map (fun x => (f x).sum)).sum) := by
  induction xs <;> simp_all

lemma denseLayer_correct {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (p : ℕ) (v : Fin n) (a : Fin ℓ) :
    denseLayer arcs σ R p v a=coefficientList (graphLayer arcs σ R p v a) := by
  induction p using Nat.twoStepInduction generalizing v a with
  | zero => simpa only [denseLayer,graphLayer] using (coefficientList_zero k).symm
  | one =>
    simp only [denseLayer]
    rw [← coefficientList_unit,wedgeList_correct]
    simp only [labelList_get]
    rw [← coefficientList_smul]
    rfl
  | more i ih0 ih =>
    simp only [denseLayer,graphLayer]
    split_ifs with hi
    · let weights : Fin n→Fin ℓ→ℤ := fun u b =>
        if (u,v)∈arcs.toFinset then sgn (R.2 ⟨i,hi⟩ a (b,v)) else 0
      let coords : List (Coordinates k) := (List.finRange n).flatMap (fun u =>
        (List.finRange ℓ).map (fun b => weights u b • graphLayer arcs σ R (i+1) u b))
      have hpred : ((List.finRange n).flatMap (fun u => (List.finRange ℓ).map (fun b =>
          (denseLayer arcs σ R (i+1) u b).map (fun x => weights u b*x)))) =
          coords.map coefficientList := by
        simp only [coords,List.map_flatMap,List.map_map,Function.comp_def,ih,coefficientList_smul]
      change wedgeList k (arraySum k _) (labelList σ v)=_
      rw [hpred,arraySum_coeff,wedgeList_correct]
      simp only [labelList_get]
      congr 1
      congr 1
      have hsum : coords.sum=∑ u : Fin n, if (u,v)∈arcs.toFinset then
          ∑ b : Fin ℓ, sgn (R.2 ⟨i,hi⟩ a (b,v)) • graphLayer arcs σ R (i+1) u b else 0 := by
        simp only [coords,sum_flatMap,List.map_map,Function.comp_def,sum_finRange]
        apply Finset.sum_congr rfl
        intro u _
        by_cases ha : (u,v)∈arcs <;> simp [weights,ha]
      exact hsum
    · exact (coefficientList_zero k).symm










end KoanaKPaths.Main

end

theorem solution :
∀ {n k ℓ : Nat} (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (σ : KoanaKPaths.Main.Labels n k)
  (R : KoanaKPaths.Main.SketchSigns n k ℓ) (p : Nat) (v : Fin n) (a : Fin ℓ),
  @Eq.{1} (List.{0} Int) (@KoanaKPaths.Main.denseLayer n k ℓ arcs σ R p v a)
    (@KoanaKPaths.ExteriorCoordinates.coefficientList k (@KoanaKPaths.Main.graphLayer n k ℓ arcs σ R p v a)) := by
  exact @KoanaKPaths.Main.denseLayer_correct
