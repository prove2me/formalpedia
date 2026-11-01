-- Prove2me | solution 1 for OAI.MetricKMedian.threshold
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:22:10.966606+00:00
-- url     : https://prove2.me/submissions/16b9a5f9-b4d4-40b3-9e27-59e69a78062b

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K027
import Definitions.Def_OAIQ053K041
import Theorems.Thm_OAI_MetricKMedian_approximationFactors_nonempty_s53
import Theorems.Thm_OAI_MetricKMedian_below_threshold_impossible_s53
import Theorems.Thm_OAI_MetricKMedian_factor_above_threshold_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Coverage
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.ProjectionInput.incident_equiv _root_.OAI.MetricKMedian.Instance.restrict_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

namespace Input

theorem client_injective (C : Input) : Function.Injective C.client := by
  intro i j h
  exact Sum.inl.inj (finSumFinEquiv.injective h)

theorem chosenFacilities_subset (C : Input) (S : Finset (Fin C.n)) :
    C.chosenFacilities S ⊆ C.toMedian.facilities :=
  image_subset_image (subset_univ S)

theorem nearest_chosen_ge_one (C : Input) (j : Fin C.m)
    (S : Finset (Fin C.n)) (hS : S.Nonempty) :
    1 ≤ nearest C.toMedian (C.client j) (C.chosenFacilities S) := by
  obtain ⟨x, hx, he⟩ := C.toMedian.nearest_attained (C.client j)
    (C.chosenFacilities S) ((C.chosenFacilities_nonempty S).mpr hS)
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  rw [he, C.distance_client_facility]
  split <;> norm_num

theorem nearest_chosen (C : Input) (j : Fin C.m)
    (S : Finset (Fin C.n)) (hS : S.Nonempty) :
    nearest C.toMedian (C.client j) (C.chosenFacilities S) =
      if j ∈ C.covered S then 1 else 3 := by
  split_ifs with hj
  · obtain ⟨i, hi, hji⟩ := (C.mem_covered S j).mp hj
    apply le_antisymm _ (C.nearest_chosen_ge_one j S hS)
    have h := C.toMedian.nearest_le (C.client j) (mem_image_of_mem C.facility hi)
    simpa only [chosenFacilities, C.distance_client_facility, hji, Bool.true_eq, ↓reduceIte,
      Rat.cast_one] using h
  · obtain ⟨x, hx, he⟩ := C.toMedian.nearest_attained (C.client j)
      (C.chosenFacilities S) ((C.chosenFacilities_nonempty S).mpr hS)
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have hji : C.incident j i ≠ true := fun h => hj ((C.mem_covered S j).mpr ⟨i, hi, h⟩)
    rw [he, C.distance_client_facility]
    simp [hji]

theorem cost_chosen (C : Input) (S : Finset (Fin C.n)) (hS : S.Nonempty) :
    cost C.toMedian (C.chosenFacilities S) =
      3 * (C.m : ℝ) - 2 * ((C.covered S).card : ℝ) := by
  unfold cost
  change (∑ j ∈ univ.image C.client,
    nearest C.toMedian j (C.chosenFacilities S)) = _
  rw [sum_image]
  · simp_rw [C.nearest_chosen _ S hS]
    calc
      ∑ j : Fin C.m, (if j ∈ C.covered S then (1 : ℝ) else 3) =
          ∑ j : Fin C.m, (3 - 2 * (if j ∈ C.covered S then (1 : ℝ) else 0)) := by
        apply sum_congr rfl
        intro j _
        split_ifs <;> norm_num
      _ = _ := by
        rw [sum_sub_distrib, ← mul_sum]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          sum_boole, filter_mem_eq_inter, univ_inter]
        ring
  · intro i _ j _ hij
    exact C.client_injective hij

theorem chosen_selected (C : Input) {T : Finset (Fin (C.m + C.n))}
    (hT : T ⊆ C.toMedian.facilities) : C.chosenFacilities (C.selected T) = T := by
  ext x
  simp only [chosenFacilities, selected, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    obtain ⟨i, _, hi⟩ := mem_image.mp (hT hx)
    exact ⟨i, hi ▸ hx, hi⟩

theorem cost_selected (C : Input) {T : Finset (Fin (C.m + C.n))}
    (hT : T ⊆ C.toMedian.facilities) (hne : T.Nonempty) :
    cost C.toMedian T = 3 * (C.m : ℝ) - 2 * ((C.covered (C.selected T)).card : ℝ) := by
  have he := C.chosen_selected hT
  have hs : (C.selected T).Nonempty := (C.chosenFacilities_nonempty _).mp (he.symm ▸ hne)
  simpa only [he] using C.cost_chosen (C.selected T) hs

theorem covered_card_le (C : Input) (S : Finset (Fin C.n)) :
    (C.covered S).card ≤ C.m := by
  simpa only [card_univ, Fintype.card_fin] using card_le_card (subset_univ (C.covered S))

theorem cost_ge_universe (C : Input) {T : Finset (Fin (C.m + C.n))}
    (hT : T ⊆ C.toMedian.facilities) (hne : T.Nonempty) :
    (C.m : ℝ) ≤ cost C.toMedian T := by
  rw [C.cost_selected hT hne]
  have h : ((C.covered (C.selected T)).card : ℝ) ≤ C.m := by
    exact_mod_cast C.covered_card_le (C.selected T)
  linarith

theorem perfect_nonempty (C : Input) {S : Finset (Fin C.n)}
    (h : C.covered S = univ) : S.Nonempty := by
  let j : Fin C.m := ⟨0, C.m_pos⟩
  have hj : j ∈ C.covered S := by rw [h]; exact mem_univ j
  obtain ⟨i, hi, _⟩ := (C.mem_covered S j).mp hj
  exact ⟨i, hi⟩

theorem optimum_of_perfect (C : Input) (h : C.Perfect) :
    optimum C.toMedian = C.m := by
  apply le_antisymm
  · obtain ⟨S, hk, hcover⟩ := h
    have hne := C.perfect_nonempty hcover
    have hb := C.toMedian.optimum_le (C.chosenFacilities_subset S)
      ((C.chosenFacilities_nonempty _).mpr hne) (by
        change (C.chosenFacilities S).card ≤ C.k
        simpa only [chosenFacilities_card] using hk)
    rw [C.cost_chosen S hne, hcover] at hb
    simp only [card_univ, Fintype.card_fin] at hb
    linarith
  · obtain ⟨T, hT, hne, _, he⟩ := C.toMedian.optimum_attained
    rw [← he]
    exact C.cost_ge_universe hT hne

end Input

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Analysis
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.ProjectionInput.incident_equiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian

private theorem unitCoverage_perfect : unitCoverage.Perfect := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · change (Finset.univ : Finset (Fin 1)).card ≤ 1
    simp
  · ext j
    rw [Coverage.Input.mem_covered]
    constructor
    · intro _; exact Finset.mem_univ j
    · intro _
      exact ⟨⟨0, Nat.zero_lt_one⟩, Finset.mem_univ _, rfl⟩

theorem factor_ge_one {α : ℝ} (hα : α ∈ approximationFactors) : 1 ≤ α := by
  obtain ⟨algorithm, _, hcorrect⟩ := hα
  obtain ⟨T, hT, hne, _, _, hcost⟩ := hcorrect unitCoverage.toMedian
  rw [unitCoverage.optimum_of_perfect unitCoverage_perfect] at hcost
  have hm : (unitCoverage.m : ℝ) = 1 := by norm_num [unitCoverage]
  rw [hm, mul_one] at hcost
  have hlow : (1 : ℝ) ≤ cost unitCoverage.toMedian T :=
    hm ▸ unitCoverage.cost_ge_universe hT hne
  exact hlow.trans hcost

theorem approximationFactors_bddBelow : BddBelow approximationFactors :=
  ⟨1, fun _ h => factor_ge_one h⟩

theorem infimum_le_threshold :
    sInf approximationFactors ≤ 1 + 2 / Real.exp 1 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact csInf_le approximationFactors_bddBelow (factor_above_threshold_s53 ε hε)

end MetricKMedian

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Threshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPThreshold
namespace MetricKMedian

theorem threshold_oai (h : Complexity.PNeNP) :
    sInf approximationFactors=1+2/Real.exp 1 := by
  apply le_antisymm infimum_le_threshold
  exact le_csInf approximationFactors_nonempty_s53 (below_threshold_impossible_s53 h)
end MetricKMedian

end Inline_PCPThreshold

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.threshold_oai := @OAI.MetricKMedian.threshold_oai
