-- Prove2me | solution 1 for GlobalTheory.CompleteHomogeneousBound.norm_le_of_completeHomogeneous_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:39:50.085124+00:00
-- url     : https://prove2.me/submissions/1987b1e2-2db7-4df1-9cf4-fc3679dc9d6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_WeightedSummable_mul
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_weightedSummable_linear
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_weightedSummable_prod
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_weightedSummable_geom_iff
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_geom_mul_linear
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_coeff_prod_geom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
open GlobalTheory GlobalTheory.CompleteHomogeneousBound
namespace GlobalTheory.CompleteHomogeneousBound
theorem _root_.solution (n : ℕ) (β : Fin n → ℂ) (c : Fin n → ℝ) (Q : ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hcQ : ∀ i, c i ≤ Q)
    (h : ∀ m : ℕ, ‖∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, β i ^ a i‖ ≤
      ∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, c i ^ a i) (i : Fin n) : ‖β i‖ ≤ Q := by
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ‖β i‖ := lt_of_le_of_lt ((hc0 i).trans (hcQ i)) hlt
  set r : ℝ := ‖β i‖⁻¹ with hr
  have hr0 : 0 < r := inv_pos.mpr hpos
  have hc : WeightedSummable r (∏ j, (mk fun k => ((c j : ℝ) : ℂ) ^ k : ℂ⟦X⟧)) := by
    refine weightedSummable_prod r _ _ fun j _ => ?_
    rw [weightedSummable_geom_iff, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (hc0 j), Real.norm_of_nonneg hr0.le, hr, ← div_eq_mul_inv,
      div_lt_one hpos]
    exact (hcQ j).trans_lt hlt
  have hβ : WeightedSummable r (∏ j, (mk fun k => β j ^ k : ℂ⟦X⟧)) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hc
    rw [norm_mul, norm_mul, coeff_prod_geom, coeff_prod_geom]
    refine mul_le_mul_of_nonneg_right ((h m).trans ?_) (norm_nonneg _)
    have : (∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ j, ((c j : ℝ) : ℂ) ^ a j) =
        ((∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ j, c j ^ a j : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.norm_real]
    exact le_abs_self _
  have hlin : WeightedSummable r (∏ j ∈ Finset.univ.erase i, (1 - C (β j) * X)) :=
    weightedSummable_prod r _ _ fun j _ => weightedSummable_linear r _
  have hm := hβ.mul hlin
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one (fun j _ => geom_mul_linear (β j)), mul_one, weightedSummable_geom_iff,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le, hr, mul_inv_cancel₀ hpos.ne'] at hm
  exact lt_irrefl _ hm
end GlobalTheory.CompleteHomogeneousBound
