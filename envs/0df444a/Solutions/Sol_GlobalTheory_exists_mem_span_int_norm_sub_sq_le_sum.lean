-- Prove2me | solution 1 for GlobalTheory.exists_mem_span_int_norm_sub_sq_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:46.754043+00:00
-- url     : https://prove2.me/submissions/7029bda8-48c9-421d-82cc-2abcbd7ad0c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Theorems.Thm_GlobalTheory_exists_add_orthogonal_norm_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} (v : ι → E) (s : Finset ι) {x : E}
    (hx : x ∈ span ℝ (v '' s)) :
    ∃ w ∈ span ℤ (v '' s), ‖x - w‖ ^ 2 ≤ (1 / 4) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
    refine ⟨0, zero_mem _, ?_⟩
    have : x = 0 := by simpa using hx
    simp [this]
  | insert a s ha ih =>
    rw [Finset.coe_insert, Set.image_insert_eq] at hx ⊢
    obtain ⟨t, y, hy, rfl⟩ := mem_span_insert.1 hx
    obtain ⟨p, hp, q, hq, hv, hle⟩ := exists_add_orthogonal_norm_sq_le (span ℝ (v '' s)) (v a)
    have hy' : y + (t - round t) • p ∈ span ℝ (v '' s) := add_mem hy (smul_mem _ _ hp)
    obtain ⟨w, hw, hwle⟩ := ih hy'
    have hwR : w ∈ span ℝ (v '' s) := span_subset_span ℤ ℝ _ hw
    refine ⟨round t • v a + w, mem_span_insert.2 ⟨_, _, hw, rfl⟩, ?_⟩
    have he : t • v a + y - (round t • v a + w) =
        (y + (t - round t) • p - w) + (t - round t) • q := by
      rw [← Int.cast_smul_eq_zsmul ℝ, hv]; module
    rw [he, norm_add_sq_real,
      Submodule.inner_right_of_mem_orthogonal (sub_mem hy' hwR) (smul_mem _ _ hq),
      Finset.sum_insert ha, norm_smul, mul_pow, Real.norm_eq_abs]
    have h1 : |t - round t| ^ 2 ≤ 1 / 4 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (abs_sub_round t) 2
      linarith
    nlinarith [mul_le_mul h1 hle (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)]
end GlobalTheory
