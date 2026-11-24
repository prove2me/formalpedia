-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.qzero_scale_q_continuity_and_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T02:44:48.445594+00:00
-- url     : https://prove2.me/submissions/73de5d76-551d-4fa0-af81-c9691189f1c4

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_scale_discount_sequence_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_convolution_series
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_real_positive_x
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_series_entire
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_origin_discount_invariant
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_nonnegative_all_real
import Theorems.Thm_Kyprianou_Ch08_StageB_source_weighted_series_terms_pointwise_summable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Topology
open Kyprianou.Ch08.StageB
/-- Zero-discount continuity and discount monotonicity of the source scale family. -/
theorem solution :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ), HasSourceScaleFamily ψ W →
      (∀ z : ℝ, 0 ≤ z →
        Tendsto (fun n : ℕ => W (((n : ℝ) + 1)⁻¹) z) atTop (𝓝 (W 0 z))) ∧
      (∀ {r s z : ℝ}, 0 ≤ r → 0 ≤ s → r ≤ s → 0 ≤ z → W r z ≤ W s z) := by
  intro ψ W hW
  have hqseq_tendsto : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  have hrng : ∀ n : ℕ, 0 < (((n : ℝ) + 1)⁻¹) ∧ (((n : ℝ) + 1)⁻¹) ≤ 1 := by
    intro n
    constructor
    · positivity
    · have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        simpa using (add_le_add_right (Nat.cast_nonneg n) (1 : ℝ))
      simpa [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn)
  constructor
  · intro z hz
    exact p2m88_scale_discount_sequence_limit ψ W hW
      (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) hrng hqseq_tendsto z
  · intro r s z hr hs hrs hz
    by_cases hzpos : 0 < z
    · rw [source_scale_discount_series_real_positive_x ψ W hW z r hzpos hr]
      rw [source_scale_discount_series_real_positive_x ψ W hW z s hzpos hs]
      refine Summable.tsum_le_tsum ?_
        (by simpa using source_weighted_series_terms_pointwise_summable ψ W hW r 0 hr z)
        (by simpa using source_weighted_series_terms_pointwise_summable ψ W hW s 0 hs z)
      intro k
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hrs k)
        (source_scale_power_nonnegative_all_real ψ W hW k z)
    · have hz0 : z = 0 := le_antisymm (le_of_not_gt hzpos) hz; subst z
      rw [source_scale_origin_discount_invariant ψ W hW r hr]
      rw [source_scale_origin_discount_invariant ψ W hW s hs]
