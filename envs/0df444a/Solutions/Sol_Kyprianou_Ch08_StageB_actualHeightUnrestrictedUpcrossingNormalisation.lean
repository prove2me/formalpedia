-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actualHeightUnrestrictedUpcrossingNormalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:28:51.473466+00:00
-- url     : https://prove2.me/submissions/fbdae6a8-8194-4702-a009-77e9056a6ea9

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_filtered_avram_upcrossing_discount_real_cap
import Theorems.Thm_Kyprianou_Ch08_StageB_original_unrestricted_upcrossing_discount_bound_zero_included
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount
import Theorems.Thm_kyprianou82_actualHeight_pos_raw
import Theorems.Thm_kyprianou82_actualHeight_zero_raw
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
  (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
  (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫ ω, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) = 1 := by
  by_cases hqpos : 0 < q
  · rw [integral_const_mul, kyprianou82_actualHeight_pos_raw P D ψ W hψ hW q hqpos, ← Real.exp_add]
    ring_nf
    simp
  · have hqzero : q = 0 := le_antisymm (le_of_not_gt hqpos) hq
    subst q
    rw [integral_const_mul, kyprianou82_actualHeight_zero_raw P D ψ W hψ hW, ← Real.exp_add]
    ring_nf
    simp
