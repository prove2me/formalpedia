-- Prove2me | solution 1 for GroundTheory.LocalField.lintegral_comp_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:39.385195+00:00
-- url     : https://prove2.me/submissions/c965b28f-7f6a-46d1-8b16-dac8929c8eff

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_modulus_ne_zero
import Theorems.Thm_GroundTheory_LocalField_map_mul_left_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable (μ : Measure K) [μ.IsAddHaarMeasure]
namespace GroundTheory.LocalField
theorem _root_.solution {a : K} (ha : a ≠ 0) (f : K → ℝ≥0∞) :
    ∫⁻ x, f (a * x) ∂μ = ((modulus a : ℝ≥0∞))⁻¹ * ∫⁻ x, f x ∂μ := by
  have he : MeasurableEmbedding (fun x : K => a * x) :=
    (Homeomorph.mulLeft₀ a ha).measurableEmbedding
  rw [← he.lintegral_map, map_mul_left_eq_smul μ ha, lintegral_smul_measure,
    ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv (modulus_ne_zero ha)]
end GroundTheory.LocalField
