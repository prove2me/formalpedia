-- Prove2me | solution 1 for GroundTheory.LocalField.lintegral_multHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:49:11.956503+00:00
-- url     : https://prove2.me/submissions/fa9d9e0c-aa93-48e6-947b-6fc712f3fc55

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Definitions.Def_GroundTheory_LocalFields_LocalFourier

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
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution {g : K → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ u, g u ∂(multHaar K) =
      multHaarConst K * ∫⁻ x in {0}ᶜ, ((modulus x : ℝ≥0∞))⁻¹ * g x ∂(haarIntegers K) := by
  rw [← measurableEmbedding_units_val.lintegral_map, multHaar,
    measurableEmbedding_units_val.map_comap, range_units_val, Measure.restrict_smul,
    lintegral_smul_measure, smul_eq_mul,
    setLIntegral_withDensity_eq_setLIntegral_mul _ measurable_modulus_inv hg
      (measurableSet_singleton 0).compl]
  rfl
end GroundTheory.LocalField
