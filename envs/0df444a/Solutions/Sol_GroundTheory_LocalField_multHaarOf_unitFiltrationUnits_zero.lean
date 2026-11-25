-- Prove2me | solution 1 for GroundTheory.LocalField.multHaarOf_unitFiltrationUnits_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:48.208392+00:00
-- url     : https://prove2.me/submissions/90b3543c-d69b-461f-a399-5c74dc704acd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
import Theorems.Thm_GroundTheory_LocalField_multHaar_unitFiltrationUnits_zero


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
open ValuativeRel MeasureTheory Measure Topology
open scoped NNReal ENNReal
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution (μ : Measure K) [μ.IsAddHaarMeasure] :
    multHaarOf μ (unitFiltrationUnits K 0 : Set Kˣ) = μ (𝒪[K] : Set K) := by
  rw [multHaarOf_eq, Measure.smul_apply, multHaar_unitFiltrationUnits_zero, smul_eq_mul, mul_one]
end GroundTheory.LocalField
