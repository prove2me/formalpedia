-- Prove2me | solution 1 for GroundTheory.LocalField.haarIntegers_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:40:12.84758+00:00
-- url     : https://prove2.me/submissions/1f488884-72a3-427c-860c-4d842f30e5b0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_coe_valBall_zero

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
theorem _root_.solution : haarIntegers K (𝒪[K] : Set K) = 1 := by
  rw [← coe_valBall_zero]
  exact addHaarMeasure_self
end GroundTheory.LocalField
