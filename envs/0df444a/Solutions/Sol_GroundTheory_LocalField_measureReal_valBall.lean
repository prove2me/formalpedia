-- Prove2me | solution 1 for GroundTheory.LocalField.measureReal_valBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:35:02.332815+00:00
-- url     : https://prove2.me/submissions/4e3732bd-b968-4ed5-8f2a-bb290ccad332

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_measure_valBall

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
theorem _root_.solution (n : ℤ) :
    μ.real (valBall K n) = (residueCard K : ℝ) ^ (-n) * μ.real (valBall K 0) := by
  rw [measureReal_def, measureReal_def, measure_valBall μ n, ENNReal.toReal_mul,
    ENNReal.coe_toReal, NNReal.coe_zpow, NNReal.coe_natCast]
end GroundTheory.LocalField
