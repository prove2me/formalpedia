-- Prove2me | solution 1 for GroundTheory.LocalField.haarIntegers_valBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:14.255408+00:00
-- url     : https://prove2.me/submissions/428c094a-088a-487b-ad2c-1ad93dbdbf82

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_coe_valBall_zero
import Theorems.Thm_GroundTheory_LocalField_measure_valBall
import Theorems.Thm_GroundTheory_LocalField_haarIntegers_integers

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
    haarIntegers K (valBall K n) = ((residueCard K : ℝ≥0) ^ (-n) : ℝ≥0) := by
  rw [measure_valBall (haarIntegers K), coe_valBall_zero, haarIntegers_integers, mul_one]
end GroundTheory.LocalField
