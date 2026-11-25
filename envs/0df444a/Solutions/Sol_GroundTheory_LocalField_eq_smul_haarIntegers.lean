-- Prove2me | solution 1 for GroundTheory.LocalField.eq_smul_haarIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:41:24.117238+00:00
-- url     : https://prove2.me/submissions/e4058fff-8d14-4731-bf5a-e29b4cbc66ab

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
theorem _root_.solution (ν : Measure K) [ν.IsAddHaarMeasure] :
    ν = ν (𝒪[K] : Set K) • haarIntegers K := by
  have := addHaarMeasure_unique ν (integersPositiveCompacts K)
  rw [← coe_valBall_zero]
  exact this
end GroundTheory.LocalField
