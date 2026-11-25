-- Prove2me | solution 1 for GroundTheory.LocalField.oneAddValBallIndicator_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:14.165151+00:00
-- url     : https://prove2.me/submissions/bcced0a7-a685-4db7-8dc2-a4aede44fb13

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon

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
omit [MeasurableSpace K] [BorelSpace K]
open Classical
namespace GroundTheory.LocalField
theorem _root_.solution (c : ℤ) (x : K) :
    oneAddValBallIndicator c x = if x - 1 ∈ valBall K c then 1 else 0 := by
  unfold oneAddValBallIndicator
  by_cases hx : x - 1 ∈ valBall K c
  · rw [Set.indicator_of_mem (show x ∈ {x : K | x - 1 ∈ valBall K c} from hx), if_pos hx]
  · rw [Set.indicator_of_notMem (show x ∉ {x : K | x - 1 ∈ valBall K c} from hx), if_neg hx]
end GroundTheory.LocalField
