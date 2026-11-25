-- Prove2me | solution 1 for GroundTheory.LocalField.oneAddValBallIndicator_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:13.873673+00:00
-- url     : https://prove2.me/submissions/fa902ec3-20ed-404b-b291-73e976cf8af2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_oneAddValBallIndicator_apply

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
namespace GroundTheory.LocalField
theorem _root_.solution (c : ℤ) (h : K) :
    oneAddValBallIndicator c (1 + h) = (valBall K c : Set K).indicator (fun _ => 1) h := by
  classical
  rw [oneAddValBallIndicator_apply, add_sub_cancel_left, Set.indicator_apply]
  rfl
end GroundTheory.LocalField
