-- Prove2me | solution 1 for GlobalTheory.T.jacquetRallisHankelDet_ne_zero_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:20:49.599566+00:00
-- url     : https://prove2.me/submissions/7993a23a-bbad-403e-89e1-b9c8416e8271

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLiftStatement
import Theorems.Thm_GlobalTheory_JR_Step_delta_lift_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (r : ℕ) (Z : Gl r k) (μ l : k), Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 := by
  first | exact @GlobalTheory.JR.Step.delta_lift_ne | exact GlobalTheory.JR.Step.delta_lift_ne | (intros; apply GlobalTheory.JR.Step.delta_lift_ne <;> assumption)
end _root_.GlobalTheory.T
