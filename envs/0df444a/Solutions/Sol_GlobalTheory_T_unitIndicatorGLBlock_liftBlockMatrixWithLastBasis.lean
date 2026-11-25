-- Prove2me | solution 1 for GlobalTheory.T.unitIndicatorGLBlock_liftBlockMatrixWithLastBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:29.16544+00:00
-- url     : https://prove2.me/submissions/c65022ad-7a40-49da-ba0d-6125fa08a099

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockLiftBlockMatrixWithLastBasisStatement
import Theorems.Thm_GlobalTheory_JR_UnitGLift_unitG_lift


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
theorem _root_.solution : ∀ (F : Type) [NormedField F] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ ≤ 1 → unitG (r + 1) F (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitG r F Z := by
  first | exact @GlobalTheory.JR.UnitGLift.unitG_lift | exact GlobalTheory.JR.UnitGLift.unitG_lift | (intros; apply GlobalTheory.JR.UnitGLift.unitG_lift <;> assumption)
end _root_.GlobalTheory.T
