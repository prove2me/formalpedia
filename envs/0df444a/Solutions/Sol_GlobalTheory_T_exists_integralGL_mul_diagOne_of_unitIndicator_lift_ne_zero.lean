-- Prove2me | solution 1 for GlobalTheory.T.exists_integralGL_mul_diagOne_of_unitIndicator_lift_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:16:55.171162+00:00
-- url     : https://prove2.me/submissions/b3835aa7-46e0-4f23-a488-9bfe1958fdf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralGLMulDiagOneOfUnitIndicatorLiftNeZ
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormSubLeMaxUltra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralGLMulDiagOneOfUnitIndicatorLiftNeZStatement
import Theorems.Thm_GlobalTheory_JR_GLift_support_lift


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 → ∀ g : GL (Fin (r + 1)) F, unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → ∃ k ∈ glO (r + 1) F, ∃ s : GL (Fin r) F, g = k * GlobalTheory.JR.Step.emb r F s := by
  first | exact @GlobalTheory.JR.GLift.support_lift | exact GlobalTheory.JR.GLift.support_lift | (intros; apply GlobalTheory.JR.GLift.support_lift <;> assumption)
end _root_.GlobalTheory.T
