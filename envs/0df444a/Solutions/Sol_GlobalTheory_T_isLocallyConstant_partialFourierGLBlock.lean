-- Prove2me | solution 1 for GlobalTheory.T.isLocallyConstant_partialFourierGLBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:18:16.592954+00:00
-- url     : https://prove2.me/submissions/1dcc2f08-03c1-4b9d-91b1-2bcc63a182a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantPartialFourierGLBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantPartialFourierGLBlockStatement
import Theorems.Thm_GlobalTheory_JR_fourG_isLocallyConstant_of_invariant


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) → IsLocallyConstant (fourG M ψ f') := by
  first | exact @GlobalTheory.JR.fourG_isLocallyConstant_of_invariant | exact GlobalTheory.JR.fourG_isLocallyConstant_of_invariant | (intros; apply GlobalTheory.JR.fourG_isLocallyConstant_of_invariant <;> assumption)
end _root_.GlobalTheory.T
