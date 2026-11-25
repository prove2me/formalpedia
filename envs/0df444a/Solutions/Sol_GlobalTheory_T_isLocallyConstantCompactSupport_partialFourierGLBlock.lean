-- Prove2me | solution 1 for GlobalTheory.T.isLocallyConstantCompactSupport_partialFourierGLBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:23:11.624776+00:00
-- url     : https://prove2.me/submissions/a602db6f-d369-463b-ac7b-447fec314418

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportPartialFourierGLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportPartialFourierGLBStatement
import Theorems.Thm_GlobalTheory_JR_fourG_isTest


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → IsTest (fourG M ψ f') := by
  first | exact @GlobalTheory.JR.fourG_isTest | exact GlobalTheory.JR.fourG_isTest | (intros; apply GlobalTheory.JR.fourG_isTest <;> assumption)
end _root_.GlobalTheory.T
