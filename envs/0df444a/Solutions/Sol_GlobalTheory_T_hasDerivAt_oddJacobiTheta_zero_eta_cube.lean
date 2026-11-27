-- Prove2me | solution 1 for GlobalTheory.T.hasDerivAt_oddJacobiTheta_zero_eta_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:43:36.984574+00:00
-- url     : https://prove2.me/submissions/35495906-f1cc-40e2-b8b1-8cdfb88872fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HasDerivAtOddJacobiThetaZeroEtaCube
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HasDerivAtOddJacobiThetaZeroEtaCubeStatement
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_OddDeriv_hasDerivAt_oddTheta_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.ThetaWeberRoad.TripleProduct → ∀ τ : UpperHalfPlane, HasDerivAt (GlobalTheory.ThetaWeberRoad.oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0 := by
  first | exact @GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero | exact GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero | (intros; apply GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero <;> assumption)
end _root_.GlobalTheory.T
