-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.thetaConst_one_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:37:37.89928+00:00
-- url     : https://prove2.me/submissions/e1fd743f-b674-4497-9ad2-f3be8eadb2e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HalfPeriodDiffThetaFourthOfSigmaStarAddition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaWeberRoad
namespace GlobalTheory.ThetaWeberRoad
theorem _root_.solution (τ : UpperHalfPlane) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ =
      cexp ((π : ℂ) * I * (τ : ℂ) / 4) * jacobiTheta₂ ((τ : ℂ) / 2) τ := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst
  push_cast
  congr 2 <;> ring
end GlobalTheory.ThetaWeberRoad
