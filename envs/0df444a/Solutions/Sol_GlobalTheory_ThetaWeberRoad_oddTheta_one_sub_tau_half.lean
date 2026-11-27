-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.oddTheta_one_sub_tau_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:40:05.50519+00:00
-- url     : https://prove2.me/submissions/a9d004c5-e9b1-41bb-9289-41b24f208413

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HalfPeriodDiffThetaFourthOfSigmaStarAddition
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_neg_cexp
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_thetaConst_zero_zero
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_oddTheta_eq_of

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
    oddTheta τ (1 / 2 - (τ : ℂ) / 2) =
      -cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ := by
  have h : jacobiTheta₂ (1 / 2 - (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2) τ = cexp 0 * jacobiTheta₂ 0 τ := by
    rw [show (1 : ℂ) / 2 - (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2 = 0 + 1 by ring, jacobiTheta₂_add_left,
      Complex.exp_zero, one_mul]
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_zero, neg_cexp]
  congr 2
  ring
end GlobalTheory.ThetaWeberRoad
