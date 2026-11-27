-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.oddTheta_tau_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:41:06.214813+00:00
-- url     : https://prove2.me/submissions/63b31aa2-8b67-4925-805a-8e46303a6b68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HalfPeriodDiffThetaFourthOfSigmaStarAddition
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_negI_mul_cexp
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_thetaConst_zero_one
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
    oddTheta τ ((τ : ℂ) / 2) =
      -I * cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ := by
  have h : jacobiTheta₂ ((τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2) τ =
      cexp (-π * I * ((τ : ℂ) + 2 * (1 / 2))) * jacobiTheta₂ (1 / 2) τ := by
    rw [show (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2 = 1 / 2 + (τ : ℂ) by ring, jacobiTheta₂_add_left']
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_one, negI_mul_cexp]
  congr 2
  ring
end GlobalTheory.ThetaWeberRoad
