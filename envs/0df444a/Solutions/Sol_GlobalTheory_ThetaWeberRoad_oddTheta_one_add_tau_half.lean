-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.oddTheta_one_add_tau_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:42:50.602275+00:00
-- url     : https://prove2.me/submissions/5d7c845a-49cb-4153-996d-7a61bdc8686a

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
    oddTheta τ ((1 + (τ : ℂ)) / 2) =
      -cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ := by
  have h : jacobiTheta₂ ((1 + (τ : ℂ)) / 2 + ((τ : ℂ) + 1) / 2) τ =
      cexp (-π * I * (τ : ℂ)) * jacobiTheta₂ 0 τ := by
    rw [show (1 + (τ : ℂ)) / 2 + ((τ : ℂ) + 1) / 2 = (0 + 1) + (τ : ℂ) by ring, jacobiTheta₂_add_left',
      jacobiTheta₂_add_left]
    congr 1
    rw [show -(π : ℂ) * I * ((τ : ℂ) + 2 * (0 + 1)) = -π * I * (τ : ℂ) - 2 * π * I by ring,
      Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_zero, neg_cexp]
  congr 2
  ring
end GlobalTheory.ThetaWeberRoad
