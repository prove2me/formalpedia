-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.oddTheta_half_add_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:39:53.429821+00:00
-- url     : https://prove2.me/submissions/84e4d25d-c39b-4585-896f-7f146c56529c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HalfPeriodDiffThetaFourthOfSigmaStarAddition
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_neg_cexp
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_thetaConst_one_zero
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
    oddTheta τ (1 / 2 + (τ : ℂ)) =
      -(cexp (-((π : ℂ) * I * (τ : ℂ))) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ) := by
  have h : jacobiTheta₂ (1 / 2 + (τ : ℂ) + ((τ : ℂ) + 1) / 2) τ =
      cexp (-π * I * ((τ : ℂ) + 2 * ((τ : ℂ) / 2))) * jacobiTheta₂ ((τ : ℂ) / 2) τ := by
    rw [show 1 / 2 + (τ : ℂ) + ((τ : ℂ) + 1) / 2 = ((τ : ℂ) / 2 + (τ : ℂ)) + 1 by ring,
      jacobiTheta₂_add_left, jacobiTheta₂_add_left']
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_one_zero, ← mul_assoc, ← Complex.exp_add, ← neg_mul, neg_cexp]
  congr 2
  ring
end GlobalTheory.ThetaWeberRoad
