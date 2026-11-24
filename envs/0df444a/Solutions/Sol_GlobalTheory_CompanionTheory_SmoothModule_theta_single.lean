-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.theta_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:26.112924+00:00
-- url     : https://prove2.me/submissions/cf3a0b3d-9077-44d9-a093-f3dc9df0c120

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep (IsURepOn UJset inG)
open PI.DSInfCharCap (dsigC thetaJ)
open PI.PhMeasCore (dsig smoothVecs)
open Formalism.REAL (Jm)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothModule
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.SmoothModule
theorem _root_.solution (a b : Fin n) :
    thetaJ ε (single a b 1) = (-(Formalism.REAL.sgn ε a b : ℂ)) • single b a 1 := by
  ext i j
  simp only [thetaJ, Jm, conjTranspose_single, Matrix.neg_apply, mul_diagonal, diagonal_mul, Matrix.smul_apply,
    Formalism.REAL.sgn, single_apply]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ε a <;> cases ε b <;> simp
  · simp [h]
end GlobalTheory.CompanionTheory.SmoothModule
