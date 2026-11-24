-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.bracket_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:16.794665+00:00
-- url     : https://prove2.me/submissions/224f8eb3-637f-4cf8-941f-f7bb40c299f3

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
theorem _root_.solution {R : Type*} [Ring R] [Algebra ℂ R] (C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] R)
    (h : ∀ X Y, inG ε X → inG ε Y → C X * C Y - C Y * C X = C (X * Y - Y * X))
    (Y Z : Matrix (Fin n) (Fin n) ℂ) : C Y * C Z - C Z * C Y = C (Y * Z - Z * Y) := by
  rw [← re_add_im (ε := ε) Y, ← re_add_im (ε := ε) Z]
  have h1 := h _ _ (inG_re Y) (inG_re Z)
  have h2 := h _ _ (inG_re Y) (inG_im Z)
  have h3 := h _ _ (inG_im Y) (inG_re Z)
  have h4 := h _ _ (inG_im Y) (inG_im Z)
  simp only [map_sub, map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm] at *
  linear_combination (norm := module) h1 + Complex.I • h2 + Complex.I • h3 +
    Complex.I • Complex.I • h4
end GlobalTheory.CompanionTheory.SmoothModule
