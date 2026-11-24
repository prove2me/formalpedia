-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.glRel_of_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:23.393879+00:00
-- url     : https://prove2.me/submissions/d65d78bc-b9c5-4a94-843d-a738d679fe70

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (h : ∀ Y Z, C Y * C Z - C Z * C Y = C (Y * Z - Z * Y)) :
    Formalism.REAL.GlRel fun a b => C (single a b 1) := by
  intro a b c d
  have key : ∀ a b c d : Fin n, C (single a b 1 * single c d 1) = if b = c then C (single a d 1) else 0 := by
    intro a b c d
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, map_zero]
  rw [h, map_sub, key, key]
end GlobalTheory.CompanionTheory.SmoothModule
