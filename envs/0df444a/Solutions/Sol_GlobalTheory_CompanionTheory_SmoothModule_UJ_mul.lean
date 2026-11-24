-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.UJ_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:14.960294+00:00
-- url     : https://prove2.me/submissions/b95e7736-d16f-4b62-b58f-84b64d4752f2

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
theorem _root_.solution {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by
  have h1 : gᴴ * Jm ε * g = Jm ε := hg
  have h2 : hᴴ * Jm ε * h = Jm ε := hh
  change (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  calc (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, h2]
end GlobalTheory.CompanionTheory.SmoothModule
