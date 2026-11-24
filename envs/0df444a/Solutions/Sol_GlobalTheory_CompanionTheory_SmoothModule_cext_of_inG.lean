-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.cext_of_inG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:17.758687+00:00
-- url     : https://prove2.me/submissions/1bb86008-9bd8-4d87-ba90-0488494928f9

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_cext_apply
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
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (d : Matrix (Fin n) (Fin n) ℂ → M)
    (hadd : ∀ X Y, inG ε X → inG ε Y → d (X + Y) = d X + d Y)
    (hsmul : ∀ (s : ℝ) X, inG ε X → d ((s : ℂ) • X) = (s : ℂ) • d X) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) : cext ε d hadd hsmul X = d X := by
  have h0 : d 0 = 0 := by simpa using hsmul 0 X hX
  have h1 : re ε X = X := by rw [re, inG_iff.1 hX]; module
  have h2 : im ε X = 0 := by rw [im, inG_iff.1 hX, sub_self, smul_zero]
  rw [cext_apply, h1, h2, h0, smul_zero, add_zero]
end GlobalTheory.CompanionTheory.SmoothModule
