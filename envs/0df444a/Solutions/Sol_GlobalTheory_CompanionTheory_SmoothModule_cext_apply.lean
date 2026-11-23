-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothModule.cext_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:48.669604+00:00
-- url     : https://prove2.me/submissions/f3954f01-260b-4efc-bc1c-245a07239f12

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
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (d : Matrix (Fin n) (Fin n) ℂ → M)
    (hadd : ∀ X Y, inG ε X → inG ε Y → d (X + Y) = d X + d Y)
    (hsmul : ∀ (s : ℝ) X, inG ε X → d ((s : ℂ) • X) = (s : ℂ) • d X) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cext ε d hadd hsmul Y = d (re ε Y) + Complex.I • d (im ε Y) := rfl
end GlobalTheory.CompanionTheory.SmoothModule
