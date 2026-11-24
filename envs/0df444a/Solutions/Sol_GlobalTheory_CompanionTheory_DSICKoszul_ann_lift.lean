-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKoszul.ann_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:26:28.262513+00:00
-- url     : https://prove2.me/submissions/1115666d-c553-4a25-829a-e83ea94e0e33

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
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
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKoszul
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {Z : Type} [AddCommGroup Z] [Module ℂ Z]
namespace GlobalTheory.CompanionTheory.DSICKoszul
theorem _root_.solution (i : NC ε) (T : Module.End ℂ Z) :
    Commute (ann i : Module.End ℂ (Ch ε Z)) (lift ε T) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  by_cases h : i ∈ A <;> simp [ann, h]
end GlobalTheory.CompanionTheory.DSICKoszul
