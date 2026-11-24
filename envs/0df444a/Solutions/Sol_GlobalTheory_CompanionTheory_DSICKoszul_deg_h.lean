-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKoszul.deg_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:41.778802+00:00
-- url     : https://prove2.me/submissions/b69bd65b-0a74-4972-8fd5-3092fe944a98

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
theorem _root_.solution (d : NC ε → Module.End ℂ Z) (j : ℕ) (x : Ch ε Z) (hx : Deg j x) :
    Deg (j + 1) ((∑ i : NC ε, ((lift ε (d i) : Module.End ℂ (Ch ε Z)) * cre i : Module.End ℂ (Ch ε Z))) x) := by
  intro A hA
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : i ∈ A
  · have : x (A.erase i) = 0 := hx _ (by
      have := Finset.card_erase_add_one h
      omega)
    simp [cre, h, this]
  · simp [cre, h]
end GlobalTheory.CompanionTheory.DSICKoszul
