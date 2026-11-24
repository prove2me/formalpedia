-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKoszul.number_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:11.976492+00:00
-- url     : https://prove2.me/submissions/39d4905c-0bbb-4c16-be31-cf39d38d3fff

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_cre_ann_apply
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
theorem _root_.solution (x : Ch ε Z) (A : Finset (NC ε)) :
    ((∑ i : NC ε, (cre i * ann i : Module.End ℂ (Ch ε Z))) x) A = (A.card : ℂ) • x A := by
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [Module.End.mul_apply, cre_ann_apply]
  rw [← Finset.sum_filter]
  simp [Nat.cast_smul_eq_nsmul]
end GlobalTheory.CompanionTheory.DSICKoszul
