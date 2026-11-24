-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICFRel.frel_of_car
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:38:42.988814+00:00
-- url     : https://prove2.me/submissions/1214eb68-3a07-4cb0-bf45-0c8e2300f16e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_gop_rel
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_lift_gop
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_lift_rel
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_add_rel
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_neg_rel
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
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICFRel
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSICFRel
theorem _root_.solution (h : CAR) : FRel := by
  intro n ε V _ _ E hE
  refine ⟨add_rel ε _ _ (lift_rel E hE) (gop_rel h ε V) fun a b c d => lift_gop _ c d, ?_⟩
  have := add_rel ε _ _ (lift_rel E hE) (neg_rel ε _ (gop_rel h ε V)) fun a b c d => (lift_gop _ d c).neg_right
  simp only [← sub_eq_add_neg] at this
  exact this
end GlobalTheory.CompanionTheory.DSICFRel
