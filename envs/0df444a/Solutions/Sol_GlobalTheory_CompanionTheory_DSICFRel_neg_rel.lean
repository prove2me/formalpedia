-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICFRel.neg_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:26:21.314023+00:00
-- url     : https://prove2.me/submissions/a915cd40-0836-4ef0-a990-d6ad171995ed

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
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
theorem _root_.solution {A : Type} [Ring A] (ε : Fin n → Bool) (G : Fin n → Fin n → A) (hG : KRel ε G) :
    KRel ε (fun c d => -G d c) := by
  intro a b c d hab hcd
  have h := hG b a d c hab.symm hcd.symm
  simp only [neg_mul_neg]
  rw [h]
  simp only [eq_comm (a := a) (b := d), eq_comm (a := c) (b := b)]
  split_ifs <;> abel
end GlobalTheory.CompanionTheory.DSICFRel
