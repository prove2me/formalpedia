-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GamDomProof.gam_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:42.016297+00:00
-- url     : https://prove2.me/submissions/70f0611d-9eb5-4097-bc83-6ec153b0f17e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CardOther
import Theorems.Thm_GlobalTheory_CompanionTheory_GamDomProof_card_four
import Theorems.Thm_GlobalTheory_CompanionTheory_GamDomProof_card_fst
import Theorems.Thm_GlobalTheory_CompanionTheory_GamDomProof_card_snd
import Theorems.Thm_GlobalTheory_CompanionTheory_GamDomProof_card_other
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
open CompanionTheory.D.DSIC
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GamDomProof
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.GamDomProof
theorem _root_.solution (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    gam ε lam a = lam a - ((n : ℝ) - 1) / 2 + (univ.filter fun b => b < a ∧ ε b = ε a).card
      + (if ε a = true then (nb ε false : ℝ) else 0) := by
  have h4 := card_four ε a
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, wtA, Pi.add_apply, Pi.sub_apply,
    card_fst, card_snd]
  split_ifs with h
  · rw [← card_other ε a h]
    push_cast
    linarith
  · push_cast
    linarith
end GlobalTheory.CompanionTheory.GamDomProof
