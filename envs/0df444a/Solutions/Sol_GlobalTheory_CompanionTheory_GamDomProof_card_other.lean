-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GamDomProof.card_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:11.411295+00:00
-- url     : https://prove2.me/submissions/b313a7d6-1ecb-4d7b-82f0-074a578d0aac

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CardOther
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
theorem _root_.solution (ε : Fin n → Bool) (a : Fin n) (h : ε a = true) :
    (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
      = nb ε false := by
  simp only [nb, card_filter, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h' | h' | h'
  · cases e : ε b <;> simp [h, h', h'.not_gt]
  · simp [← h', h]
  · cases e : ε b <;> simp [h, h', h'.not_gt]
end GlobalTheory.CompanionTheory.GamDomProof
