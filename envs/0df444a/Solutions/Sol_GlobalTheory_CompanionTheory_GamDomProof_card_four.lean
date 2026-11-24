-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GamDomProof.card_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:09.51805+00:00
-- url     : https://prove2.me/submissions/41ab23e0-3964-4480-bb2f-d2a36e4d67bb

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
theorem _root_.solution (ε : Fin n → Bool) (a : Fin n) :
    ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) + (univ.filter fun b => b < a ∧ ε b = ε a).card
      + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card + 1 = n := by
  have h1 : (1 : ℝ) = ∑ b : Fin n, if b = a then (1 : ℝ) else 0 := by simp
  have h2 : (n : ℝ) = ∑ _b : Fin n, (1 : ℝ) := by simp
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [h2]
  nth_rewrite 5 [h1]
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · by_cases e : ε b = ε a <;> simp [h, h.not_gt, h.ne', e]
  · simp [h]
  · by_cases e : ε b = ε a <;> simp [h, h.not_gt, h.ne, e]
end GlobalTheory.CompanionTheory.GamDomProof
