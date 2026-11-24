-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZetaHighest.card_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:55:55.430902+00:00
-- url     : https://prove2.me/submissions/85581869-ac10-4864-ad79-32fa34651dc6

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkStrictMono
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZetaHighest
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.ZetaHighest
theorem _root_.solution (ε : Fin n → Bool) (c : Fin n) (hc : ε c = true) :
    ((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b ≠ ε c).card : ℝ)
      = nb ε false := by
  unfold nb
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b c with h | h | h
  · cases e : ε b <;> simp [h, not_lt.2 h.le, hc]
  · simp [h, hc]
  · cases e : ε b <;> simp [h, not_lt.2 h.le, hc]
end GlobalTheory.CompanionTheory.ZetaHighest
