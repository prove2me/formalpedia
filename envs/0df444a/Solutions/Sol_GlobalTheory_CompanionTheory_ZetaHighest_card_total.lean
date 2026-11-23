-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZetaHighest.card_total
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:01.994871+00:00
-- url     : https://prove2.me/submissions/6957d676-35f3-4ad0-ad84-52949a1645a4

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
theorem _root_.solution (ε : Fin n → Bool) (c : Fin n) :
    ((univ.filter fun b => c < b ∧ ε b = ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b = ε c).card : ℝ) +
      ((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b ≠ ε c).card : ℝ) + 1
      = n := by
  have h1 : (1 : ℝ) = ∑ b : Fin n, if b = c then 1 else 0 := by simp
  have h2 : (n : ℝ) = ∑ _b : Fin n, (1 : ℝ) := by simp
  rw [h2]
  conv_lhs => rw [h1]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b c with h | h | h
  · by_cases e : ε b = ε c <;> simp [h, h.ne, not_lt.2 h.le, e]
  · simp [h]
  · by_cases e : ε b = ε c <;> simp [h, h.ne', not_lt.2 h.le, e]
end GlobalTheory.CompanionTheory.ZetaHighest
