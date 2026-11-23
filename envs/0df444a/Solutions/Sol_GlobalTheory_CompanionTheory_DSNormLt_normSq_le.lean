-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSNormLt.normSq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:36.337536+00:00
-- url     : https://prove2.me/submissions/c591fb2b-da8f-41d7-b8c8-f4e798caeefa

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_sig_anti
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_sig_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_pair_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_term_le
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSNormLt
theorem _root_.solution (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (h1 : ∀ a b, |t a b| ≤ 1) :
    ∑ a, ((∑ b, t a b) / 2) ^ 2 ≤ ∑ a : Fin n, ((∑ b, sig a b) / 2) ^ 2 := by
  set x : Fin n → ℝ := fun a => (∑ b, t a b) / 2 with hx
  set r : Fin n → ℝ := fun a => (∑ b, sig a b) / 2 with hr
  let τ : Equiv.Perm (Fin n) := Tuple.sort (fun a => - x a)
  have hτ : Antitone (fun a => x (τ a)) := by
    intro a b hab
    have := Tuple.monotone_sort (fun a => - x a) hab
    simpa using this
  have e1 : 4 * ∑ a, x a ^ 2 ≤ 4 * ∑ a, x (τ a) * r a := by
    have := pair_eq t ht x
    have h2 := pair_eq sig sig_anti (fun a => x (τ a))
    calc 4 * ∑ a, x a ^ 2 = ∑ a, ∑ b, t a b * (x a - x b) := by
          rw [← this]; simp only [hx, sq]
      _ ≤ ∑ a, ∑ b, |x a - x b| :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => term_le (h1 a b)
      _ = ∑ a, ∑ b, |x (τ a) - x (τ b)| := by
          rw [← Equiv.sum_comp τ]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Equiv.sum_comp τ]
      _ = ∑ a, ∑ b, sig a b * (x (τ a) - x (τ b)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (sig_mul hτ a b).symm
      _ = _ := h2.symm
  have e2 : 2 * ∑ a, x (τ a) * r a ≤ ∑ a, x (τ a) ^ 2 + ∑ a, r a ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ => by nlinarith [sq_nonneg (x (τ a) - r a)]
  have e3 : ∑ a, x (τ a) ^ 2 = ∑ a, x a ^ 2 := Equiv.sum_comp τ (fun a => x a ^ 2)
  show ∑ a, x a ^ 2 ≤ ∑ a, r a ^ 2
  linarith
end GlobalTheory.CompanionTheory.DSNormLt
