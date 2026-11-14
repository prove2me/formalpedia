-- Prove2me | solution 1 for NarrowDNF.BourgainDuality.dual_contract24
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:18:28.818239+00:00
-- url     : https://prove2.me/submissions/7f317978-5f65-4dea-8192-3873cbe00054

import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_NarrowDNF_BourgainDuality
import Theorems.Thm_NarrowDNF_BourgainDuality_weighted_holder43

namespace NarrowDNF.BourgainDuality
end NarrowDNF.BourgainDuality

section


/-!
# Finite fourth-moment duality

Weighted Hölder and finite self-adjoint operator duality used by the Bourgain
square-function proof. Every weight is explicit; zero weights are allowed.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainDuality

variable {α : Type*} [Fintype α]



private theorem moment43_nonneg (w f : α → ℝ) (hw : ∀ x, 0 ≤ w x) : 0 ≤ moment43 w f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (Real.rpow_nonneg (abs_nonneg _) _)



/-- The fourth-power form of Hölder avoids fractional powers in operator
contraction and cancellation arguments. -/
private theorem weighted_holder43_fourth (w f g : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, w x * f x * g x)^4 ≤ moment43 w f ^ 3 * ∑ x, w x * g x ^ 4 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (weighted_holder43 w f g hw) 4
  have hf0 := moment43_nonneg w f hw
  have hg0 : 0 ≤ ∑ x, w x * g x ^ 4 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (by positivity)
  rw [← abs_pow, abs_of_nonneg (by positivity), mul_pow,
    ← Real.rpow_mul_natCast hf0, ← Real.rpow_mul_natCast hg0] at h
  norm_num at h
  exact h











end NarrowDNF.BourgainDuality

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainDuality
variable {α : Type*} [Fintype α]
/-- Dual form of an L2-to-L4 contraction, in polynomial moment form. -/
theorem solution (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (T : (α → ℝ) → α → ℝ)
    (hself : ∀ f g, (∑ x, w x * T f x * g x) = ∑ x, w x * f x * T g x)
    (h24 : ∀ f, (∑ x, w x * T f x ^ 4) ≤ (∑ x, w x * f x ^ 2)^2)
    (f : α → ℝ) :
    (∑ x, w x * T f x ^ 2)^2 ≤ moment43 w f ^ 3 := by
  let L := ∑ x, w x * T f x ^ 2
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)
  have hA0 := moment43_nonneg w f hw
  have hpair : (∑ x, w x * T f x * T f x) = L := by
    simp only [L, pow_two, mul_assoc]
  have h := weighted_holder43_fourth w f (T (T f)) hw
  rw [← hself f (T f), hpair] at h
  have hbound : L ^ 4 ≤ moment43 w f ^ 3 * L^2 :=
    h.trans (mul_le_mul_of_nonneg_left (h24 (T f)) (pow_nonneg hA0 _))
  by_cases hL : L = 0
  · change L^2 ≤ _
    rw [hL]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using pow_nonneg hA0 3
  · have hLp : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hLp)).mp
    nlinarith [hbound]
