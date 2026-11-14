-- Prove2me | solution 1 for NarrowDNF.BourgainDuality.dual_fourth_contraction
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:18:51.161139+00:00
-- url     : https://prove2.me/submissions/116db23d-6a0c-4e12-a4b7-5a5119edbe13

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



private theorem dual43_pair (t : ℝ) : t * dual43 t = |t| ^ (4/3 : ℝ) := by
  have h : |t| * |t| ^ (1/3 : ℝ) = |t| ^ (4/3 : ℝ) := by
    calc
      _ = |t| ^ (1 : ℝ) * |t| ^ (1/3 : ℝ) := by rw [Real.rpow_one]
      _ = |t| ^ ((1 : ℝ) + 1/3) :=
        (Real.rpow_add' (abs_nonneg t) (by norm_num)).symm
      _ = _ := by norm_num
  by_cases ht : 0 ≤ t
  · simpa [dual43, ht, abs_of_nonneg ht] using h
  · have ht' : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    simp only [dual43, if_neg ht]
    simpa only [abs_of_nonpos ht', neg_mul, mul_neg, neg_neg] using h

private theorem dual43_fourth (t : ℝ) : dual43 t ^ 4 = |t| ^ (4/3 : ℝ) := by
  unfold dual43
  split_ifs
  · rw [← Real.rpow_mul_natCast (abs_nonneg t)]
    norm_num
  · rw [neg_pow]
    norm_num only
    rw [← Real.rpow_mul_natCast (abs_nonneg t)]
    norm_num





end NarrowDNF.BourgainDuality

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainDuality
variable {α : Type*} [Fintype α]
/-- L4 contraction of a self-adjoint finite operator implies L(4/3) contraction.
No dual norm theorem or infinite-dimensional functional analysis is assumed. -/
theorem solution (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (T : (α → ℝ) → α → ℝ)
    (hself : ∀ f g, (∑ x, w x * T f x * g x) = ∑ x, w x * f x * T g x)
    (hfourth : ∀ f, (∑ x, w x * T f x ^ 4) ≤ ∑ x, w x * f x ^ 4)
    (f : α → ℝ) : moment43 w (T f) ≤ moment43 w f := by
  let g := fun x => dual43 (T f x)
  let L := moment43 w (T f)
  have hL0 : 0 ≤ L := moment43_nonneg _ _ hw
  have hA0 := moment43_nonneg w f hw
  have hpair : (∑ x, w x * T f x * g x) = L := by
    simp only [g, L, moment43, mul_assoc, dual43_pair]
  have hg : (∑ x, w x * g x ^ 4) = L := by
    simp only [g, L, moment43, dual43_fourth]
  have h := weighted_holder43_fourth w f (T g) hw
  rw [← hself f g, hpair] at h
  have hTg := hfourth g
  rw [hg] at hTg
  have hbound : L ^ 4 ≤ moment43 w f ^ 3 * L :=
    h.trans (mul_le_mul_of_nonneg_left hTg (pow_nonneg hA0 _))
  by_cases hL : L = 0
  · simpa only [← hL] using hA0
  · have hLp : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
    have hcube : L ^ 3 ≤ moment43 w f ^ 3 := by
      apply (mul_le_mul_iff_left₀ hLp).mp
      nlinarith [hbound]
    exact le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) hA0 hcube
