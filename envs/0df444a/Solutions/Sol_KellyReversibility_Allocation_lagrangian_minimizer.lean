-- Prove2me | solution 1 for KellyReversibility.Allocation.lagrangian_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @techtao
-- created : 2026-10-05T03:43:21.546635+00:00
-- url     : https://prove2.me/submissions/239e8890-0a65-431a-9250-51995d0e22c9

import Definitions.Def_KellyReversibility_Allocation_CapacityAllocation
set_option autoImplicit false

-- Exact target: https://prove2.me/theorems/74078167-a525-456a-9d2d-7d25e7e3244c
-- Every helper is closed locally; no target theorem or open lemma is imported.


set_option autoImplicit false
open scoped BigOperators
open KellyReversibility.Allocation

namespace CapacityWork

private lemma scalar_minimum (a b s t : ℝ) (hb : 0 < b) (hs : 0 < s)
    (ht : 0 < t) (heq : b * s ^ 2 = a) :
    a / s + b * s ≤ a / t + b * t := by
  have hdiv : a / s = b * s := (div_eq_iff (ne_of_gt hs)).2 (by nlinarith [heq])
  have h : 2 * b * s - b * t ≤ a / t := by
    apply (le_div_iff₀ ht).2
    nlinarith [mul_nonneg (le_of_lt hb) (sq_nonneg (t - s))]
  rw [hdiv]
  linarith

private lemma scalar_minimum_strict (a b s t : ℝ) (hb : 0 < b) (hs : 0 < s)
    (ht : 0 < t) (heq : b * s ^ 2 = a) (hne : t ≠ s) :
    a / s + b * s < a / t + b * t := by
  have hdiv : a / s = b * s := (div_eq_iff (ne_of_gt hs)).2 (by nlinarith [heq])
  have h : 2 * b * s - b * t < a / t := by
    apply (lt_div_iff₀ ht).2
    have hp : 0 < b * (t - s) ^ 2 := mul_pos hb (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
    nlinarith
  rw [hdiv]
  linarith

theorem lagrangian_minimizer {J : ℕ} (a f : Fin J → ℝ) (F y : ℝ)
    (ha : ∀ j, 0 < a j) (hf : ∀ j, 0 < f j) (hy : 0 < y) :
    let φstar : Fin J → ℝ := fun j => a j + Real.sqrt (a j / (y * f j))
    (∀ j, a j < φstar j) ∧
      ∀ φ : Fin J → ℝ, (∀ j, a j < φ j) → φ ≠ φstar →
        lagrangian a f F y φstar < lagrangian a f F y φ := by
  dsimp only
  let s : Fin J → ℝ := fun j => Real.sqrt (a j / (y * f j))
  have hs (j : Fin J) : 0 < s j := Real.sqrt_pos.2 (div_pos (ha j) (mul_pos hy (hf j)))
  have heq (j : Fin J) : (y * f j) * (s j) ^ 2 = a j := by
    dsimp [s]
    rw [Real.sq_sqrt (le_of_lt (div_pos (ha j) (mul_pos hy (hf j))))]
    field_simp [ne_of_gt hy, ne_of_gt (hf j)]
  constructor
  · intro j
    exact lt_add_of_pos_right _ (hs j)
  · intro φ hφ hne
    have hex : ∃ j, φ j ≠ a j + s j := by
      by_contra! h
      exact hne (funext h)
    obtain ⟨j, hj⟩ := hex
    have hle (i : Fin J) :
        a i / s i + y * f i * (a i + s i) ≤ a i / (φ i - a i) + y * f i * φ i := by
      have h := scalar_minimum (a i) (y * f i) (s i) (φ i - a i)
        (mul_pos hy (hf i)) (hs i) (sub_pos.mpr (hφ i)) (heq i)
      nlinarith
    have hlt :
        a j / s j + y * f j * (a j + s j) < a j / (φ j - a j) + y * f j * φ j := by
      have h := scalar_minimum_strict (a j) (y * f j) (s j) (φ j - a j)
        (mul_pos hy (hf j)) (hs j) (sub_pos.mpr (hφ j)) (heq j)
        (by intro h; apply hj; linarith)
      nlinarith
    have hsum :
        (∑ i, (a i / s i + y * f i * (a i + s i))) <
        ∑ i, (a i / (φ i - a i) + y * f i * φ i) := by
      exact Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ j, hlt⟩
    simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hsum
    simp only [lagrangian, meanNumberInNetwork, add_sub_cancel_left]
    dsimp only [s] at hsum
    linarith

end CapacityWork

theorem solution {J : ℕ} (a f : Fin J → ℝ) (F y : ℝ)
    (ha : ∀ j, 0 < a j) (hf : ∀ j, 0 < f j) (hy : 0 < y) :
    let φstar : Fin J → ℝ := fun j => a j + Real.sqrt (a j / (y * f j))
    (∀ j, a j < φstar j) ∧
      ∀ φ : Fin J → ℝ, (∀ j, a j < φ j) → φ ≠ φstar →
        lagrangian a f F y φstar < lagrangian a f F y φ := by
  exact CapacityWork.lagrangian_minimizer a f F y ha hf hy

#print axioms solution
