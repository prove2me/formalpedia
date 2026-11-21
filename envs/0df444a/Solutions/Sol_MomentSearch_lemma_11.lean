-- Prove2me | solution 1 for MomentSearch.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T22:43:14.971181+00:00
-- url     : https://prove2.me/submissions/3a5052ca-33f9-4344-b24e-cae3883a9b8c

import Mathlib
import Definitions.Def_MomentSearch_moment
import Definitions.Def_MomentSearch_SolvesCorrection

open scoped BigOperators
open MomentSearch

private lemma affine_vanishing {n : ℕ} (x : Fin n → ℝ) (c d : ℝ)
    (i : ℕ) (a : Fin n → ℝ)
    (h : ∀ j : ℕ, j ≤ i → ∑ t : Fin n, a t * x t ^ j = 0) :
    ∑ t : Fin n, a t * (c * x t + d) ^ i = 0 := by
  induction i generalizing a with
  | zero => simpa using h 0 (by omega)
  | succ i ih =>
    have h₀ := ih a (fun j hj => h j (Nat.le_trans hj (Nat.le_succ i)))
    have h₁ := ih (fun t => a t * x t) (by
      intro j hj
      simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
        h (j + 1) (Nat.succ_le_succ hj))
    calc
      ∑ t : Fin n, a t * (c * x t + d) ^ (i + 1) =
          c * (∑ t : Fin n, (a t * x t) * (c * x t + d) ^ i) +
          d * (∑ t : Fin n, a t * (c * x t + d) ^ i) := by
            simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro t _
            ring
      _ = 0 := by rw [h₀, h₁]; ring

private theorem affine_moment_equivalence {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (∀ a : Fin n → ℝ,
      (∀ i : ℕ, i ≤ k → ∑ t : Fin n, a t * ((t : ℕ) : ℝ) ^ i = 0) ↔
        (∀ i : ℕ, i ≤ k → ∑ t : Fin n, a t * grid n (t : ℕ) ^ i = 0)) ∧
    (∀ p p' : Fin n → ℝ, p ∈ stdSimplex ℝ (Fin n) → p' ∈ stdSimplex ℝ (Fin n) →
      ((∀ i : ℕ, i ≤ k → moment p i = moment p' i) ↔
        (∀ i : ℕ, i ≤ k →
          ∑ t : Fin n, p t * grid n (t : ℕ) ^ i = ∑ t : Fin n, p' t * grid n (t : ℕ) ^ i))) := by
  have hn' : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have equivalence : ∀ a : Fin n → ℝ,
      (∀ i : ℕ, i ≤ k → ∑ t : Fin n, a t * ((t : ℕ) : ℝ) ^ i = 0) ↔
      (∀ i : ℕ, i ≤ k → ∑ t : Fin n, a t * grid n (t : ℕ) ^ i = 0) := by
    intro a
    constructor
    · intro h i hi
      have h' := affine_vanishing (fun t : Fin n => ((t : ℕ) : ℝ))
        (2 / ((n : ℝ) - 1)) (-1) i a
        (fun j hj => h j (Nat.le_trans hj hi))
      simpa only [grid, div_eq_mul_inv, sub_eq_add_neg, mul_assoc,
        mul_left_comm, mul_comm] using h'
    · intro h i hi
      have h' := affine_vanishing (fun t : Fin n => grid n (t : ℕ))
        (((n : ℝ) - 1) / 2) (((n : ℝ) - 1) / 2) i a
        (fun j hj => h j (Nat.le_trans hj hi))
      have inverse (t : Fin n) :
          (((n : ℝ) - 1) / 2) * grid n (t : ℕ) +
            (((n : ℝ) - 1) / 2) = ((t : ℕ) : ℝ) := by
        dsimp [grid]
        field_simp [hn']
        ring
      simpa only [inverse] using h'
  refine ⟨equivalence, ?_⟩
  intro p p' _ _
  simpa only [moment, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using
    equivalence (fun t => p t - p' t)

theorem solution {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (m m₀ : Fin n) (a : Fin n → ℝ)
    (ha : SolvesCorrection n k m m₀ a) :
    ∃ p p' : Fin n → ℝ, p ∈ stdSimplex ℝ (Fin n) ∧ p' ∈ stdSimplex ℝ (Fin n) ∧
      (∀ i : ℕ, i ≤ k → moment p i = moment p' i) ∧
      1 - (1 / 2) * ∑ t : Fin n, |a t| ≤ p m ∧
      1 - (1 / 2) * ∑ t : Fin n, |a t| ≤ p' m₀ := by
  classical
  let pos (t : Fin n) : ℝ := max (a t) 0
  let neg (t : Fin n) : ℝ := max (-a t) 0
  let δ (j t : Fin n) : ℝ := if t = j then 1 else 0
  let L : ℝ := (1 / 2) * ∑ t : Fin n, |a t|
  let Z : ℝ := 1 + L
  have hpos (t : Fin n) : 0 ≤ pos t := le_max_right _ _
  have hneg (t : Fin n) : 0 ≤ neg t := le_max_right _ _
  have hδ (j t : Fin n) : 0 ≤ δ j t := by dsimp [δ]; split <;> norm_num
  have hsplit (t : Fin n) : pos t - neg t = a t := by
    dsimp [pos, neg]
    rcases le_total 0 (a t) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
  have habs (t : Fin n) : pos t + neg t = |a t| := by
    dsimp [pos, neg]
    rcases le_total 0 (a t) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h, add_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h, zero_add]
  have hzero : ∑ t : Fin n, a t = 0 := by
    simpa using ha 0 (Nat.zero_le k)
  have hdiff : (∑ t : Fin n, pos t) - (∑ t : Fin n, neg t) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [hsplit] using hzero
  have htotal : (∑ t : Fin n, pos t) + (∑ t : Fin n, neg t) = ∑ t : Fin n, |a t| := by
    rw [← Finset.sum_add_distrib]
    simp only [habs]
  have hposSum : ∑ t : Fin n, pos t = L := by dsimp [L]; linarith
  have hnegSum : ∑ t : Fin n, neg t = L := by dsimp [L]; linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hZ : 0 < Z := by dsimp [Z]; linarith
  have hδsum (j : Fin n) (f : Fin n → ℝ) :
      ∑ t : Fin n, δ j t * f t = f j := by
    simp [δ, ite_mul]
  have simplex (j : Fin n) (b : Fin n → ℝ) (hb : ∀ t, 0 ≤ b t)
      (hbs : ∑ t : Fin n, b t = L) :
      (fun t => (δ j t + b t) / Z) ∈ stdSimplex ℝ (Fin n) := by
    refine ⟨fun t => div_nonneg (add_nonneg (hδ j t) (hb t)) hZ.le, ?_⟩
    rw [← Finset.sum_div, Finset.sum_add_distrib, hbs]
    have hmass : ∑ t : Fin n, δ j t = 1 := by simpa using hδsum j (fun _ => 1)
    rw [hmass]
    exact div_self hZ.ne'
  have peak (j : Fin n) (b : Fin n → ℝ) (hb : 0 ≤ b j) :
      1 - L ≤ (δ j j + b j) / Z := by
    apply (le_div_iff₀ hZ).2
    simp only [δ, if_true]
    dsimp [Z]
    nlinarith [sq_nonneg L]
  let p (t : Fin n) : ℝ := (δ m t + neg t) / Z
  let q (t : Fin n) : ℝ := (δ m₀ t + pos t) / Z
  have hp : p ∈ stdSimplex ℝ (Fin n) := simplex m neg hneg hnegSum
  have hq : q ∈ stdSimplex ℝ (Fin n) := simplex m₀ pos hpos hposSum
  refine ⟨p, q, hp, hq, ?_, peak m neg (hneg m), peak m₀ pos (hpos m₀)⟩
  apply ((affine_moment_equivalence hn k).2 p q hp hq).2
  intro i hi
  let f (t : Fin n) : ℝ := grid n (t : ℕ) ^ i
  have hc : ∑ t : Fin n, a t * f t = f m - f m₀ := ha i hi
  have hd : (∑ t : Fin n, pos t * f t) - (∑ t : Fin n, neg t * f t) =
      f m - f m₀ := by
    rw [← Finset.sum_sub_distrib]
    simpa only [← sub_mul, hsplit] using hc
  change (∑ t : Fin n, ((δ m t + neg t) / Z) * f t) =
    ∑ t : Fin n, ((δ m₀ t + pos t) / Z) * f t
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, add_mul, Finset.sum_add_distrib, hδsum]
  congr 1
  linarith
