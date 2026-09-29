-- Prove2me | solution 1 for LassoDantzig.Equivalence.lemma_B1_eq_B2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:03:33.69519+00:00
-- url     : https://prove2.me/submissions/ada90497-3cb5-487c-8a13-2bf3430c11dc

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

theorem aux_lb12_kkt {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (hr : 0 ≤ r) (β : Fin M → ℝ) (hL : IsLasso X y r β) (j : Fin M) :
    |(1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec β i)| ≤ r * colNorm X j := by
  set g := (1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec β i) with hg
  set A := (1 / (n : ℝ)) * ∑ i, X i j ^ 2 with hA
  set c := colNorm X j with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := by positivity
  have key : ∀ t : ℝ, 2 * t * g ≤ t ^ 2 * A + 2 * r * c * |t| := by
    intro t
    have h := hL (fun k => β k + if k = j then t else 0)
    have hmv : ∀ i, X.mulVec (fun k => β k + if k = j then t else 0) i
        = X.mulVec β i + t * X i j := by
      intro i
      simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, mul_comm]
    have hpen : ∑ k, colNorm X k * |β k + (if k = j then t else 0)|
        ≤ ∑ k, colNorm X k * |β k| + c * |t| := by
      have hterm : ∀ k, colNorm X k * |β k + (if k = j then t else 0)|
          ≤ colNorm X k * |β k| + (if k = j then c * |t| else 0) := by
        intro k
        have hck : 0 ≤ colNorm X k := Real.sqrt_nonneg _
        split_ifs with hk
        · subst hk
          nlinarith [mul_le_mul_of_nonneg_left (abs_add_le (β k) t) hck]
        · simp
      calc _ ≤ ∑ k, (colNorm X k * |β k| + (if k = j then c * |t| else 0)) :=
            Finset.sum_le_sum (fun k _ => hterm k)
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    unfold lassoObj at h
    simp only [hmv] at h
    have hexp : (1 / (n:ℝ)) * ∑ i, (y i - (X.mulVec β i + t * X i j)) ^ 2
        = (1 / (n:ℝ)) * ∑ i, (y i - X.mulVec β i) ^ 2 - 2 * t * g + t ^ 2 * A := by
      rw [hg, hA]
      have hh : ∀ i, (y i - (X.mulVec β i + t * X i j)) ^ 2
          = (y i - X.mulVec β i) ^ 2 - 2 * t * (X i j * (y i - X.mulVec β i))
            + t ^ 2 * X i j ^ 2 := fun i => by ring
      simp only [hh, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [hexp] at h
    nlinarith [mul_le_mul_of_nonneg_left hpen (by linarith : (0:ℝ) ≤ 2 * r)]
  have hside : ∀ s : ℝ, s = 1 ∨ s = -1 → s * g ≤ r * c := by
    intro s hs
    have hs2 : s ^ 2 = 1 := by rcases hs with h | h <;> subst h <;> norm_num
    have hsa : |s| = 1 := by rcases hs with h | h <;> subst h <;> norm_num
    apply le_of_forall_pos_le_add
    intro ε hε
    set t := 2 * ε / (A + 1) with ht
    have ht0 : 0 < t := by positivity
    have htA : t * A ≤ 2 * ε := by
      rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    have hk := key (s * t)
    rw [abs_mul, hsa, abs_of_pos ht0, mul_pow, hs2] at hk
    by_contra hcon
    push Not at hcon
    nlinarith [mul_lt_mul_of_pos_left hcon ht0, mul_le_mul_of_nonneg_left htA ht0.le]
  rw [abs_le]
  constructor
  · have := hside (-1) (Or.inr rfl); linarith
  · have := hside 1 (Or.inl rfl); linarith

end LassoDantzig.Equivalence

open LassoDantzig.Equivalence

theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f w : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hw : NoiseEventHalf X r w) (βL : Fin M → ℝ) (hL : IsLasso X (fun i => f i + w i) r βL) :
    ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * (f i - X.mulVec βL i)| ≤ 3 * r * fmax X / 2 := by
  intro j
  have h1 := aux_lb12_kkt X (fun i => f i + w i) r hr.le βL hL j
  have h2 := hw j
  have hc : colNorm X j ≤ fmax X := le_ciSup (Finite.bddAbove_range _) j
  have hsplit : (1 / (n : ℝ)) * ∑ i, X i j * (f i - X.mulVec βL i)
      = (1 / (n : ℝ)) * ∑ i, X i j * ((f i + w i) - X.mulVec βL i)
        - (1 / (n : ℝ)) * ∑ i, X i j * w i := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hsplit]
  calc _ ≤ |(1 / (n : ℝ)) * ∑ i, X i j * ((f i + w i) - X.mulVec βL i)|
        + |(1 / (n : ℝ)) * ∑ i, X i j * w i| := abs_sub _ _
    _ ≤ r * colNorm X j + r * colNorm X j / 2 := by linarith
    _ ≤ 3 * r * fmax X / 2 := by nlinarith
