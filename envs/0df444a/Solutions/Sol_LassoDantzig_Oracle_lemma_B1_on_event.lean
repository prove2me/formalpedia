-- Prove2me | solution 1 for LassoDantzig.Oracle.lemma_B1_on_event
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:51:05.517301+00:00
-- url     : https://prove2.me/submissions/91240148-d566-4435-9b06-f4a3db1bf393

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

theorem aux_lb1_colNorm_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) :
    0 ≤ colNorm X j := by
  unfold colNorm empNorm
  exact Real.sqrt_nonneg _

/-- Cross-term identity. -/
theorem aux_lb1_cross {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (f y : Fin n → ℝ)
    (βhat β : Fin M → ℝ) :
    ∑ j, (βhat j - β j) * ((1 / (n : ℝ)) * ∑ i, X i j * (y i - f i)) =
      (1 / (n : ℝ)) * ∑ i, (y i - f i) * (X.mulVec βhat i - X.mulVec β i) := by
  have h : ∀ i, X.mulVec βhat i - X.mulVec β i = ∑ j, X i j * (βhat j - β j) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Expansion of the difference of empirical risks. -/
theorem aux_lb1_expand {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (f y : Fin n → ℝ)
    (βhat β : Fin M → ℝ) :
    empSq (fun i => y i - X.mulVec βhat i) - empSq (fun i => y i - X.mulVec β i) =
      empSq (fun i => X.mulVec βhat i - f i) - empSq (fun i => X.mulVec β i - f i) -
        2 * ((1 / (n : ℝ)) * ∑ i, (y i - f i) * (X.mulVec βhat i - X.mulVec β i)) := by
  unfold empSq
  have h : ∀ i, (y i - X.mulVec βhat i) ^ 2 =
      (X.mulVec βhat i - f i) ^ 2 - (X.mulVec β i - f i) ^ 2 + (y i - X.mulVec β i) ^ 2
        - 2 * ((y i - f i) * (X.mulVec βhat i - X.mulVec β i)) := by
    intro i; ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

theorem aux_lb1_crossbound {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (f y : Fin n → ℝ)
    (r : ℝ) (hA : NoiseBound X (fun i => y i - f i) r) (βhat β : Fin M → ℝ) :
    2 * ∑ j, (βhat j - β j) * ((1 / (n : ℝ)) * ∑ i, X i j * (y i - f i)) ≤
      r * ∑ j, colNorm X j * |βhat j - β j| := by
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj := hA j
  simp only at hj
  set V := (1 / (n : ℝ)) * ∑ i, X i j * (y i - f i)
  have h1 : 2 * ((βhat j - β j) * V) ≤ |βhat j - β j| * (2 * |V|) := by
    calc 2 * ((βhat j - β j) * V) ≤ |2 * ((βhat j - β j) * V)| := le_abs_self _
      _ = |βhat j - β j| * (2 * |V|) := by
        rw [abs_mul, abs_mul, abs_two]; ring
  have h2 : |βhat j - β j| * (2 * |V|) ≤ |βhat j - β j| * (r * colNorm X j) :=
    mul_le_mul_of_nonneg_left hj (abs_nonneg _)
  linarith

theorem aux_lb1_split {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (βhat β : Fin M → ℝ) :
    ∑ j, colNorm X j * (|βhat j - β j| + |β j| - |βhat j|) ≤
      2 * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| := by
  unfold supp
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hc := aux_lb1_colNorm_nonneg X j
  split_ifs with h
  · have : |β j| - |βhat j| ≤ |βhat j - β j| := by
      rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
    have : colNorm X j * (|βhat j - β j| + |β j| - |βhat j|) ≤
        colNorm X j * (2 * |βhat j - β j|) :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    linarith
  · rw [not_not.mp h]
    simp

end LassoDantzig.Oracle

open LassoDantzig.Oracle
open MeasureTheory ProbabilityTheory

theorem solution {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (f y : Fin n → ℝ) (r : ℝ) (hr : 0 < r) (hA : NoiseBound X (fun i => y i - f i) r)
    (βhat : Fin M → ℝ) (hL : IsLasso X y r βhat) (β : Fin M → ℝ) :
    empSq (fun i => X.mulVec βhat i - f i) + r * ∑ j, colNorm X j * |βhat j - β j| ≤
        empSq (fun i => X.mulVec β i - f i) +
          4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ∧
      empSq (fun i => X.mulVec β i - f i) +
          4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ≤
        empSq (fun i => X.mulVec β i - f i) +
          4 * r * Real.sqrt (sparsity β) *
            Real.sqrt (∑ j ∈ supp β, colNorm X j ^ 2 * |βhat j - β j| ^ 2) := by
  constructor
  · have hlasso := hL β
    unfold lassoObj at hlasso
    have hexp := aux_lb1_expand X f y βhat β
    have hcross := aux_lb1_cross X f y βhat β
    have hcb := aux_lb1_crossbound X f y r hA βhat β
    have hsplit := aux_lb1_split X βhat β
    have hlin : ∑ j, colNorm X j * (|βhat j - β j| + |β j| - |βhat j|) =
        ∑ j, colNorm X j * |βhat j - β j| + ∑ j, colNorm X j * |β j| -
          ∑ j, colNorm X j * |βhat j| := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hlin] at hsplit
    have h2r : 0 ≤ 2 * r := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsplit h2r
    rw [hcross] at hcb
    nlinarith
  · have hc : ∀ j, 0 ≤ colNorm X j * |βhat j - β j| := fun j =>
      mul_nonneg (aux_lb1_colNorm_nonneg X j) (abs_nonneg _)
    have hS : 0 ≤ ∑ j ∈ supp β, colNorm X j * |βhat j - β j| :=
      Finset.sum_nonneg (fun j _ => hc j)
    have hcs := sq_sum_le_card_mul_sum_sq (s := supp β)
      (f := fun j => colNorm X j * |βhat j - β j|)
    simp only [mul_pow] at hcs
    have hle : ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ≤
        Real.sqrt (sparsity β) *
          Real.sqrt (∑ j ∈ supp β, colNorm X j ^ 2 * |βhat j - β j| ^ 2) := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
      have := Real.abs_le_sqrt hcs
      rw [abs_of_nonneg hS] at this
      unfold sparsity
      exact this
    have h4r : 0 ≤ 4 * r := by linarith
    have := mul_le_mul_of_nonneg_left hle h4r
    linarith [mul_assoc (4 * r) (Real.sqrt (sparsity β))
      (Real.sqrt (∑ j ∈ supp β, colNorm X j ^ 2 * |βhat j - β j| ^ 2))]
