-- Prove2me | solution 1 for LassoDantzig.Lasso.eq_B6_kkt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:03:51.485381+00:00
-- url     : https://prove2.me/submissions/958b1223-2228-424c-b575-d6e4e4fd9e12

import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

/-- Quadratic expansion of the empirical loss around `βhat`. -/
lemma aux_b6kkt_expand {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ)
    (βhat d : Fin M → ℝ) :
    (1 / (n : ℝ)) * ∑ i, (y i - X.mulVec (βhat + d) i) ^ 2 =
      (1 / (n : ℝ)) * ∑ i, (y i - X.mulVec βhat i) ^ 2
        - 2 * ∑ j, d j * ((1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i))
        + (1 / (n : ℝ)) * ∑ i, (X.mulVec d i) ^ 2 := by
  have hcross : ∑ i, (y i - X.mulVec βhat i) * X.mulVec d i =
      ∑ j, d j * ∑ i, X i j * (y i - X.mulVec βhat i) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  have hsplit : ∑ i, (y i - X.mulVec (βhat + d) i) ^ 2 =
      ∑ i, (y i - X.mulVec βhat i) ^ 2 - 2 * ∑ i, (y i - X.mulVec βhat i) * X.mulVec d i
        + ∑ i, (X.mulVec d i) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mulVec_add, Pi.add_apply]
    ring
  have hg : ∑ j, d j * ((1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i)) =
      (1 / (n : ℝ)) * ∑ j, d j * ∑ i, X i j * (y i - X.mulVec βhat i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hsplit, hg, ← hcross]
  ring

/-- A limiting argument: a linear-in-`s` inequality holding for all small `s > 0`. -/
lemma aux_b6kkt_lim (A B c δ : ℝ) (hδ : 0 < δ) (hc : 0 ≤ c)
    (h : ∀ s : ℝ, 0 < s → s ≤ δ → s * A ≤ s * B + s ^ 2 * c) : A ≤ B := by
  by_contra hAB
  push Not at hAB
  have hAB' : 0 < A - B := by linarith
  set s := min δ ((A - B) / (2 * (c + 1))) with hs
  have hs1 : 0 < s := lt_min hδ (by positivity)
  have hs2 : s ≤ δ := min_le_left _ _
  have hs3 : s ≤ (A - B) / (2 * (c + 1)) := min_le_right _ _
  have h1 := h s hs1 hs2
  have h2 : s * (A - B) ≤ s * (s * c) := by nlinarith
  have h3 : A - B ≤ s * c := le_of_mul_le_mul_left h2 hs1
  have h4 : s * (2 * (c + 1)) ≤ A - B := by
    rwa [le_div_iff₀ (by positivity)] at hs3
  nlinarith [mul_nonneg hs1.le hc]

/-- One-coordinate perturbation inequality derived from minimality. -/
lemma aux_b6kkt_coord {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) (h : IsLasso X y r βhat) (j : Fin M) (t : ℝ) :
    2 * t * ((1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i)) ≤
      t ^ 2 * ((1 / (n : ℝ)) * ∑ i, X i j ^ 2) + 2 * r * (|βhat j + t| - |βhat j|) := by
  have hmin := h (βhat + Pi.single j t)
  rw [aux_b6kkt_expand] at hmin
  have hlin : ∑ k, (Pi.single j t : Fin M → ℝ) k *
      ((1 / (n : ℝ)) * ∑ i, X i k * (y i - X.mulVec βhat i)) =
      t * ((1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i)) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hquad : (1 / (n : ℝ)) * ∑ i, (X.mulVec (Pi.single j t) i) ^ 2 =
      t ^ 2 * ((1 / (n : ℝ)) * ∑ i, X i j ^ 2) := by
    have : ∀ i, X.mulVec (Pi.single j t) i = X i j * t := by
      intro i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    simp_rw [this, mul_pow, ← Finset.sum_mul]
    ring
  have hl1 : l1Norm (βhat + Pi.single j t) - l1Norm βhat = |βhat j + t| - |βhat j| := by
    unfold l1Norm
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hlin, hquad] at hmin
  have he : 2 * r * l1Norm (βhat + Pi.single j t) =
      2 * r * l1Norm βhat + 2 * r * (|βhat j + t| - |βhat j|) := by
    rw [← hl1]; ring
  linarith

end LassoDantzig.Lasso

open LassoDantzig.Lasso
open MeasureTheory ProbabilityTheory

theorem solution {n M : ℕ} (hn : 1 ≤ n)
    (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (βhat : Fin M → ℝ) :
    IsLasso X y r βhat ↔
      ∀ j : Fin M,
        (βhat j ≠ 0 →
          (1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i) = r * Real.sign (βhat j)) ∧
        (βhat j = 0 →
          |(1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i)| ≤ r) := by
  constructor
  · intro h j
    set g := (1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i) with hg
    set c := (1 / (n : ℝ)) * ∑ i, X i j ^ 2 with hc
    set b := βhat j with hb
    have hc0 : 0 ≤ c := by positivity
    have H : ∀ t : ℝ, 2 * t * g ≤ t ^ 2 * c + 2 * r * (|b + t| - |b|) :=
      fun t => aux_b6kkt_coord X y r βhat h j t
    -- g ≤ r
    have hup : g ≤ r := by
      have := aux_b6kkt_lim (2 * g) (2 * r) c 1 one_pos hc0 (fun s hs _ => by
        have h1 := H s
        have h2 : |b + s| ≤ |b| + s := by
          have := abs_add_le b s
          rwa [abs_of_pos hs] at this
        nlinarith)
      linarith
    -- -g ≤ r
    have hlo : -g ≤ r := by
      have := aux_b6kkt_lim (-2 * g) (2 * r) c 1 one_pos hc0 (fun s hs _ => by
        have h1 := H (-s)
        have h2 : |b + -s| ≤ |b| + s := by
          have := abs_add_le b (-s)
          rwa [abs_neg, abs_of_pos hs] at this
        nlinarith)
      linarith
    refine ⟨fun hb0 => ?_, fun hb0 => abs_le.mpr ⟨by linarith, hup⟩⟩
    rcases lt_or_gt_of_ne hb0 with hneg | hpos
    · -- b < 0: g ≤ -r
      have hle : g ≤ -r := by
        have := aux_b6kkt_lim (2 * r) (-2 * g) c (-b) (by linarith) hc0 (fun s hs hsb => by
          have h1 := H s
          have e1 : |b + s| = -(b + s) := abs_of_nonpos (by linarith)
          have e2 : |b| = -b := abs_of_neg hneg
          rw [e1, e2] at h1
          nlinarith)
        linarith
      rw [Real.sign_of_neg hneg]
      linarith
    · -- b > 0: g ≥ r
      have hge : r ≤ g := by
        have := aux_b6kkt_lim (2 * r) (2 * g) c b hpos hc0 (fun s hs hsb => by
          have h1 := H (-s)
          have e1 : |b + -s| = b - s := abs_of_nonneg (by linarith)
          have e2 : |b| = b := abs_of_pos hpos
          rw [e1, e2] at h1
          nlinarith)
        linarith
      rw [Real.sign_of_pos hpos]
      linarith
  · intro hk β
    have hd : β = βhat + (β - βhat) := by abel
    set d := β - βhat with hdd
    rw [hd, aux_b6kkt_expand]
    have hterm : ∀ j, d j * ((1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i)) ≤
        r * (|βhat j + d j| - |βhat j|) := by
      intro j
      set g := (1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i) with hg
      obtain ⟨h1, h2⟩ := hk j
      by_cases hb0 : βhat j = 0
      · have hg' := h2 hb0
        rw [hb0, zero_add, abs_zero, sub_zero]
        calc d j * g ≤ |d j * g| := le_abs_self _
          _ = |d j| * |g| := abs_mul _ _
          _ ≤ |d j| * r := mul_le_mul_of_nonneg_left hg' (abs_nonneg _)
          _ = r * |d j| := by ring
      · have hg' := h1 hb0
        rcases lt_or_gt_of_ne hb0 with hneg | hpos
        · rw [Real.sign_of_neg hneg] at hg'
          rw [abs_of_neg hneg, hg, hg']
          have := neg_le_abs (βhat j + d j)
          nlinarith [mul_nonneg hr.le (show 0 ≤ |βhat j + d j| + (βhat j + d j) by linarith)]
        · rw [Real.sign_of_pos hpos] at hg'
          rw [abs_of_pos hpos, hg, hg']
          have := le_abs_self (βhat j + d j)
          nlinarith [mul_nonneg hr.le (show 0 ≤ |βhat j + d j| - (βhat j + d j) by linarith)]
    have hsum : ∑ j, d j * ((1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i)) ≤
        r * (l1Norm (βhat + d) - l1Norm βhat) := by
      unfold l1Norm
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => by simpa using hterm j)
    have hq : 0 ≤ (1 / (n : ℝ)) * ∑ i, (X.mulVec d i) ^ 2 := by positivity
    nlinarith
