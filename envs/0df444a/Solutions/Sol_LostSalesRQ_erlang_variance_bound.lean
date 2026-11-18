-- Prove2me | solution 1 for LostSalesRQ.erlang_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T18:52:03.655601+00:00
-- url     : https://prove2.me/submissions/00a99e5f-3fa4-4123-8f29-102427bf2523

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals

namespace LostSalesRQ
open Finset

lemma pm_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < poisMass μ j := by
  unfold poisMass; positivity

lemma pm_succ (μ : ℝ) (j : ℕ) :
    poisMass μ (j + 1) * ((j : ℝ) + 1) = μ * poisMass μ j := by
  unfold poisMass
  rw [Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma pc_succ (μ : ℝ) (j : ℕ) : poisCdf μ (j + 1) = poisCdf μ j + poisMass μ (j + 1) := by
  unfold poisCdf; rw [Finset.sum_range_succ]

lemma pc_zero (μ : ℝ) : poisCdf μ 0 = poisMass μ 0 := by simp [poisCdf]

lemma pm_le_pc {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : poisMass μ j ≤ poisCdf μ j := by
  unfold poisCdf
  exact Finset.single_le_sum (fun i _ => (pm_pos hμ i).le) (Finset.self_mem_range_succ j)

lemma pc_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < poisCdf μ j :=
  lt_of_lt_of_le (pm_pos hμ j) (pm_le_pc hμ j)

lemma sum_i_pm (μ : ℝ) (j : ℕ) :
    ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i = μ * (poisCdf μ j - poisMass μ j) := by
  induction j with
  | zero => simp [poisCdf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination h

lemma sum_ii_pm (μ : ℝ) (j : ℕ) :
    ∑ i ∈ range (j + 1), (i : ℝ) * ((i : ℝ) - 1) * poisMass μ i
      = μ ^ 2 * (poisCdf μ j - poisMass μ j) - μ * (j : ℝ) * poisMass μ j := by
  induction j with
  | zero => simp [poisCdf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination ((n : ℝ) + μ) * h

lemma lf_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < lossFraction μ j := by
  unfold lossFraction; exact div_pos (pm_pos hμ j) (pc_pos hμ j)

lemma lf_le_one {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : lossFraction μ j ≤ 1 := by
  unfold lossFraction; rw [div_le_one (pc_pos hμ j)]; exact pm_le_pc hμ j

lemma moh_mul_pc {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    meanOnHand μ j * poisCdf μ j = ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
  have hF := pc_pos hμ j
  have h1 := sum_i_pm μ j
  have h0 : ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i
      = (j : ℝ) * poisCdf μ j - ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i := by
    unfold poisCdf
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h0, h1]
  unfold meanOnHand lossFraction
  field_simp
  ring

lemma moh_nonneg {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 ≤ meanOnHand μ j := by
  have hF := pc_pos hμ j
  have h := moh_mul_pc hμ j
  have hs : 0 ≤ ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
    apply Finset.sum_nonneg
    intro i hi
    have hij : (i : ℝ) ≤ j := by
      have := Finset.mem_range.mp hi
      exact_mod_cast Nat.lt_succ_iff.mp this
    exact mul_nonneg (by linarith) (pm_pos hμ i).le
  by_contra hneg
  push_neg at hneg
  have : meanOnHand μ j * poisCdf μ j < 0 := mul_neg_of_neg_of_pos hneg hF
  linarith

lemma lf_succ {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    lossFraction μ (j + 1) = μ * lossFraction μ j / (μ + meanOnHand μ j + 1) := by
  have hF := pc_pos hμ j
  have hp := pm_pos hμ j
  have h := pm_succ μ j
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hHdef : meanOnHand μ j = (j : ℝ) - μ + μ * lossFraction μ j := rfl
  have hpe : poisMass μ j = lossFraction μ j * poisCdf μ j := by
    unfold lossFraction; field_simp
  have he := lf_pos hμ j
  rw [hHdef]
  set e := lossFraction μ j with he_def
  set F := poisCdf μ j with hF_def
  have hp' : poisMass μ (j + 1) = μ * e * F / ((j : ℝ) + 1) := by
    rw [eq_div_iff hj.ne', h, hpe]; ring
  show poisMass μ (j + 1) / poisCdf μ (j + 1) = _
  rw [pc_succ, hp']
  have h1 : 0 < F + μ * e * F / ((j : ℝ) + 1) := by positivity
  have h2 : 0 < μ + ((j : ℝ) - μ + μ * e) + 1 := by nlinarith
  rw [div_eq_div_iff h1.ne' h2.ne']
  field_simp
  ring

lemma ohv_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    onHandVariance μ j = μ * (1 - lossFraction μ j * (meanOnHand μ j + 1)) := by
  have hF := pc_pos hμ j
  have hFne : poisCdf μ j ≠ 0 := hF.ne'
  set H := meanOnHand μ j with hHdef
  -- reflect the sum
  have hrefl : onHandVariance μ j
      = ∑ i ∈ range (j + 1), (((j : ℝ) - (i : ℝ)) - H) ^ 2 * (poisMass μ i / poisCdf μ j) := by
    unfold onHandVariance
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : j + 1 - 1 - i = j - i := by omega
    have h2 : j - (j - i) = i := by omega
    rw [h1, h2]
    push_cast [hij]
    ring
  rw [hrefl]
  have hexp : ∀ i ∈ range (j + 1), (((j : ℝ) - (i : ℝ)) - H) ^ 2 * (poisMass μ i / poisCdf μ j)
      = ((((j : ℝ) - H) ^ 2) * poisMass μ i - (2 * ((j : ℝ) - H) - 1) * ((i : ℝ) * poisMass μ i)
          + (i : ℝ) * ((i : ℝ) - 1) * poisMass μ i) / poisCdf μ j := by
    intro i _; field_simp; ring
  rw [Finset.sum_congr rfl hexp, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_i_pm, sum_ii_pm]
  have hFdef : ∑ i ∈ range (j + 1), poisMass μ i = poisCdf μ j := rfl
  rw [hFdef]
  rw [hHdef]
  unfold meanOnHand lossFraction
  field_simp
  ring

lemma en_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : erlangNormalizer μ j = 1 / lossFraction μ j := by
  unfold erlangNormalizer lossFraction
  rw [one_div_div]


lemma R_ineq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    μ ≤ (meanOnHand μ j + 1) * (meanOnHand μ j + μ * lossFraction μ j) := by
  induction j with
  | zero =>
    have h0 : lossFraction μ 0 = 1 := by
      unfold lossFraction; rw [pc_zero]; exact div_self (pm_pos hμ 0).ne'
    have hH0 : meanOnHand μ 0 = 0 := by unfold meanOnHand; rw [h0]; simp
    rw [hH0, h0]; linarith
  | succ n ih =>
    have he := lf_pos hμ n
    have hH := moh_nonneg hμ n
    have hrec := lf_succ hμ n
    have hHdef : meanOnHand μ n = (n : ℝ) - μ + μ * lossFraction μ n := rfl
    have hH' : meanOnHand μ (n + 1) = ((n : ℝ) + 1) - μ + μ * lossFraction μ (n + 1) := by
      unfold meanOnHand; push_cast; ring
    rw [hH', hrec]
    set e := lossFraction μ n with he_def
    set H := meanOnHand μ n with hH_def
    have heH : μ * e = H - n + μ := by linarith [hHdef]
    have hD : 0 < μ + H + 1 := by linarith
    have hsub : μ * (μ * e / (μ + H + 1)) = μ * (H - n + μ) / (μ + H + 1) := by
      rw [← heH]; ring
    rw [hsub, ← sub_nonneg]
    have key : ((n : ℝ) + 1 - μ + μ * (H - n + μ) / (μ + H + 1) + 1) *
        ((n : ℝ) + 1 - μ + μ * (H - n + μ) / (μ + H + 1) + μ * (H - n + μ) / (μ + H + 1)) - μ
        = ((n : ℝ) + 1) * ((H + 1) ^ 2 * ((n : ℝ) + 2 + μ) + (H + 1) * μ * (μ - n - 1) - μ ^ 2)
            / (μ + H + 1) ^ 2 := by
      field_simp; ring
    rw [key]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity)
    have hR : 0 ≤ (H + 1) * (2 * H - n + μ) - μ := by
      have : (H + 1) * (H + μ * e) = (H + 1) * (2 * H - n + μ) := by rw [heH]; ring
      linarith [ih, this]
    have ha : 0 < H + 1 := by linarith
    by_cases hc : 0 ≤ (H + 1) * ((n : ℝ) + 2 - μ) + μ
    · nlinarith [mul_nonneg hμ.le hR, mul_nonneg ha.le hc]
    · push_neg at hc
      have hc' : 0 < (H + 1) * (μ - n - 2) - μ := by linarith
      have hm : 0 < μ - n - 2 := by
        by_contra hneg; push_neg at hneg
        nlinarith [mul_nonneg ha.le (by linarith : (0 : ℝ) ≤ -(μ - n - 2))]
      have h1 : 0 < μ * ((H + 1) * (μ - n - 2) - μ) := mul_pos hμ hc'
      have h2 : 0 < (H + 1) ^ 2 * ((n : ℝ) + 2 + μ) := by positivity
      have h3 : 0 < (H + 1) * μ := mul_pos ha hμ
      nlinarith [h1, h2, h3]

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ : ℝ) (hμ : 0 < μ) (j : ℕ) (hj : 1 ≤ j) :
    0 < onHandVariance μ j ∧ onHandVariance μ j ≤ meanOnHand μ j * (meanOnHand μ j + 1) := by
  constructor
  · have hF := pc_pos hμ j
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (j + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega
    have hnn : ∀ l ∈ Finset.range (j + 1),
        0 ≤ ((l : ℝ) - meanOnHand μ j) ^ 2 * (poisMass μ (j - l) / poisCdf μ j) := by
      intro l _
      exact mul_nonneg (sq_nonneg _) (div_nonneg (pm_pos hμ _).le hF.le)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l hl _ => hnn l hl)
    rw [Finset.sum_pair (by norm_num)] at hle
    simp only [Nat.cast_zero, Nat.cast_one, Nat.sub_zero] at hle
    have hw0 : 0 < poisMass μ j / poisCdf μ j := div_pos (pm_pos hμ _) hF
    have hw1 : 0 < poisMass μ (j - 1) / poisCdf μ j := div_pos (pm_pos hμ _) hF
    set H := meanOnHand μ j
    have hpos : 0 < (0 - H) ^ 2 * (poisMass μ j / poisCdf μ j)
        + (1 - H) ^ 2 * (poisMass μ (j - 1) / poisCdf μ j) := by
      by_cases hH0 : H = 0
      · rw [hH0]; norm_num; exact hw1
      · have : 0 < (0 - H) ^ 2 := by
          have : (0 - H) ≠ 0 := by intro h; apply hH0; linarith
          positivity
        nlinarith [mul_pos this hw0, mul_nonneg (sq_nonneg (1 - H)) hw1.le]
    unfold onHandVariance
    linarith
  · have hR := R_ineq hμ j
    have hv := ohv_eq hμ j
    rw [hv]
    nlinarith [hR]
