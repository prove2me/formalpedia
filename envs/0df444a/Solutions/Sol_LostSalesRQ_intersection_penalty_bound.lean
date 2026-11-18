-- Prove2me | solution 1 for LostSalesRQ.intersection_penalty_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T19:26:35.970141+00:00
-- url     : https://prove2.me/submissions/e1730572-2561-45d6-9425-a99ba05901d8

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Theorems.Thm_LostSalesRQ_moment_inequality
import Theorems.Thm_LostSalesRQ_erlang_variance_bound
import Theorems.Thm_LostSalesRQ_intersection_penalty_formula

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

end LostSalesRQ

namespace LostSalesRQ

lemma H2_core (ρ u θ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hu : 0 < u) (hθ0 : 0 < θ)
    (hθbar : 2 * θ * (ρ + 2) < 7 * ρ) (hu0 : (2 - 4 * ρ) / 3 < u)
    (hZ : 0 < 2 * θ / 7 - ((1 - ρ - u) / (1 + ρ)) ^ 2) :
    0 < 4 * (1 - 5 * θ * (1 + ρ) ^ 2 / (28 * ρ)) * (u + ρ)
      - 2 * (1 - 5 * θ * (1 + ρ) ^ 2 / (28 * ρ)) * (1 - θ) * u * (1 + ρ)
      - (1 - θ) * (1 + ρ) ^ 2 := by
  have hρ' : 0 < 1 + ρ := by linarith
  set E := 14 / 5 * ρ * u + θ * (1 + ρ) * (ρ ^ 2 + 28 / 5 * ρ - 1 - θ * (1 + ρ) ^ 2) with hE
  have hid : 4 * (1 - 5 * θ * (1 + ρ) ^ 2 / (28 * ρ)) * (u + ρ)
      - 2 * (1 - 5 * θ * (1 + ρ) ^ 2 / (28 * ρ)) * (1 - θ) * u * (1 + ρ)
      - (1 - θ) * (1 + ρ) ^ 2
      = (1 + ρ) ^ 2 * (2 * θ / 7 - ((1 - ρ - u) / (1 + ρ)) ^ 2) + 5 * u / (14 * ρ) * E := by
    rw [hE]; field_simp; ring
  rw [hid]
  set tb := 7 * ρ / (2 * (ρ + 2)) with htb
  have htb0 : 0 < tb := by positivity
  have hθtb : θ < tb := by rw [htb, lt_div_iff₀ (by positivity)]; linarith
  have hQ : 0 < 4 + 77 * ρ + 107 * ρ ^ 2 - 89 * ρ ^ 3 - 75 * ρ ^ 4 := by
    have : 4 + 77 * ρ + 107 * ρ ^ 2 - 89 * ρ ^ 3 - 75 * ρ ^ 4
        = 4 + 20 * ρ + 57 * ρ * (1 - ρ) + ρ ^ 2 * (1 - ρ) * (164 + 75 * ρ) := by ring
    rw [this]
    have : 0 < 1 - ρ := by linarith
    positivity
  have hEb : 0 < 14 / 5 * ρ * u + tb * (1 + ρ) * (ρ ^ 2 + 28 / 5 * ρ - 1 - tb * (1 + ρ) ^ 2) := by
    have heq : 14 / 5 * ρ * u + tb * (1 + ρ) * (ρ ^ 2 + 28 / 5 * ρ - 1 - tb * (1 + ρ) ^ 2)
        = 14 / 5 * ρ * (u - (2 - 4 * ρ) / 3)
          + 7 * ρ / (60 * (ρ + 2) ^ 2) * (4 + 77 * ρ + 107 * ρ ^ 2 - 89 * ρ ^ 3 - 75 * ρ ^ 4) := by
      rw [htb]; field_simp; ring
    rw [heq]
    have : 0 < u - (2 - 4 * ρ) / 3 := by linarith
    positivity
  have hE0 : 0 < 14 / 5 * ρ * u := by positivity
  have hchord : E = (1 - θ / tb) * (14 / 5 * ρ * u)
      + (θ / tb) * (14 / 5 * ρ * u + tb * (1 + ρ) * (ρ ^ 2 + 28 / 5 * ρ - 1 - tb * (1 + ρ) ^ 2))
      + (1 + ρ) ^ 3 * θ * (tb - θ) := by
    rw [hE]; field_simp; ring
  have hEpos : 0 < E := by
    rw [hchord]
    have h1 : 0 < 1 - θ / tb := by rw [sub_pos, div_lt_one htb0]; exact hθtb
    have h2 : 0 ≤ θ / tb := by positivity
    have h3 : 0 ≤ (1 + ρ) ^ 3 * θ * (tb - θ) := by
      have : 0 ≤ tb - θ := by linarith
      positivity
    nlinarith [mul_pos h1 hE0, mul_nonneg h2 hEb.le]
  have : 0 < 5 * u / (14 * ρ) * E := by positivity
  nlinarith [mul_nonneg (sq_nonneg (1 + ρ)) hZ.le, sq_nonneg (1 + ρ)]

lemma H2_alg (μ x v : ℝ) (hμ3 : 3 ≤ μ) (hx : 1 ≤ x) (hv0 : 0 < v) (hv1 : v ≤ (x - 1) * x)
    (hdom : (x - 1) * x + v ≤ μ)
    (hZ : ((x ^ 2 - x - v) / (x ^ 2 + v)) ^ 2 < 2 * (v / μ) / 7)
    (hL3 : 3 * (x ^ 2 - x - v) < x ^ 2 + v) :
    0 < 1 - 5 * (x + v / x) ^ 2 / (28 * μ) ∧
    (x + v / x) / 2 + (x + v / x) ^ 2 / (4 * (1 - 5 * (x + v / x) ^ 2 / (28 * μ)))
      < (x + v) / (1 - v / μ) := by
  have hx0 : 0 < x := by linarith
  have hμ0 : 0 < μ := by linarith
  have hvlow : x ^ 2 / 2 - 3 * x / 4 < v := by nlinarith
  have hμx : 2 / 3 * x ^ 2 < μ := by nlinarith [sq_nonneg (x - 9 / 4)]
  have hθhalf : v / μ ≤ 1 / 2 := by rw [div_le_iff₀ hμ0]; nlinarith
  have hθ1 : v / μ < 1 := by linarith
  -- L bounds
  have hLx : x + v / x ≤ 2 * x - 1 := by
    have : v / x ≤ x - 1 := by rw [div_le_iff₀ hx0]; nlinarith
    linarith
  have hL1 : 1 ≤ x + v / x := by have : 0 < v / x := by positivity
                                 linarith
  have hμL : (x + v / x) ^ 2 - 1 ≤ 2 * μ := by
    have h1 : x * (x + v / x - 1) ≤ μ := by
      have : x * (x + v / x - 1) = (x - 1) * x + v := by field_simp; ring
      linarith
    have h2 : (x + v / x + 1) / 2 ≤ x := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ x + v / x - 1)]
  have hσ : 7 / 12 ≤ 1 - 5 * (x + v / x) ^ 2 / (28 * μ) := by
    have : (x + v / x) ^ 2 ≤ 7 / 3 * μ := by linarith
    have : 5 * (x + v / x) ^ 2 / (28 * μ) ≤ 5 / 12 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  refine ⟨by linarith, ?_⟩
  have hμv : 0 < μ - v := by nlinarith
  have hθx : v / μ < 3 / 2 * (v / x ^ 2) := by
    rw [show 3 / 2 * (v / x ^ 2) = (3 * v) / (2 * x ^ 2) by ring,
      div_lt_div_iff₀ hμ0 (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hμx hv0]
  have hρ0 : 0 < v / x ^ 2 := by positivity
  have hρ1 : v / x ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
  have hθbar : 2 * (v / μ) * (v / x ^ 2 + 2) < 7 * (v / x ^ 2) := by
    have h2 : 2 * (v / μ) * (v / x ^ 2) ≤ v / x ^ 2 := by nlinarith
    nlinarith
  have hu0' : (2 - 4 * (v / x ^ 2)) / 3 < 1 / x := by
    have key : 2 * x ^ 2 - 4 * v < 3 * x := by nlinarith
    have e1 : (2 - 4 * (v / x ^ 2)) / 3 = (2 * x ^ 2 - 4 * v) / (3 * x ^ 2) := by field_simp
    have e2 : 1 / x = 3 * x / (3 * x ^ 2) := by field_simp
    rw [e1, e2]
    exact div_lt_div_of_pos_right key (by positivity)
  have hκ : (x ^ 2 - x - v) / (x ^ 2 + v) = (1 - v / x ^ 2 - 1 / x) / (1 + v / x ^ 2) := by
    field_simp
    ring
  have hZ' : 0 < 2 * (v / μ) / 7 - ((1 - v / x ^ 2 - 1 / x) / (1 + v / x ^ 2)) ^ 2 := by
    rw [← hκ]; linarith
  have hcore := H2_core (v / x ^ 2) (1 / x) (v / μ) hρ0 hρ1 (by positivity) (by positivity)
    hθbar hu0' hZ'
  have hσeq : 1 - 5 * (x + v / x) ^ 2 / (28 * μ)
      = 1 - 5 * (v / μ) * (1 + v / x ^ 2) ^ 2 / (28 * (v / x ^ 2)) := by
    field_simp
  have hσpos : 0 < 1 - 5 * (v / μ) * (1 + v / x ^ 2) ^ 2 / (28 * (v / x ^ 2)) := by
    rw [← hσeq]; linarith
  rw [hσeq]
  generalize hS : 1 - 5 * (v / μ) * (1 + v / x ^ 2) ^ 2 / (28 * (v / x ^ 2)) = σ at hcore hσpos ⊢
  have h1θ : 1 - v / μ ≠ 0 := by linarith
  have hμv' : μ - v ≠ 0 := hμv.ne'
  have hσ0 : σ ≠ 0 := hσpos.ne'
  have hkey : 4 * σ * (1 - v / μ) * (1 / x) ^ 2 *
      ((x + v) / (1 - v / μ) - (x + v / x) / 2 - (x + v / x) ^ 2 / (4 * σ))
      = 4 * σ * (1 / x + v / x ^ 2) - 2 * σ * (1 - v / μ) * (1 / x) * (1 + v / x ^ 2)
        - (1 - v / μ) * (1 + v / x ^ 2) ^ 2 := by
    field_simp
    ring
  have hfac : 0 < 4 * σ * (1 - v / μ) * (1 / x) ^ 2 := by
    have : 0 < 1 - v / μ := by linarith
    positivity
  have : 0 < (x + v) / (1 - v / μ) - (x + v / x) / 2 - (x + v / x) ^ 2 / (4 * σ) := by
    rw [← hkey] at hcore
    exact pos_of_mul_pos_right hcore hfac.le
  linarith

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ : ℝ) (j : ℕ) (hj : 1 ≤ j) (hμj : (j : ℝ) ≤ μ)
    (hμ3 : 3 ≤ μ) :
    0 < 1 - 5 * baseStockCost μ (intersectionPenalty μ j) j ^ 2 / (28 * μ) ∧
    baseStockCost μ (intersectionPenalty μ j) j / 2 +
        baseStockCost μ (intersectionPenalty μ j) j ^ 2 /
          (4 * (1 - 5 * baseStockCost μ (intersectionPenalty μ j) j ^ 2 / (28 * μ))) <
      intersectionPenalty μ j := by
  have hμ : 0 < μ := by linarith
  have hH1 := moment_inequality μ j hj hμj
  have hA3 := erlang_variance_bound μ hμ j hj
  obtain ⟨_, _, ha, _, hL, hL6⟩ := intersection_penalty_formula μ hμ j
  have hv := ohv_eq hμ j
  have hA := en_eq hμ j
  have he := lf_pos hμ j
  have hH := moh_nonneg hμ j
  have hx0 : 0 < meanOnHand μ j + 1 := by linarith
  have hex : lossFraction μ j * (meanOnHand μ j + 1) = 1 - onHandVariance μ j / μ := by
    rw [hv]; field_simp; ring
  have hθ1 : onHandVariance μ j / μ < 1 := by
    have : 0 < lossFraction μ j * (meanOnHand μ j + 1) := mul_pos he hx0
    linarith
  have haj : intersectionPenalty μ j
      = (meanOnHand μ j + 1 + onHandVariance μ j) / (1 - onHandVariance μ j / μ) := by
    rw [ha, hA, ← hex]
    have : lossFraction μ j ≠ 0 := he.ne'
    field_simp
  have hdom : (meanOnHand μ j + 1 - 1) * (meanOnHand μ j + 1) + onHandVariance μ j ≤ μ := by
    have h6 : (meanOnHand μ j + 1) + onHandVariance μ j / (meanOnHand μ j + 1)
        = (j : ℝ) + 1 - μ + μ / (meanOnHand μ j + 1) := by
      rw [← hL, hL6]
    have h7 : (meanOnHand μ j + 1) ^ 2 + onHandVariance μ j
        = ((j : ℝ) + 1 - μ) * (meanOnHand μ j + 1) + μ := by
      field_simp at h6
      linarith
    nlinarith
  have hv1 : onHandVariance μ j ≤ (meanOnHand μ j + 1 - 1) * (meanOnHand μ j + 1) := by
    have := hA3.2
    nlinarith
  have hκeq : (meanOnHand μ j - onHandVariance μ j / (meanOnHand μ j + 1)) /
        baseStockCost μ (intersectionPenalty μ j) j
      = ((meanOnHand μ j + 1) ^ 2 - (meanOnHand μ j + 1) - onHandVariance μ j) /
        ((meanOnHand μ j + 1) ^ 2 + onHandVariance μ j) := by
    rw [hL]; field_simp; ring
  have hZ : (((meanOnHand μ j + 1) ^ 2 - (meanOnHand μ j + 1) - onHandVariance μ j) /
        ((meanOnHand μ j + 1) ^ 2 + onHandVariance μ j)) ^ 2 < 2 * (onHandVariance μ j / μ) / 7 := by
    have := hH1.1
    rw [hκeq] at this
    linarith
  have hL3 : 3 * ((meanOnHand μ j + 1) ^ 2 - (meanOnHand μ j + 1) - onHandVariance μ j)
      < (meanOnHand μ j + 1) ^ 2 + onHandVariance μ j := by
    have h := hH1.2
    rw [hL] at h
    have e1 : 3 * (meanOnHand μ j - onHandVariance μ j / (meanOnHand μ j + 1))
        = 3 * ((meanOnHand μ j + 1) ^ 2 - (meanOnHand μ j + 1) - onHandVariance μ j)
            / (meanOnHand μ j + 1) := by field_simp; ring
    have e2 : meanOnHand μ j + 1 + onHandVariance μ j / (meanOnHand μ j + 1)
        = ((meanOnHand μ j + 1) ^ 2 + onHandVariance μ j) / (meanOnHand μ j + 1) := by
      field_simp
    rw [e1, e2] at h
    exact (div_lt_div_iff_of_pos_right hx0).mp h
  have hfin := H2_alg μ (meanOnHand μ j + 1) (onHandVariance μ j) hμ3 (by linarith) hA3.1 hv1
    hdom hZ hL3
  rw [hL, haj]
  exact hfin
