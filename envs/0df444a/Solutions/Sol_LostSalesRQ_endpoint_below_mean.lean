-- Prove2me | solution 1 for LostSalesRQ.endpoint_below_mean
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T19:39:40.313654+00:00
-- url     : https://prove2.me/submissions/b01b8144-3b1a-4cba-abb4-e06974a38101

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Theorems.Thm_LostSalesRQ_intersection_penalty_formula
import Theorems.Thm_LostSalesRQ_erlang_variance_bound
import Theorems.Thm_LostSalesRQ_intersection_penalty_bound
import Theorems.Thm_LostSalesRQ_poisson_gaussian_rank_bound
import Theorems.Thm_LostSalesRQ_rational_gaussian_bound
import Theorems.Thm_LostSalesRQ_stockout_aging_bound

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

open Finset

lemma ebm_rank_one {μ : ℝ} (hμ : 0 ≤ μ) : 1 ≤ rankBound μ 1 := by
  unfold rankBound
  apply le_ciInf
  intro l
  unfold expectedShortfall poisTail
  rw [Finset.sum_range_succ]
  have hle : ∑ i ∈ range l, poisMass μ i ≤ ∑ i ∈ range l, ((l : ℝ) - (i : ℝ)) * poisMass μ i := by
    apply Finset.sum_le_sum
    intro i hi
    have hil : i < l := Finset.mem_range.mp hi
    have h1 : (1 : ℝ) ≤ (l : ℝ) - (i : ℝ) := by
      have : (i : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hil
      linarith
    have hp : 0 ≤ poisMass μ i := by unfold poisMass; positivity
    nlinarith
  simp only [sub_self, zero_mul, add_zero]
  linarith

lemma pm_le_pc0 {t : ℝ} (ht : 0 ≤ t) (i : ℕ) : poisMass t i ≤ poisCdf t i := by
  unfold poisCdf
  exact Finset.single_le_sum (f := fun k => poisMass t k)
    (fun k _ => by unfold poisMass; positivity) (Finset.self_mem_range_succ i)

lemma ebm_zero_mem (μ η : ℝ) :
    (0 : ℝ) ∈ {x : ℝ | ∃ (m : ℕ) (τ : Fin m → ℝ), Monotone τ ∧ (∀ i, 0 ≤ τ i ∧ τ i ≤ μ) ∧
      x = ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))} := by
  refine ⟨0, Fin.elim0, ?_, fun i => i.elim0, ?_⟩
  · intro a; exact a.elim0
  · simp

lemma ebm_D_nonneg (μ η : ℝ) : 0 ≤ agingRateSup μ η := by
  unfold agingRateSup
  by_cases hb : BddAbove {x : ℝ | ∃ (m : ℕ) (τ : Fin m → ℝ), Monotone τ ∧
      (∀ i, 0 ≤ τ i ∧ τ i ≤ μ) ∧
      x = ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))}
  · exact le_csSup hb (ebm_zero_mem μ η)
  · rw [Real.sSup_of_not_bddAbove hb]

lemma ebm_D_one (μ : ℝ) : agingRateSup μ 1 ≤ 0 := by
  unfold agingRateSup
  apply csSup_le ⟨0, ebm_zero_mem μ 1⟩
  rintro x ⟨m, τ, _, hτ, rfl⟩
  apply Finset.sum_nonpos
  intro i _
  have := pm_le_pc0 (hτ i).1 (i : ℕ)
  linarith

lemma ebm_bdd (μ a : ℝ) :
    BddAbove {x : ℝ | ∃ η : ℝ, 1 ≤ η ∧ x = min (rankBound μ η) (a - agingRateSup μ η)} := by
  refine ⟨a, ?_⟩
  rintro x ⟨η, _, rfl⟩
  have h1 := ebm_D_nonneg μ η
  have h2 := min_le_right (rankBound μ η) (a - agingRateSup μ η)
  linarith

lemma ebm_alg1 (σ y t : ℝ) (hy0 : 0 < y) (hy73 : y ≤ 7 / 3) (hσy : σ = 1 - 5 * y / 28)
    (ht : 0 < t) (htsq : t ^ 2 = σ) : 13 * σ + y ≤ 13 * t := by
  have hσ0 : 0 < σ := by rw [hσy]; linarith
  have hsq : (13 * σ + y) ^ 2 ≤ 169 * σ := by
    rw [hσy]; nlinarith [mul_nonneg hy0.le (sub_nonneg.mpr hy73)]
  have hA : 0 < 13 * σ + y := by linarith
  nlinarith

lemma ebm_alg2 (η t σ y : ℝ) (hη : 0 < η) (ht : 0 < t) (hσ : 0 < σ) (htsq : t ^ 2 = σ)
    (h13 : 13 * σ + y ≤ 13 * t) (hy0 : 0 < y) : η * t ≤ 13 * η / (13 + y / σ) := by
  rw [le_div_iff₀ (by positivity)]
  have e : η * t * (13 + y / σ) = η * t * (13 * σ + y) / σ := by
    field_simp
  rw [e, div_le_iff₀ hσ]
  have h1 := mul_le_mul_of_nonneg_left h13 (by positivity : 0 ≤ η * t)
  have h2 : η * t * (13 * t) = 13 * η * σ := by rw [← htsq]; ring
  linarith

lemma ebm_lower (μ a L : ℝ) (hμ3 : 3 ≤ μ) (hL1 : 1 ≤ L) (hL2 : L ^ 2 ≤ 7 / 3 * μ)
    (hσ : 0 < 1 - 5 * L ^ 2 / (28 * μ))
    (ha : L / 2 + L ^ 2 / (4 * (1 - 5 * L ^ 2 / (28 * μ))) < a) :
    L ≤ Real.sqrt 2 * lowerCurve μ a := by
  have hμ : 0 < μ := by linarith
  set σ := 1 - 5 * L ^ 2 / (28 * μ) with hσdef
  have hσ1 : σ ≤ 1 := by
    have : 0 ≤ 5 * L ^ 2 / (28 * μ) := by positivity
    linarith
  set s2 := Real.sqrt 2 with hs2
  have hs2sq : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2pos : 0 < s2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2lt : s2 < 3 / 2 := by nlinarith
  have hs2gt : 1 < s2 := by nlinarith
  suffices h : ∃ η : ℝ, 1 ≤ η ∧ L / s2 ≤ min (rankBound μ η) (a - agingRateSup μ η) by
    obtain ⟨η, hη, hle⟩ := h
    have hmem : min (rankBound μ η) (a - agingRateSup μ η) ∈
        {x : ℝ | ∃ η : ℝ, 1 ≤ η ∧ x = min (rankBound μ η) (a - agingRateSup μ η)} :=
      ⟨η, hη, rfl⟩
    have hsup := le_csSup (ebm_bdd μ a) hmem
    unfold lowerCurve
    have e : L = s2 * (L / s2) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (hle.trans hsup) hs2pos.le
  have hLσ : L ^ 2 / 4 ≤ L ^ 2 / (4 * σ) :=
    div_le_div_of_nonneg_left (sq_nonneg L) (by positivity) (by linarith)
  have hg34 : L / s2 ≤ 3 / 4 * L := by
    rw [div_le_iff₀ hs2pos]; nlinarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  by_cases hcase : L ≤ s2
  · refine ⟨1, le_refl 1, le_min ?_ ?_⟩
    · have h1 := ebm_rank_one hμ.le
      have : L / s2 ≤ 1 := by rw [div_le_one hs2pos]; exact hcase
      linarith
    · have h0 := ebm_D_one μ
      linarith
  · push Not at hcase
    have hσ712 : 7 / 12 ≤ σ := by
      have : 5 * L ^ 2 / (28 * μ) ≤ 5 / 12 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    set t := Real.sqrt σ with ht
    have htsq : t ^ 2 = σ := Real.sq_sqrt hσ.le
    have htpos : 0 < t := Real.sqrt_pos.mpr hσ
    have ht1 : t ≤ 1 := by nlinarith
    have hg1 : 1 < L / s2 := by rw [one_lt_div hs2pos]; exact hcase
    have hL0 : 0 < L := by linarith
    set η := L / (s2 * t) with hηdef
    have hgη : L / s2 = η * t := by
      rw [hηdef]; field_simp
    have hηg : L / s2 ≤ η := by
      rw [hgη]; nlinarith [mul_le_mul_of_nonneg_left ht1 (show 0 ≤ η by positivity)]
    have hη1 : 1 ≤ η := by linarith
    have hηpos : 0 < η := by linarith
    have hηsq : η ^ 2 = L ^ 2 / (2 * σ) := by
      rw [hηdef, div_pow, mul_pow, hs2sq, htsq]
    clear_value η
    refine ⟨η, hη1, le_min ?_ ?_⟩
    · have hG1 := poisson_gaussian_rank_bound μ η hμ hη1
      set r := Real.sqrt μ with hr
      have hrsq : r ^ 2 = μ := Real.sq_sqrt hμ.le
      have hrpos : 0 < r := Real.sqrt_pos.mpr hμ
      clear_value r
      have hG2 := rational_gaussian_bound (η / r) (by positivity)
      have hchain : 13 * η / (13 + 2 * η ^ 2 / μ) < r * gaussianRankProfile (η / r) := by
        have e : 13 * η / (13 + 2 * η ^ 2 / μ) =
            r * (13 * (η / r) / (13 + 2 * (η / r) ^ 2)) := by
          rw [div_pow, hrsq]; field_simp
        rw [e]
        exact mul_lt_mul_of_pos_left hG2 hrpos
      have hkey : L / s2 ≤ 13 * η / (13 + 2 * η ^ 2 / μ) := by
        have hy : 2 * η ^ 2 / μ = L ^ 2 / μ / σ := by
          rw [hηsq]; field_simp
        rw [hy, hgη]
        have hy0 : 0 < L ^ 2 / μ := by positivity
        have hy73 : L ^ 2 / μ ≤ 7 / 3 := by rw [div_le_iff₀ hμ]; linarith
        have hσy : σ = 1 - 5 * (L ^ 2 / μ) / 28 := by
          rw [hσdef]; ring
        have h13 := ebm_alg1 σ (L ^ 2 / μ) t hy0 hy73 hσy htpos htsq
        exact ebm_alg2 η t σ (L ^ 2 / μ) hηpos htpos hσ htsq h13 hy0
      linarith
    · have hD := stockout_aging_bound μ η hμ.le hη1
      have hηsq' : η ^ 2 / 2 = L ^ 2 / (4 * σ) := by
        rw [hηsq]; field_simp; ring
      have hg23 : 2 / 3 * (L / s2) < L / 2 := by
        rw [show 2 / 3 * (L / s2) = (2 * L) / (3 * s2) by ring,
          div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ : ℝ) (j : ℕ) (hj : 1 ≤ j) (hμj : (j : ℝ) ≤ μ) (hμ3 : 3 ≤ μ) :
    baseStockCost μ (intersectionPenalty μ j) j =
        baseStockCost μ (intersectionPenalty μ j) (j + 1) ∧
    baseStockCost μ (intersectionPenalty μ j) j ≤
        Real.sqrt 2 * lowerCurve μ (intersectionPenalty μ j) := by
  have hμ : 0 < μ := by linarith
  obtain ⟨_, _, _, hEq, hL, hL6⟩ := intersection_penalty_formula μ hμ j
  refine ⟨hEq, ?_⟩
  have hA3 := erlang_variance_bound μ hμ j hj
  have hH := moh_nonneg hμ j
  have hP := intersection_penalty_bound μ j hj hμj hμ3
  set L := baseStockCost μ (intersectionPenalty μ j) j with hLdef
  set H := meanOnHand μ j with hHdef
  set v := onHandVariance μ j with hvdef
  have hx0 : 0 < H + 1 := by linarith
  have hx0' : H + 1 ≠ 0 := hx0.ne'
  have h6 : H + 1 + v / (H + 1) = (j : ℝ) + 1 - μ + μ / (H + 1) := hL.symm.trans hL6
  have h7 : (H + 1) ^ 2 + v = ((j : ℝ) + 1 - μ) * (H + 1) + μ := by
    field_simp at h6; linarith
  have hdom : H * (H + 1) + v ≤ μ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hμj) hx0.le]
  have hL1 : 1 ≤ L := by
    rw [hL]
    have : 0 ≤ v / (H + 1) := div_nonneg hA3.1.le hx0.le
    linarith
  have hLH : L ≤ 2 * H + 1 := by
    rw [hL]
    have : v / (H + 1) ≤ H := by
      rw [div_le_iff₀ hx0]; linarith [hA3.2]
    linarith
  have hLsq : L ^ 2 ≤ 7 / 3 * μ := by
    have hdomL : (H + 1) * (L - 1) ≤ μ := by
      have : (H + 1) * (L - 1) = H * (H + 1) + v := by
        rw [hL]; field_simp; ring
      linarith
    nlinarith [mul_le_mul_of_nonneg_right (show (L + 1) / 2 ≤ H + 1 by linarith)
      (show (0 : ℝ) ≤ L - 1 by linarith)]
  exact ebm_lower μ (intersectionPenalty μ j) L hμ3 hL1 hLsq hP.1 hP.2
