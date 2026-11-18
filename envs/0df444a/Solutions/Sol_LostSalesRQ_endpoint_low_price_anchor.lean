-- Prove2me | solution 1 for LostSalesRQ.endpoint_low_price_anchor
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T19:50:07.061257+00:00
-- url     : https://prove2.me/submissions/c6ae6c80-a3ed-4737-89c0-e1f8a74260c2

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Theorems.Thm_LostSalesRQ_penalty_calibration

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

lemma anc_pm_nonneg {t : ℝ} (ht : 0 ≤ t) (i : ℕ) : 0 ≤ poisMass t i := by
  unfold poisMass; positivity

lemma anc_pm_le_pc {t : ℝ} (ht : 0 ≤ t) (i : ℕ) : poisMass t i ≤ poisCdf t i := by
  unfold poisCdf
  exact Finset.single_le_sum (f := fun k => poisMass t k)
    (fun k _ => anc_pm_nonneg ht k) (Finset.self_mem_range_succ i)

lemma anc_es_succ (t : ℝ) (l : ℕ) :
    expectedShortfall t (l + 1) = expectedShortfall t l + poisCdf t l := by
  unfold expectedShortfall poisCdf
  rw [Finset.sum_range_succ _ (l + 1)]
  push_cast
  simp only [sub_self, zero_mul, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma anc_pt_succ (t : ℝ) (l : ℕ) : poisTail t (l + 1) = poisTail t l - poisMass t l := by
  unfold poisTail; rw [Finset.sum_range_succ]; ring

lemma anc_zero_mem (μ η : ℝ) :
    (0 : ℝ) ∈ {x : ℝ | ∃ (m : ℕ) (τ : Fin m → ℝ), Monotone τ ∧ (∀ i, 0 ≤ τ i ∧ τ i ≤ μ) ∧
      x = ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))} := by
  refine ⟨0, Fin.elim0, ?_, fun i => i.elim0, ?_⟩
  · intro a; exact a.elim0
  · simp

lemma anc_D_nonneg (μ η : ℝ) : 0 ≤ agingRateSup μ η := by
  unfold agingRateSup
  by_cases hb : BddAbove {x : ℝ | ∃ (m : ℕ) (τ : Fin m → ℝ), Monotone τ ∧
      (∀ i, 0 ≤ τ i ∧ τ i ≤ μ) ∧
      x = ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))}
  · exact le_csSup hb (anc_zero_mem μ η)
  · rw [Real.sSup_of_not_bddAbove hb]

lemma anc_bdd (μ a : ℝ) :
    BddAbove {x : ℝ | ∃ η : ℝ, 1 ≤ η ∧ x = min (rankBound μ η) (a - agingRateSup μ η)} := by
  refine ⟨a, ?_⟩
  rintro x ⟨η, _, rfl⟩
  have h1 := anc_D_nonneg μ η
  have h2 := min_le_right (rankBound μ η) (a - agingRateSup μ η)
  linarith

-- The rank values at the weight 1 + 1/μ.
lemma anc_V_step {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    expectedShortfall μ (k + 1) + (1 + μ⁻¹) * poisTail μ (k + 1) ≤
      expectedShortfall μ (k + 1 + 1) + (1 + μ⁻¹) * poisTail μ (k + 1 + 1) := by
  rw [anc_es_succ μ (k + 1), anc_pt_succ μ (k + 1), pc_succ]
  have h1 := pm_succ μ k
  have h2 := anc_pm_le_pc hμ.le k
  have h3 := anc_pm_nonneg hμ.le k
  have h4 := anc_pm_nonneg hμ.le (k + 1)
  -- need: (1/μ) p_{k+1} ≤ F_k
  have key : μ⁻¹ * poisMass μ (k + 1) ≤ poisCdf μ k := by
    have e : μ⁻¹ * poisMass μ (k + 1) = poisMass μ k / ((k : ℝ) + 1) := by
      field_simp
      linarith [h1]
    rw [e]
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    calc poisMass μ k / ((k : ℝ) + 1) ≤ poisMass μ k := div_le_self h3 hk
      _ ≤ poisCdf μ k := h2
  push_cast
  nlinarith [key]

lemma anc_V_ge {μ : ℝ} (hμ : 0 < μ) (l : ℕ) :
    expectedShortfall μ 1 + (1 + μ⁻¹) * poisTail μ 1 ≤
      expectedShortfall μ l + (1 + μ⁻¹) * poisTail μ l := by
  rcases l with _ | l
  · -- l = 0
    have e1 : expectedShortfall μ 1 = poisMass μ 0 := by
      unfold expectedShortfall; simp [Finset.sum_range_succ]
    have e2 : poisTail μ 1 = 1 - poisMass μ 0 := by
      unfold poisTail; simp
    have e3 : expectedShortfall μ 0 = 0 := by unfold expectedShortfall; simp
    have e4 : poisTail μ 0 = 1 := by unfold poisTail; simp
    rw [e1, e2, e3, e4]
    have hp := anc_pm_nonneg hμ.le 0
    have hμi : 0 < μ⁻¹ := inv_pos.mpr hμ
    nlinarith
  · induction l with
    | zero => exact le_refl _
    | succ n ih => exact ih.trans (anc_V_step hμ n)

lemma anc_B {μ : ℝ} (hμ : 0 < μ) :
    rankBound μ (1 + μ⁻¹) = 1 + (1 - Real.exp (-μ)) / μ := by
  have hV1 : expectedShortfall μ 1 + (1 + μ⁻¹) * poisTail μ 1 = 1 + (1 - Real.exp (-μ)) / μ := by
    have e1 : expectedShortfall μ 1 = poisMass μ 0 := by
      unfold expectedShortfall; simp [Finset.sum_range_succ]
    have e2 : poisTail μ 1 = 1 - poisMass μ 0 := by
      unfold poisTail; simp
    have e0 : poisMass μ 0 = Real.exp (-μ) := by unfold poisMass; simp
    rw [e1, e2, e0]
    field_simp
    ring
  unfold rankBound
  apply le_antisymm
  · rw [← hV1]
    exact ciInf_le ⟨expectedShortfall μ 1 + (1 + μ⁻¹) * poisTail μ 1,
      by rintro _ ⟨l, rfl⟩; exact anc_V_ge hμ l⟩ 1
  · rw [← hV1]
    exact le_ciInf (fun l => anc_V_ge hμ l)

lemma anc_term_nonpos {μ τ : ℝ} (hμ : 0 < μ) (hτ0 : 0 ≤ τ) (hτμ : τ ≤ μ) (k : ℕ) :
    (1 + μ⁻¹) * poisMass τ (k + 1) - poisCdf τ (k + 1) ≤ 0 := by
  rw [pc_succ]
  have h1 := pm_succ τ k
  have h2 := anc_pm_le_pc hτ0 k
  have h3 := anc_pm_nonneg hτ0 k
  have key : μ⁻¹ * poisMass τ (k + 1) ≤ poisCdf τ k := by
    have e : μ⁻¹ * poisMass τ (k + 1) = τ * poisMass τ k / (μ * ((k : ℝ) + 1)) := by
      field_simp
      linarith [h1]
    rw [e, div_le_iff₀ (by positivity)]
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    have : τ * poisMass τ k ≤ μ * poisMass τ k := mul_le_mul_of_nonneg_right hτμ h3
    have : μ * poisMass τ k ≤ μ * ((k : ℝ) + 1) * poisMass τ k := by
      have := mul_le_mul_of_nonneg_left hk hμ.le
      nlinarith
    have : μ * ((k : ℝ) + 1) * poisMass τ k ≤ μ * ((k : ℝ) + 1) * poisCdf τ k :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  nlinarith [key]

lemma anc_D_le {μ : ℝ} (hμ : 0 < μ) :
    ∀ x ∈ {x : ℝ | ∃ (m : ℕ) (τ : Fin m → ℝ), Monotone τ ∧ (∀ i, 0 ≤ τ i ∧ τ i ≤ μ) ∧
      x = ∑ i : Fin m, ((1 + μ⁻¹) * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))},
      x ≤ μ⁻¹ := by
  rintro x ⟨m, τ, _, hτ, rfl⟩
  rcases m with _ | m
  · simp only [Finset.univ_eq_empty, Finset.sum_empty]; exact (inv_pos.mpr hμ).le
  · rw [Fin.sum_univ_succ]
    have hfirst : (1 + μ⁻¹) * poisMass (τ 0) ((0 : Fin (m + 1)) : ℕ) -
        poisCdf (τ 0) ((0 : Fin (m + 1)) : ℕ) ≤ μ⁻¹ := by
      simp only [Fin.val_zero]
      rw [pc_zero]
      have e0 : poisMass (τ 0) 0 = Real.exp (-τ 0) := by unfold poisMass; simp
      rw [e0]
      have hle : Real.exp (-τ 0) ≤ 1 := by
        rw [Real.exp_le_one_iff]; linarith [(hτ 0).1]
      have hpos : 0 < μ⁻¹ := inv_pos.mpr hμ
      nlinarith [Real.exp_pos (-τ 0)]
    have hrest : ∑ i : Fin m, ((1 + μ⁻¹) * poisMass (τ i.succ) ((i.succ : Fin (m + 1)) : ℕ) -
        poisCdf (τ i.succ) ((i.succ : Fin (m + 1)) : ℕ)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      simp only [Fin.val_succ]
      exact anc_term_nonpos hμ (hτ i.succ).1 (hτ i.succ).2 i
    linarith

lemma anc_D {μ : ℝ} (hμ : 0 < μ) : agingRateSup μ (1 + μ⁻¹) = μ⁻¹ := by
  unfold agingRateSup
  apply le_antisymm
  · exact csSup_le ⟨0, anc_zero_mem μ (1 + μ⁻¹)⟩ (anc_D_le hμ)
  · apply le_csSup ⟨μ⁻¹, anc_D_le hμ⟩
    refine ⟨1, fun _ => 0, fun _ _ _ => le_refl _, fun _ => ⟨le_refl _, hμ.le⟩, ?_⟩
    simp [pc_zero, poisMass]

lemma anc_lf1 {μ : ℝ} (hμ : 0 < μ) : lossFraction μ 1 = μ / (1 + μ) := by
  unfold lossFraction poisCdf poisMass
  simp [Finset.sum_range_succ]
  have := Real.exp_pos (-μ)
  field_simp

lemma anc_lf2 {μ : ℝ} (hμ : 0 < μ) : lossFraction μ 2 = μ ^ 2 / (2 + 2 * μ + μ ^ 2) := by
  unfold lossFraction poisCdf poisMass
  simp [Finset.sum_range_succ, Nat.factorial]
  have := Real.exp_pos (-μ)
  field_simp

lemma anc_lf3 {μ : ℝ} (hμ : 0 < μ) :
    lossFraction μ 3 = μ ^ 3 / (6 + 6 * μ + 3 * μ ^ 2 + μ ^ 3) := by
  unfold lossFraction poisCdf poisMass
  simp [Finset.sum_range_succ, Nat.factorial]
  have := Real.exp_pos (-μ)
  field_simp
  ring

lemma anc_bsc (μ a : ℝ) (j : ℕ) :
    baseStockCost μ a j = (j : ℝ) - μ + (μ + a) * lossFraction μ j := by
  unfold baseStockCost meanOnHand; ring

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ : ℝ) (hμ : 0 < μ) :
    erlangNormalizer μ 1 = 1 + μ⁻¹ ∧
    calibratedPenalty μ (1 + μ⁻¹) = 1 + (2 - Real.exp (-μ)) / μ ∧
    1 + (1 - Real.exp (-μ)) / μ ≤ lowerCurve μ (1 + (2 - Real.exp (-μ)) / μ) ∧
    max (baseStockCost μ (1 + (2 - Real.exp (-μ)) / μ) 1)
        (baseStockCost μ (1 + (2 - Real.exp (-μ)) / μ) 2) <
      5 / 4 * (1 + (1 - Real.exp (-μ)) / μ) ∧
    (2 ≤ μ → baseStockCost μ (1 + (2 - Real.exp (-μ)) / μ) 3 <
      7 / 5 * (1 + (1 - Real.exp (-μ)) / μ)) := by
  have hB := anc_B hμ
  have hD := anc_D hμ
  have hη : (1 : ℝ) ≤ 1 + μ⁻¹ := by have := inv_pos.mpr hμ; linarith
  have hx0 : 0 < Real.exp (-μ) := Real.exp_pos _
  have hx1 : Real.exp (-μ) * (1 + μ) ≤ 1 := by
    have h := Real.add_one_le_exp μ
    have e : Real.exp (-μ) * Real.exp μ = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos μ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold erlangNormalizer poisCdf poisMass
    simp [Finset.sum_range_succ]
    field_simp
    ring
  · have hcal := (penalty_calibration μ hμ.le).1 (1 + μ⁻¹) hη
    rw [← hcal, hB, hD]
    field_simp
    ring
  · have hmem : min (rankBound μ (1 + μ⁻¹))
        (1 + (2 - Real.exp (-μ)) / μ - agingRateSup μ (1 + μ⁻¹)) ∈
        {x : ℝ | ∃ η : ℝ, 1 ≤ η ∧
          x = min (rankBound μ η) (1 + (2 - Real.exp (-μ)) / μ - agingRateSup μ η)} :=
      ⟨1 + μ⁻¹, hη, rfl⟩
    have hsup := le_csSup (anc_bdd μ (1 + (2 - Real.exp (-μ)) / μ)) hmem
    unfold lowerCurve
    refine le_trans (le_of_eq ?_) hsup
    rw [hB, hD]
    have e : 1 + (2 - Real.exp (-μ)) / μ - μ⁻¹ = 1 + (1 - Real.exp (-μ)) / μ := by
      field_simp; ring
    rw [e, min_self]
  · apply max_lt
    · rw [anc_bsc, anc_lf1 hμ]
      generalize Real.exp (-μ) = x at hx0 hx1 ⊢
      rw [show ((1 : ℕ) : ℝ) = 1 by norm_num]
      have e : (1 : ℝ) - μ + (μ + (1 + (2 - x) / μ)) * (μ / (1 + μ)) = (3 + μ - x) / (1 + μ) := by
        field_simp; ring
      have e2 : 5 / 4 * (1 + (1 - x) / μ) = 5 * (μ + 1 - x) / (4 * μ) := by
        field_simp; ring
      rw [e, e2, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hμ hμ, mul_pos (mul_pos hμ hμ) hμ]
    · rw [anc_bsc, anc_lf2 hμ]
      generalize Real.exp (-μ) = x at hx0 hx1 ⊢
      rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
      have e : (2 : ℝ) - μ + (μ + (1 + (2 - x) / μ)) * (μ ^ 2 / (2 + 2 * μ + μ ^ 2))
          = (4 + 4 * μ + μ ^ 2 - x * μ) / (2 + 2 * μ + μ ^ 2) := by
        field_simp; ring
      have e2 : 5 / 4 * (1 + (1 - x) / μ) = 5 * (μ + 1 - x) / (4 * μ) := by
        field_simp; ring
      rw [e, e2, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hμ hμ, mul_pos (mul_pos hμ hμ) hμ, mul_pos (mul_pos hμ hμ) (mul_pos hμ hμ)]
  · intro h2
    rw [anc_bsc, anc_lf3 hμ]
    generalize Real.exp (-μ) = x at hx0 hx1 ⊢
    rw [show ((3 : ℕ) : ℝ) = 3 by norm_num]
    have e : (3 : ℝ) - μ + (μ + (1 + (2 - x) / μ)) * (μ ^ 3 / (6 + 6 * μ + 3 * μ ^ 2 + μ ^ 3))
        = (18 + 12 * μ + 5 * μ ^ 2 + μ ^ 3 - x * μ ^ 2) / (6 + 6 * μ + 3 * μ ^ 2 + μ ^ 3) := by
      field_simp; ring
    have e2 : 7 / 5 * (1 + (1 - x) / μ) = 7 * (μ + 1 - x) / (5 * μ) := by
      field_simp; ring
    rw [e, e2, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hμ hμ, mul_pos (mul_pos hμ hμ) hμ, mul_pos (mul_pos hμ hμ) (mul_pos hμ hμ)]
