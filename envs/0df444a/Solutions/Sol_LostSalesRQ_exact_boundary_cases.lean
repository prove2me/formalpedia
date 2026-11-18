-- Prove2me | solution 1 for LostSalesRQ.exact_boundary_cases
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T21:03:52.048279+00:00
-- url     : https://prove2.me/submissions/99a4ebc2-38a0-4c8e-94f8-67995ebb03f2

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Theorems.Thm_LostSalesRQ_lower_curve_properties
import Theorems.Thm_LostSalesRQ_exact_base_stock_cost
import Theorems.Thm_LostSalesRQ_rq_policy_exists
import Theorems.Thm_LostSalesRQ_tightness_bounds

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

lemma ebc_pm_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : 0 ≤ poisMass μ j := by
  unfold poisMass; positivity

lemma ebc_pc_pos {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : 0 < poisCdf μ j := by
  unfold poisCdf
  rw [Finset.sum_range_succ']
  have h0 : 0 < poisMass μ 0 := by unfold poisMass; simp [Real.exp_pos]
  have : 0 ≤ ∑ i ∈ range j, poisMass μ (i + 1) :=
    Finset.sum_nonneg (fun i _ => ebc_pm_nonneg hμ (i + 1))
  linarith

lemma ebc_lf_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : 0 ≤ lossFraction μ j :=
  div_nonneg (ebc_pm_nonneg hμ j) (ebc_pc_pos hμ j).le

lemma ebc_pm_le_pc {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : poisMass μ j ≤ poisCdf μ j := by
  unfold poisCdf
  rw [Finset.sum_range_succ]
  have : 0 ≤ ∑ i ∈ range j, poisMass μ i := Finset.sum_nonneg (fun i _ => ebc_pm_nonneg hμ i)
  linarith

lemma ebc_lf_le_one {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : lossFraction μ j ≤ 1 := by
  unfold lossFraction
  rw [div_le_one (ebc_pc_pos hμ j)]
  exact ebc_pm_le_pc hμ j

/-- H_j ≥ 1 - e_j: mean on-hand stock dominates the probability of positive stock. -/
lemma ebc_moh_ge {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : 1 - lossFraction μ j ≤ meanOnHand μ j := by
  have hF := ebc_pc_pos hμ j
  have hid : meanOnHand μ j * poisCdf μ j =
      ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
    have hs := sum_i_pm μ j
    have e : ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i =
        (j : ℝ) * poisCdf μ j - ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i := by
      unfold poisCdf
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e, hs]
    unfold meanOnHand lossFraction
    field_simp
    ring
  have hge : poisCdf μ j - poisMass μ j ≤
      ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
    unfold poisCdf
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [sub_self, zero_mul, add_zero, add_sub_cancel_right]
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i < j := Finset.mem_range.mp hi
    have h1 : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
      have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hi'
      linarith
    have := ebc_pm_nonneg hμ i
    nlinarith
  have : (1 - lossFraction μ j) * poisCdf μ j = poisCdf μ j - poisMass μ j := by
    unfold lossFraction; field_simp
  have key : (1 - lossFraction μ j) * poisCdf μ j ≤ meanOnHand μ j * poisCdf μ j := by
    rw [this, hid]; exact hge
  exact le_of_mul_le_mul_right key hF

lemma ebc_L0 {μ : ℝ} (hμ : 0 ≤ μ) (a : ℝ) : baseStockCost μ a 0 = a := by
  have hF := ebc_pc_pos hμ 0
  have hl : lossFraction μ 0 = 1 := by
    unfold lossFraction; rw [pc_zero] at hF ⊢; field_simp
  unfold baseStockCost meanOnHand; rw [hl]; push_cast; ring

lemma ebc_L_ge {μ a : ℝ} (hμ : 0 ≤ μ) (ha1 : a ≤ 1) (j : ℕ) : a ≤ baseStockCost μ a j := by
  have h1 := ebc_moh_ge hμ j
  have h2 := ebc_lf_le_one hμ j
  unfold baseStockCost
  nlinarith

lemma ebc_pm_zero_zero : poisMass 0 0 = 1 := by unfold poisMass; simp

lemma ebc_pm_zero_succ (j : ℕ) : poisMass 0 (j + 1) = 0 := by unfold poisMass; simp

lemma ebc_pc_zero (j : ℕ) : poisCdf 0 j = 1 := by
  induction j with
  | zero => rw [pc_zero, ebc_pm_zero_zero]
  | succ n ih => rw [pc_succ, ih, ebc_pm_zero_succ]; ring

lemma ebc_L_zero_succ (a : ℝ) (j : ℕ) : baseStockCost 0 a (j + 1) = (j : ℝ) + 1 := by
  unfold baseStockCost meanOnHand lossFraction
  rw [ebc_pm_zero_succ, ebc_pc_zero]; push_cast; ring

lemma ebc_min_eq {μ a : ℝ} (hμ : 0 ≤ μ) (ha1 : a ≤ 1) : minBaseStockCost μ a = a := by
  unfold minBaseStockCost
  apply le_antisymm
  · have := ciInf_le ⟨a, by rintro _ ⟨j, rfl⟩; exact ebc_L_ge hμ ha1 j⟩ 0
    rw [ebc_L0 hμ] at this; exact this
  · exact le_ciInf (fun j => ebc_L_ge hμ ha1 j)

lemma ebc_min_zero {a : ℝ} (ha : 0 ≤ a) : minBaseStockCost 0 a = min a 1 := by
  unfold minBaseStockCost
  have hlow : ∀ j : ℕ, min a 1 ≤ baseStockCost 0 a j := by
    intro j
    cases j with
    | zero => rw [ebc_L0 le_rfl]; exact min_le_left _ _
    | succ n =>
      rw [ebc_L_zero_succ]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have := min_le_right a 1
      linarith
  apply le_antisymm
  · have hb : BddBelow (Set.range fun j => baseStockCost 0 a j) :=
      ⟨min a 1, by rintro _ ⟨j, rfl⟩; exact hlow j⟩
    rcases le_total a 1 with h | h
    · rw [min_eq_left h]
      have := ciInf_le hb 0
      rw [ebc_L0 le_rfl] at this; exact this
    · rw [min_eq_right h]
      have := ciInf_le hb 1
      rw [show (1 : ℕ) = 0 + 1 from rfl, ebc_L_zero_succ] at this
      simpa using this
  · exact le_ciInf hlow

/-- Some demand environment of unit rate exists (it is implied by the finite tightness bound). -/
lemma ebc_space_nonempty : Nonempty (DemandSpace 1) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have h := (tightness_bounds).1 0 1 le_rfl (by norm_num)
  have htop : OPTk 0 1 0 = ⊤ := by
    unfold OPTk OPT
    exact iInf_of_empty _
  rw [htop] at h
  exact ENNReal.ofReal_ne_top (top_le_iff.mp h)

lemma ebc_opt_le_noorder (μ a : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) :
    OPTk μ a 0 ≤ ENNReal.ofReal a := by
  obtain ⟨S⟩ := ebc_space_nonempty
  have h := (exact_base_stock_cost μ a hμ ha S).1
  unfold OPTk OPT
  rw [← h]
  exact iInf₂_le S (noOrderPolicy S)

lemma ebc_opt_le_bs (μ a : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (j : ℕ) (hj : 1 ≤ j) :
    OPTk μ a 0 ≤ ENNReal.ofReal (baseStockCost μ a j) := by
  obtain ⟨S⟩ := ebc_space_nonempty
  obtain ⟨π, hπ⟩ := rq_policy_exists 1 μ zero_le_one hμ S (j - 1) 1 le_rfl
  have h := (exact_base_stock_cost μ a hμ ha S).2 j hj π hπ
  unfold OPTk OPT
  rw [← h]
  exact iInf₂_le S π

end LostSalesRQ

open LostSalesRQ in
theorem solution :
    (∀ μ a : ℝ, 0 ≤ μ → 0 ≤ a → a ≤ 1 →
      lowerCurve μ a = a ∧ OPTk μ a 0 = ENNReal.ofReal a ∧ minBaseStockCost μ a = a) ∧
    (∀ a : ℝ, 0 ≤ a →
      lowerCurve 0 a = min a 1 ∧ minBaseStockCost 0 a = min a 1 ∧
        OPTk 0 a 0 = ENNReal.ofReal (min a 1)) := by
  refine ⟨fun μ a hμ ha ha1 => ?_, fun a ha => ?_⟩
  · have hlc := lower_curve_properties μ hμ
    have h6 := hlc.2.2.2.2.2 a ha
    have hL : lowerCurve μ a = a := by
      rw [min_eq_right ha1] at h6
      exact le_antisymm h6.2 h6.1
    refine ⟨hL, ?_, ebc_min_eq hμ ha1⟩
    apply le_antisymm (ebc_opt_le_noorder μ a hμ ha)
    have := hlc.1 a ha
    rw [hL] at this
    exact this
  · have hlc := lower_curve_properties 0 le_rfl
    have h6 := hlc.2.2.2.2.2 a ha
    have hopt1 : OPTk 0 a 0 ≤ ENNReal.ofReal 1 := by
      have := ebc_opt_le_bs 0 a le_rfl ha 1 le_rfl
      rwa [show (1 : ℕ) = 0 + 1 from rfl, ebc_L_zero_succ, Nat.cast_zero, zero_add] at this
    have hopt0 := ebc_opt_le_noorder 0 a le_rfl ha
    have hlow := hlc.1 a ha
    have hL1 : lowerCurve 0 a ≤ 1 := by
      have := le_trans hlow hopt1
      exact (ENNReal.ofReal_le_ofReal_iff zero_le_one).mp this
    have hL : lowerCurve 0 a = min a 1 := by
      apply le_antisymm (le_min h6.2 hL1)
      rw [min_comm]; exact h6.1
    refine ⟨hL, ebc_min_zero ha, ?_⟩
    apply le_antisymm
    · rcases le_total a 1 with h | h
      · rw [min_eq_left h]; exact hopt0
      · rw [min_eq_right h]; exact hopt1
    · rw [← hL]; exact hlow
