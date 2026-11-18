-- Prove2me | solution 1 for LostSalesRQ.lower_curve_properties
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T20:06:50.296783+00:00
-- url     : https://prove2.me/submissions/7e563871-ebf3-43bf-ae6b-a83836fdf527

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Theorems.Thm_LostSalesRQ_committed_supply_lower_bound
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

lemma lc_pm_nonneg {t : ℝ} (ht : 0 ≤ t) (i : ℕ) : 0 ≤ poisMass t i := by
  unfold poisMass; positivity

lemma lc_partial_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : ∑ i ∈ range n, poisMass t i ≤ 1 := by
  have h := Real.sum_le_exp_of_nonneg ht n
  have e : ∑ i ∈ range n, poisMass t i = Real.exp (-t) * ∑ i ∈ range n, t ^ i / (i.factorial : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold poisMass
    ring
  rw [e]
  have h2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos (-t)
  nlinarith

lemma lc_pc_le_one {t : ℝ} (ht : 0 ≤ t) (i : ℕ) : poisCdf t i ≤ 1 := lc_partial_le_one ht (i + 1)

lemma lc_pc_nonneg {t : ℝ} (ht : 0 ≤ t) (i : ℕ) : 0 ≤ poisCdf t i := by
  unfold poisCdf; exact Finset.sum_nonneg (fun k _ => lc_pm_nonneg ht k)

lemma lc_pm_le_pc {t : ℝ} (ht : 0 ≤ t) (i : ℕ) : poisMass t i ≤ poisCdf t i := by
  unfold poisCdf
  exact Finset.single_le_sum (f := fun k => poisMass t k)
    (fun k _ => lc_pm_nonneg ht k) (Finset.self_mem_range_succ i)

lemma lc_tail_nonneg {t : ℝ} (ht : 0 ≤ t) (l : ℕ) : 0 ≤ poisTail t l := by
  unfold poisTail; linarith [lc_partial_le_one ht l]

lemma lc_es_nonneg {t : ℝ} (ht : 0 ≤ t) (l : ℕ) : 0 ≤ expectedShortfall t l := by
  unfold expectedShortfall
  apply Finset.sum_nonneg
  intro i hi
  have hil : i ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have : (i : ℝ) ≤ l := by exact_mod_cast hil
  have := lc_pm_nonneg ht i
  have : 0 ≤ (l : ℝ) - i := by linarith
  positivity

lemma lc_V_nonneg {μ η : ℝ} (hμ : 0 ≤ μ) (hη : 0 ≤ η) (l : ℕ) :
    0 ≤ expectedShortfall μ l + η * poisTail μ l := by
  have := lc_es_nonneg hμ l
  have := lc_tail_nonneg hμ l
  positivity

lemma lc_B_bdd {μ η : ℝ} (hμ : 0 ≤ μ) (hη : 0 ≤ η) :
    BddBelow (Set.range fun l : ℕ => expectedShortfall μ l + η * poisTail μ l) :=
  ⟨0, by rintro _ ⟨l, rfl⟩; exact lc_V_nonneg hμ hη l⟩

lemma lc_B_concave {μ η₁ η₂ a b : ℝ} (hμ : 0 ≤ μ) (h1 : 0 ≤ η₁) (h2 : 0 ≤ η₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * rankBound μ η₁ + b * rankBound μ η₂ ≤ rankBound μ (a * η₁ + b * η₂) := by
  unfold rankBound
  apply le_ciInf
  intro l
  have e1 := ciInf_le (lc_B_bdd hμ h1) l
  have e2 := ciInf_le (lc_B_bdd hμ h2) l
  have e3 : expectedShortfall μ l + (a * η₁ + b * η₂) * poisTail μ l =
      a * (expectedShortfall μ l + η₁ * poisTail μ l) +
        b * (expectedShortfall μ l + η₂ * poisTail μ l) := by
    have : expectedShortfall μ l = (a + b) * expectedShortfall μ l := by rw [hab]; ring
    linear_combination this
  rw [e3]
  have := mul_le_mul_of_nonneg_left e1 ha
  have := mul_le_mul_of_nonneg_left e2 hb
  linarith

lemma lc_term_le {μ η τ : ℝ} (hμ : 0 ≤ μ) (hη : 0 ≤ η) (hτ0 : 0 ≤ τ) (hτμ : τ ≤ μ) (i : ℕ) :
    η * poisMass τ i - poisCdf τ i ≤ if i < ⌈η * μ⌉₊ + 1 then η else 0 := by
  split_ifs with h
  · have h1 := lc_pm_le_pc hτ0 i
    have h2 := lc_pc_le_one hτ0 i
    have h3 := lc_pc_nonneg hτ0 i
    have h4 := lc_pm_nonneg hτ0 i
    nlinarith
  · push Not at h
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : η * μ ≤ k := by
      have h' : ⌈η * μ⌉₊ ≤ k := by omega
      have := Nat.le_ceil (η * μ)
      have : (⌈η * μ⌉₊ : ℝ) ≤ k := by exact_mod_cast h'
      linarith
    have hs := pm_succ τ k
    have hpk := lc_pm_nonneg hτ0 k
    have hpk1 := lc_pm_nonneg hτ0 (k + 1)
    have hFk := lc_pm_le_pc hτ0 k
    have hF : poisCdf τ (k + 1) = poisCdf τ k + poisMass τ (k + 1) := pc_succ τ k
    -- (k+1) η p_{k+1} = η τ p_k ≤ η μ p_k ≤ k p_k ≤ (k+1) F_{k+1}
    have hkey : ((k : ℝ) + 1) * (η * poisMass τ (k + 1)) ≤ ((k : ℝ) + 1) * poisCdf τ (k + 1) := by
      have e : ((k : ℝ) + 1) * (η * poisMass τ (k + 1)) = η * (τ * poisMass τ k) := by
        rw [← hs]; ring
      rw [e]
      have i1 : η * (τ * poisMass τ k) ≤ η * (μ * poisMass τ k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hτμ hpk) hη
      have i2 : η * (μ * poisMass τ k) ≤ (k : ℝ) * poisMass τ k := by
        have := mul_le_mul_of_nonneg_right hk hpk
        linarith
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have i3 : (k : ℝ) * poisMass τ k ≤ ((k : ℝ) + 1) * poisCdf τ (k + 1) := by
        rw [hF]
        nlinarith
      linarith
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have := le_of_mul_le_mul_left hkey hk1
    linarith

lemma lc_sum_ite (K : ℕ) (η : ℝ) :
    ∀ m : ℕ, ∑ i ∈ range m, (if i < K then η else 0) = ((min m K : ℕ) : ℝ) * η := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : m < K
    · rw [if_pos h, min_eq_left (le_of_lt h), min_eq_left (by omega : m + 1 ≤ K)]
      push_cast; ring
    · rw [if_neg h, min_eq_right (by omega : K ≤ m), min_eq_right (by omega : K ≤ m + 1)]
      ring

lemma lc_sched_bdd {μ η : ℝ} (hμ : 0 ≤ μ) (hη : 0 ≤ η) :
    BddAbove {x : ℝ | ∃ (m : ℕ) (τ : Fin m → ℝ), Monotone τ ∧ (∀ i, 0 ≤ τ i ∧ τ i ≤ μ) ∧
      x = ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))} := by
  refine ⟨((⌈η * μ⌉₊ + 1 : ℕ) : ℝ) * η, ?_⟩
  rintro x ⟨m, τ, _, hτ, rfl⟩
  have h1 : ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ)) ≤
      ∑ i : Fin m, (if (i : ℕ) < ⌈η * μ⌉₊ + 1 then η else 0) :=
    Finset.sum_le_sum (fun i _ => lc_term_le hμ hη (hτ i).1 (hτ i).2 (i : ℕ))
  have h2 : ∑ i : Fin m, (if (i : ℕ) < ⌈η * μ⌉₊ + 1 then η else 0) =
      ∑ i ∈ range m, (if i < ⌈η * μ⌉₊ + 1 then η else 0) :=
    Fin.sum_univ_eq_sum_range (fun i => if i < ⌈η * μ⌉₊ + 1 then η else 0) m
  rw [h2, lc_sum_ite] at h1
  have h3 : ((min m (⌈η * μ⌉₊ + 1) : ℕ) : ℝ) ≤ ((⌈η * μ⌉₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast min_le_right _ _
  have := mul_le_mul_of_nonneg_right h3 hη
  linarith

lemma lc_D_convex {μ η₁ η₂ a b : ℝ} (hμ : 0 ≤ μ) (h1 : 0 ≤ η₁) (h2 : 0 ≤ η₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    agingRateSup μ (a * η₁ + b * η₂) ≤ a * agingRateSup μ η₁ + b * agingRateSup μ η₂ := by
  unfold agingRateSup
  apply csSup_le
  · refine ⟨0, 0, Fin.elim0, ?_, fun i => i.elim0, ?_⟩
    · intro x; exact x.elim0
    · simp
  · rintro x ⟨m, τ, hmono, hτ, rfl⟩
    have m1 := le_csSup (lc_sched_bdd hμ h1) ⟨m, τ, hmono, hτ, rfl⟩
    have m2 := le_csSup (lc_sched_bdd hμ h2) ⟨m, τ, hmono, hτ, rfl⟩
    have e : ∑ i : Fin m, ((a * η₁ + b * η₂) * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ)) =
        a * ∑ i : Fin m, (η₁ * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ)) +
          b * ∑ i : Fin m, (η₂ * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      linear_combination (poisCdf (τ i) (i : ℕ)) * hab
    rw [e]
    have := mul_le_mul_of_nonneg_left m1 ha
    have := mul_le_mul_of_nonneg_left m2 hb
    linarith

lemma lc_zero_mem (μ η : ℝ) :
    (0 : ℝ) ∈ {x : ℝ | ∃ (m : ℕ) (τ : Fin m → ℝ), Monotone τ ∧ (∀ i, 0 ≤ τ i ∧ τ i ≤ μ) ∧
      x = ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))} := by
  refine ⟨0, Fin.elim0, ?_, fun i => i.elim0, ?_⟩
  · intro a; exact a.elim0
  · simp

lemma lc_D_nonneg {μ η : ℝ} (hμ : 0 ≤ μ) (hη : 0 ≤ η) : 0 ≤ agingRateSup μ η :=
  le_csSup (lc_sched_bdd hμ hη) (lc_zero_mem μ η)

lemma lc_cand_bdd (μ a : ℝ) (hμ : 0 ≤ μ) :
    BddAbove {x : ℝ | ∃ η : ℝ, 1 ≤ η ∧ x = min (rankBound μ η) (a - agingRateSup μ η)} := by
  refine ⟨a, ?_⟩
  rintro x ⟨η, hη, rfl⟩
  have h1 := lc_D_nonneg hμ (by linarith : (0 : ℝ) ≤ η)
  have h2 := min_le_right (rankBound μ η) (a - agingRateSup μ η)
  linarith

lemma lc_cand_ne (μ a : ℝ) :
    {x : ℝ | ∃ η : ℝ, 1 ≤ η ∧ x = min (rankBound μ η) (a - agingRateSup μ η)}.Nonempty :=
  ⟨_, 1, le_rfl, rfl⟩

lemma lc_B_one {μ : ℝ} (hμ : 0 ≤ μ) : rankBound μ 1 = 1 := by
  unfold rankBound
  apply le_antisymm
  · have h := ciInf_le (lc_B_bdd hμ zero_le_one) 0
    have e : expectedShortfall μ 0 + 1 * poisTail μ 0 = 1 := by
      unfold expectedShortfall poisTail; simp
    linarith
  · apply le_ciInf
    intro l
    unfold expectedShortfall poisTail
    rw [Finset.sum_range_succ]
    have hle : ∑ i ∈ range l, poisMass μ i ≤
        ∑ i ∈ range l, ((l : ℝ) - (i : ℝ)) * poisMass μ i := by
      apply Finset.sum_le_sum
      intro i hi
      have hil : i < l := Finset.mem_range.mp hi
      have h1 : (1 : ℝ) ≤ (l : ℝ) - (i : ℝ) := by
        have : (i : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hil
        linarith
      have hp := lc_pm_nonneg hμ i
      nlinarith
    simp only [sub_self, zero_mul, add_zero]
    linarith

lemma lc_D_one {μ : ℝ} (hμ : 0 ≤ μ) : agingRateSup μ 1 = 0 := by
  apply le_antisymm
  · unfold agingRateSup
    apply csSup_le ⟨0, lc_zero_mem μ 1⟩
    rintro x ⟨m, τ, _, hτ, rfl⟩
    apply Finset.sum_nonpos
    intro i _
    have := lc_pm_le_pc (hτ i).1 (i : ℕ)
    linarith
  · exact lc_D_nonneg hμ zero_le_one

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ : ℝ) (hμ : 0 ≤ μ) :
    (∀ a : ℝ, 0 ≤ a → ENNReal.ofReal (lowerCurve μ a) ≤ OPTk μ a 0) ∧
    (∀ η : ℝ, 1 ≤ η → rankBound μ η ≤ lowerCurve μ (calibratedPenalty μ η)) ∧
    ConcaveOn ℝ (Set.Ici 0) (lowerCurve μ) ∧
    MonotoneOn (lowerCurve μ) (Set.Ici 0) ∧
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → |lowerCurve μ a - lowerCurve μ b| ≤ |a - b|) ∧
    (∀ a : ℝ, 0 ≤ a → min 1 a ≤ lowerCurve μ a ∧ lowerCurve μ a ≤ a) := by
  -- one-sided Lipschitz bound, valid for all penalties
  have hlip : ∀ a b : ℝ, lowerCurve μ a ≤ lowerCurve μ b + |a - b| := by
    intro a b
    unfold lowerCurve
    apply csSup_le (lc_cand_ne μ a)
    rintro x ⟨η, hη, rfl⟩
    have hmem := le_csSup (lc_cand_bdd μ b hμ) ⟨η, hη, rfl⟩
    have h1 : a ≤ b + |a - b| := by
      have := le_abs_self (a - b); linarith
    have h2 : min (rankBound μ η) (a - agingRateSup μ η) ≤
        min (rankBound μ η) (b - agingRateSup μ η) + |a - b| := by
      rcases le_total (rankBound μ η) (b - agingRateSup μ η) with h | h
      · rw [min_eq_left h]
        have := min_le_left (rankBound μ η) (a - agingRateSup μ η)
        have := abs_nonneg (a - b)
        linarith
      · rw [min_eq_right h]
        have := min_le_right (rankBound μ η) (a - agingRateSup μ η)
        linarith
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- part 1: below the optimum
    intro a ha
    by_cases htop : OPTk μ a 0 = ⊤
    · rw [htop]; exact le_top
    · have hle : lowerCurve μ a ≤ (OPTk μ a 0).toReal := by
        unfold lowerCurve
        apply csSup_le (lc_cand_ne μ a)
        rintro x ⟨η, hη, rfl⟩
        have h := committed_supply_lower_bound μ a η hμ ha hη
        rcases le_or_gt (min (rankBound μ η) (a - agingRateSup μ η)) 0 with h0 | h0
        · exact h0.trans ENNReal.toReal_nonneg
        · rw [← ENNReal.ofReal_toReal htop] at h
          exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h
      calc ENNReal.ofReal (lowerCurve μ a) ≤ ENNReal.ofReal (OPTk μ a 0).toReal :=
            ENNReal.ofReal_le_ofReal hle
        _ = OPTk μ a 0 := ENNReal.ofReal_toReal htop
  · -- part 2: the calibrated penalty
    intro η hη
    have hcal := (penalty_calibration μ hμ).1 η hη
    have hmem := le_csSup (lc_cand_bdd μ (calibratedPenalty μ η) hμ) ⟨η, hη, rfl⟩
    have e : calibratedPenalty μ η - agingRateSup μ η = rankBound μ η := by linarith
    rw [e, min_self] at hmem
    exact hmem
  · -- part 3: concavity
    refine ⟨convex_Ici 0, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨m1, ⟨η₁, hη₁, rfl⟩, hm1⟩ :=
      exists_lt_of_lt_csSup (lc_cand_ne μ x)
        (by linarith : lowerCurve μ x - ε / 2 < lowerCurve μ x)
    obtain ⟨m2, ⟨η₂, hη₂, rfl⟩, hm2⟩ :=
      exists_lt_of_lt_csSup (lc_cand_ne μ y)
        (by linarith : lowerCurve μ y - ε / 2 < lowerCurve μ y)
    have hη : 1 ≤ a * η₁ + b * η₂ := by nlinarith
    have hmem : min (rankBound μ (a * η₁ + b * η₂))
        (a * x + b * y - agingRateSup μ (a * η₁ + b * η₂)) ≤ lowerCurve μ (a * x + b * y) :=
      le_csSup (lc_cand_bdd μ (a * x + b * y) hμ) ⟨a * η₁ + b * η₂, hη, rfl⟩
    have hB := lc_B_concave (μ := μ) hμ (by linarith : (0 : ℝ) ≤ η₁) (by linarith : (0 : ℝ) ≤ η₂)
      ha hb hab
    have hD := lc_D_convex (μ := μ) hμ (by linarith : (0 : ℝ) ≤ η₁) (by linarith : (0 : ℝ) ≤ η₂)
      ha hb hab
    have hmin : a * min (rankBound μ η₁) (x - agingRateSup μ η₁) +
        b * min (rankBound μ η₂) (y - agingRateSup μ η₂) ≤
        min (rankBound μ (a * η₁ + b * η₂)) (a * x + b * y - agingRateSup μ (a * η₁ + b * η₂)) := by
      apply le_min
      · have := mul_le_mul_of_nonneg_left (min_le_left (rankBound μ η₁) (x - agingRateSup μ η₁)) ha
        have := mul_le_mul_of_nonneg_left (min_le_left (rankBound μ η₂) (y - agingRateSup μ η₂)) hb
        linarith
      · have := mul_le_mul_of_nonneg_left (min_le_right (rankBound μ η₁) (x - agingRateSup μ η₁)) ha
        have := mul_le_mul_of_nonneg_left (min_le_right (rankBound μ η₂) (y - agingRateSup μ η₂)) hb
        nlinarith
    have h1 := mul_le_mul_of_nonneg_left hm1.le ha
    have h2 := mul_le_mul_of_nonneg_left hm2.le hb
    have hε2 : a * (ε / 2) + b * (ε / 2) = ε / 2 := by rw [← add_mul, hab]; ring
    have e1 : a * (lowerCurve μ x - ε / 2) = a * lowerCurve μ x - a * (ε / 2) := by ring
    have e2 : b * (lowerCurve μ y - ε / 2) = b * lowerCurve μ y - b * (ε / 2) := by ring
    linarith
  · -- part 4: monotone
    intro a _ b _ hab
    have := hlip a b
    unfold lowerCurve
    apply csSup_le (lc_cand_ne μ a)
    rintro x ⟨η, hη, rfl⟩
    have hmem := le_csSup (lc_cand_bdd μ b hμ) ⟨η, hη, rfl⟩
    have : min (rankBound μ η) (a - agingRateSup μ η) ≤ min (rankBound μ η) (b - agingRateSup μ η) :=
      min_le_min le_rfl (by linarith)
    linarith
  · -- part 5: 1-Lipschitz
    intro a b _ _
    rw [abs_le]
    have h1 := hlip a b
    have h2 := hlip b a
    rw [abs_sub_comm] at h2
    constructor <;> linarith
  · -- part 6: elementary bounds
    intro a ha
    constructor
    · have hmem := le_csSup (lc_cand_bdd μ a hμ) ⟨1, le_rfl, rfl⟩
      rw [lc_B_one hμ, lc_D_one hμ, sub_zero] at hmem
      exact hmem
    · unfold lowerCurve
      apply csSup_le (lc_cand_ne μ a)
      rintro x ⟨η, hη, rfl⟩
      have := lc_D_nonneg hμ (by linarith : (0 : ℝ) ≤ η)
      have := min_le_right (rankBound μ η) (a - agingRateSup μ η)
      linarith
