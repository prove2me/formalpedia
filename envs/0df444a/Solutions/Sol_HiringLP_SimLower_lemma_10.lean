-- Prove2me | solution 1 for HiringLP.SimLower.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:23:43.924034+00:00
-- url     : https://prove2.me/submissions/b7e7535e-a937-448e-a306-cc54debbb69e

import Mathlib
import Definitions.Def_HiringLP_SimLower_Model
import Definitions.Def_HiringLP_SimLower_LP

set_option autoImplicit false
open HiringLP.SimLower Finset

theorem setProb_eq_HSL {n : ℕ} (q : Fin n → ℝ) (A : Finset (Fin n)) :
    setProb q A = (∏ i ∈ A, q i) * ∏ i ∈ univ \ A, (1 - q i) := by
  unfold setProb
  rw [Finset.prod_ite]
  have h1 : (univ.filter fun i : Fin n => i ∈ A) = A := by ext i; simp
  have h2 : (univ.filter fun i : Fin n => ¬ i ∈ A) = univ \ A := by ext i; simp
  rw [h1, h2]

theorem sum_one_HSL {n : ℕ} (q : Fin n → ℝ) : ∑ A : Finset (Fin n), setProb q A = 1 := by
  have := Finset.prod_add q (fun i => 1 - q i) univ
  simp only [add_sub_cancel, Finset.prod_const_one] at this
  rw [Finset.powerset_univ] at this
  refine Eq.trans (sum_congr rfl fun A _ => setProb_eq_HSL q A) this.symm

theorem sum_mem_HSL {n : ℕ} (q : Fin n → ℝ) (i : Fin n) :
    ∑ A : Finset (Fin n), setProb q A * (if i ∈ A then 1 else 0) = q i := by
  have := Finset.prod_add q (fun j => if j = i then 0 else 1 - q j) univ
  have e : ∏ j : Fin n, (q j + if j = i then 0 else 1 - q j) = q i := by
    have : ∀ j : Fin n, (q j + if j = i then 0 else 1 - q j) = if j = i then q i else 1 := by
      intro j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    simp_rw [this]
    simp
  rw [e, Finset.powerset_univ] at this
  refine Eq.trans ?_ this.symm
  apply sum_congr rfl
  intro A _
  rw [setProb_eq_HSL]
  by_cases hi : i ∈ A
  · simp only [hi, if_true, mul_one]
    congr 1
    apply prod_congr rfl
    intro j hj
    have : j ≠ i := by
      intro h; subst h; simp [hi] at hj
    simp [this]
  · simp only [hi, if_false, mul_zero]
    symm
    rw [mul_eq_zero]
    right
    apply prod_eq_zero (i := i)
    · simp [hi]
    · simp

theorem lin_HSL {n : ℕ} (q : Fin n → ℝ) (c : Fin n → ℝ) :
    ∑ A : Finset (Fin n), setProb q A * (∑ i ∈ A, c i) = ∑ i, c i * q i := by
  have h1 : ∀ A : Finset (Fin n), ∑ i ∈ A, c i = ∑ i, c i * (if i ∈ A then 1 else 0) := by
    intro A
    simp [mul_ite, Finset.sum_ite_mem]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  have : ∀ A : Finset (Fin n), setProb q A * (c i * (if i ∈ A then 1 else 0)) =
      c i * (setProb q A * (if i ∈ A then 1 else 0)) := by intro A; ring
  simp_rw [this]
  rw [← Finset.mul_sum, sum_mem_HSL]

theorem setProb_nonneg_HSL {n : ℕ} (q : Fin n → ℝ) (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1)
    (A : Finset (Fin n)) : 0 ≤ setProb q A := by
  unfold setProb
  apply prod_nonneg
  intro i _
  split_ifs
  · exact h0 i
  · linarith [h1 i]

theorem reward_le_HSL {n : ℕ} (I : SimInstance n) (hI : I.Valid) (y : Fin n → ℝ)
    (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    rewardIndep I y ≤ ∑ i, I.v i * I.p i * y i - max (∑ i, I.p i * y i - I.k) 0 := by
  set q : Fin n → ℝ := fun i => y i * I.p i with hq
  have hq0 : ∀ i, 0 ≤ q i := fun i => mul_nonneg (hy i).1 (hI.2.2.1 i).1
  have hq1 : ∀ i, q i ≤ 1 := fun i =>
    calc q i ≤ 1 * 1 := mul_le_mul (hy i).2 (hI.2.2.1 i).2 (hI.2.2.1 i).1 zero_le_one
      _ = 1 := one_mul 1
  set μ : ℝ := ∑ i, q i with hμ
  have hw0 := setProb_nonneg_HSL q hq0 hq1
  have hcard : ∑ A : Finset (Fin n), setProb q A * (A.card : ℝ) = μ := by
    have := lin_HSL q (fun _ => (1 : ℝ))
    simp only [sum_const, nsmul_eq_mul, mul_one, one_mul] at this
    simpa using this
  have hv : ∑ A : Finset (Fin n), setProb q A * (∑ i ∈ A, I.v i) = ∑ i, I.v i * q i :=
    lin_HSL q I.v
  have hm : ∑ A : Finset (Fin n), setProb q A * max ((A.card : ℝ) - I.k) 0 ≥ max (μ - I.k) 0 := by
    have hpt : ∀ A : Finset (Fin n), max ((A.card : ℝ) - I.k) 0 ≥
        max (μ - I.k) 0 + (if (I.k : ℝ) < μ then 1 else 0) * ((A.card : ℝ) - μ) := by
      intro A
      by_cases h : (I.k : ℝ) < μ
      · simp only [h, if_true, one_mul]
        rw [max_eq_left (show (0 : ℝ) ≤ μ - I.k by linarith)]
        have := le_max_left ((A.card : ℝ) - I.k) 0
        linarith
      · simp only [h, if_false, zero_mul, add_zero]
        rw [max_eq_right (show μ - (I.k : ℝ) ≤ 0 by linarith [not_lt.1 h])]
        exact le_max_right _ _
    calc ∑ A : Finset (Fin n), setProb q A * max ((A.card : ℝ) - I.k) 0
        ≥ ∑ A : Finset (Fin n), setProb q A *
            (max (μ - I.k) 0 + (if (I.k : ℝ) < μ then 1 else 0) * ((A.card : ℝ) - μ)) := by
          apply sum_le_sum
          intro A _
          exact mul_le_mul_of_nonneg_left (hpt A) (hw0 A)
      _ = max (μ - I.k) 0 := by
          have : ∀ A : Finset (Fin n), setProb q A *
              (max (μ - I.k) 0 + (if (I.k : ℝ) < μ then 1 else 0) * ((A.card : ℝ) - μ)) =
              max (μ - I.k) 0 * setProb q A +
              (if (I.k : ℝ) < μ then 1 else 0) * (setProb q A * (A.card : ℝ)) -
              (if (I.k : ℝ) < μ then 1 else 0) * μ * setProb q A := by
            intro A; ring
          simp_rw [this]
          rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, sum_one_HSL, hcard]
          ring
  unfold rewardIndep
  have : ∑ A : Finset (Fin n), setProb (fun i => y i * I.p i) A *
      ((∑ i ∈ A, I.v i) - max ((A.card : ℝ) - I.k) 0) =
      ∑ A : Finset (Fin n), setProb q A * (∑ i ∈ A, I.v i) -
      ∑ A : Finset (Fin n), setProb q A * max ((A.card : ℝ) - I.k) 0 := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro A _
    simp only [hq]
    ring
  rw [this, hv]
  have e1 : ∑ i, I.v i * q i = ∑ i, I.v i * I.p i * y i := by
    apply sum_congr rfl; intro i _; simp only [hq]; ring
  have e2 : μ = ∑ i, I.p i * y i := by
    simp only [hμ, hq]; apply sum_congr rfl; intro i _; ring
  rw [e1, ← e2]
  linarith

theorem solution {n : ℕ} (I : SimInstance n) (hI : I.Valid) :
    OPTsim I ≤ LPsim I := by
  unfold OPTsim
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨S, rfl⟩
  set y : Fin n → ℝ := fun i => if i ∈ S then 1 else 0 with hy
  have hy01 : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := by
    intro i; by_cases h : i ∈ S <;> simp [hy, h]
  have hle := reward_le_HSL I hI y hy01
  set z : ℝ := -(max (∑ i, I.p i * y i - I.k) 0) with hz
  have hfeas : LPFeasible I y z := by
    refine ⟨hy01, ?_, ?_⟩
    · simp only [hz]; have := le_max_right (∑ i, I.p i * y i - (I.k : ℝ)) 0; linarith
    · simp only [hz]; have := le_max_left (∑ i, I.p i * y i - (I.k : ℝ)) 0; linarith
  have hobj : reward I S ≤ LPobj I y z := by
    unfold reward LPobj
    rw [← hy]
    simp only [hz]
    linarith
  refine hobj.trans ?_
  apply le_csSup
  · refine ⟨∑ i, I.v i * I.p i, ?_⟩
    rintro _ ⟨y', z', hf, rfl⟩
    unfold LPobj
    have : ∑ i, I.v i * I.p i * y' i ≤ ∑ i, I.v i * I.p i := by
      apply sum_le_sum
      intro i _
      have h1 := hI.2.2.2.1 i
      have h2 := (hI.2.2.1 i).1
      have h3 := (hf.1 i).2
      nlinarith [mul_nonneg h1 h2]
    linarith [hf.2.1]
  · exact ⟨y, z, hfeas, rfl⟩
