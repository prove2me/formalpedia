-- Prove2me | solution 1 for MDPFinance.ConsumptionInvestment.regime_monotone_fraction
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T20:06:35.900849+00:00
-- url     : https://prove2.me/submissions/1b560553-09f5-451e-a507-cb31265f1140

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_StochasticOrders

open MeasureTheory ProbabilityTheory MDPFinance.ConsumptionInvestment

namespace RMFCex

/-- `Q_j = ⅗ δ_{-1} + ⅖ δ_1` (mean `-1/5`). -/
noncomputable def Qj : Measure ℝ :=
  ENNReal.ofReal (3 / 5) • Measure.dirac (-1) + ENNReal.ofReal (2 / 5) • Measure.dirac 1

/-- `Q_k = ½ δ_{-1} + ⅕ δ_0 + ³⁄₁₀ δ_1`: a mean-preserving contraction of `Q_j`. -/
noncomputable def Qk : Measure ℝ :=
  ENNReal.ofReal (1 / 2) • Measure.dirac (-1) + ENNReal.ofReal (1 / 5) • Measure.dirac 0 +
    ENNReal.ofReal (3 / 10) • Measure.dirac 1

instance : IsProbabilityMeasure Qj := by
  constructor
  simp only [Qj, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num

instance : IsProbabilityMeasure Qk := by
  constructor
  simp only [Qk, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num

theorem int_dirac (f : ℝ → ℝ) (a : ℝ) : Integrable f (Measure.dirac a) :=
  (integrable_const (f a)).congr (ae_eq_dirac f).symm

theorem int_sm (f : ℝ → ℝ) (c a : ℝ) : Integrable f (ENNReal.ofReal c • Measure.dirac a) :=
  (int_dirac f a).smul_measure ENNReal.ofReal_ne_top

theorem integral_sm (f : ℝ → ℝ) (c a : ℝ) (hc : 0 ≤ c) :
    ∫ y, f y ∂(ENNReal.ofReal c • Measure.dirac a) = c * f a := by
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hc, smul_eq_mul]

theorem int_Qj (f : ℝ → ℝ) : Integrable f Qj := (int_sm f _ _).add_measure (int_sm f _ _)

theorem int_Qk (f : ℝ → ℝ) : Integrable f Qk :=
  ((int_sm f _ _).add_measure (int_sm f _ _)).add_measure (int_sm f _ _)

theorem integral_Qj (f : ℝ → ℝ) : ∫ y, f y ∂Qj = 3 / 5 * f (-1) + 2 / 5 * f 1 := by
  rw [Qj, integral_add_measure (int_sm f _ _) (int_sm f _ _), integral_sm _ _ _ (by norm_num),
    integral_sm _ _ _ (by norm_num)]

theorem integral_Qk (f : ℝ → ℝ) :
    ∫ y, f y ∂Qk = 1 / 2 * f (-1) + 1 / 5 * f 0 + 3 / 10 * f 1 := by
  rw [Qk, integral_add_measure ((int_sm f _ _).add_measure (int_sm f _ _)) (int_sm f _ _),
    integral_add_measure (int_sm f _ _) (int_sm f _ _), integral_sm _ _ _ (by norm_num),
    integral_sm _ _ _ (by norm_num), integral_sm _ _ _ (by norm_num)]

theorem ae_Qj (p : ℝ → Prop) : (∀ᵐ y ∂Qj, p y) ↔ p (-1) ∧ p 1 := by
  rw [ae_iff, Qj, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply]
  by_cases h1 : p (-1) <;> by_cases h2 : p 1 <;> simp [h1, h2]

theorem ae_Qk (p : ℝ → Prop) : (∀ᵐ y ∂Qk, p y) ↔ p (-1) ∧ p 0 ∧ p 1 := by
  rw [ae_iff, Qk, Measure.add_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.smul_apply, Measure.dirac_apply, Measure.dirac_apply, Measure.dirac_apply]
  by_cases h1 : p (-1) <;> by_cases h2 : p 0 <;> by_cases h3 : p 1 <;> simp [h1, h2, h3]

theorem NAj : ¬ ∃ a : ℝ, (∀ᵐ y ∂Qj, 0 ≤ a * y) ∧ Qj {y | 0 < a * y} > 0 := by
  rintro ⟨a, ha, hpos⟩
  rw [ae_Qj] at ha
  have : a = 0 := by linarith [ha.1, ha.2]
  subst this
  simp at hpos

theorem NAk : ¬ ∃ a : ℝ, (∀ᵐ y ∂Qk, 0 ≤ a * y) ∧ Qk {y | 0 < a * y} > 0 := by
  rintro ⟨a, ha, hpos⟩
  rw [ae_Qk] at ha
  have : a = 0 := by linarith [ha.1, ha.2.2]
  subst this
  simp at hpos

theorem nrj : Qj {y | y ≠ 0} ≠ 0 := by
  rw [Qj, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]
  simp

theorem nrk : Qk {y | y ≠ 0} ≠ 0 := by
  rw [Qk, Measure.add_apply, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]
  simp

theorem Aj : Set.Icc (-1 : ℝ) 1 = {α | ∀ᵐ y ∂Qj, 0 ≤ 1 + α * y} := by
  ext α; simp only [Set.mem_Icc, Set.mem_setOf_eq, ae_Qj]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem Ak : Set.Icc (-1 : ℝ) 1 = {α | ∀ᵐ y ∂Qk, 0 ≤ 1 + α * y} := by
  ext α; simp only [Set.mem_Icc, Set.mem_setOf_eq, ae_Qk]
  constructor
  · intro h; exact ⟨by linarith [h.1, h.2], by norm_num, by linarith [h.1, h.2]⟩
  · intro h; constructor <;> linarith [h.1, h.2.2]

theorem icv : LEIncreasingConcaveOrder Qj Qk := by
  intro f _ hc _ _
  rw [integral_Qj, integral_Qk]
  have := hc.2 (Set.mem_univ (-1 : ℝ)) (Set.mem_univ (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at this
  norm_num at this
  linarith

theorem sq_half (x : ℝ) : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm

theorem optj : ∀ α ∈ Set.Icc (-1 : ℝ) 1, ∫ y, (1 + α * y) ^ (1 / 2 : ℝ) ∂Qj ≤
    ∫ y, (1 + (-5 / 13) * y) ^ (1 / 2 : ℝ) ∂Qj := by
  intro α hα
  rw [integral_Qj, integral_Qj]
  simp only [sq_half]
  obtain ⟨h1, h2⟩ := hα
  set s := Real.sqrt (1 + α * -1)
  set t := Real.sqrt (1 + α * 1)
  have hs : s ^ 2 = 1 + α * -1 := Real.sq_sqrt (by linarith)
  have ht : t ^ 2 = 1 + α * 1 := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  set S := Real.sqrt (1 + (-5 / 13 : ℝ) * -1)
  set T := Real.sqrt (1 + (-5 / 13 : ℝ) * 1)
  have hS : S ^ 2 = 18 / 13 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hT : T ^ 2 = 8 / 13 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hST : S = 3 / 2 * T := by
    have : S ^ 2 = (3 / 2 * T) ^ 2 := by rw [hS, mul_pow, hT]; norm_num
    exact (pow_left_inj₀ hS0 (by positivity) two_ne_zero).mp this
  have hL : (3 / 5 * s + 2 / 5 * t) ^ 2 ≤ (3 / 5 * S + 2 / 5 * T) ^ 2 := by
    rw [hST]
    nlinarith [sq_nonneg (2 / 5 * s - 3 / 5 * t)]
  nlinarith [sq_nonneg (3 / 5 * s + 2 / 5 * t - (3 / 5 * S + 2 / 5 * T))]

theorem optk : ∀ α ∈ Set.Icc (-1 : ℝ) 1, ∫ y, (1 + α * y) ^ (1 / 2 : ℝ) ∂Qk ≤
    ∫ y, (1 + (-8 / 17) * y) ^ (1 / 2 : ℝ) ∂Qk := by
  intro α hα
  rw [integral_Qk, integral_Qk]
  simp only [sq_half, mul_zero, add_zero, Real.sqrt_one]
  obtain ⟨h1, h2⟩ := hα
  set s := Real.sqrt (1 + α * -1)
  set t := Real.sqrt (1 + α * 1)
  have hs : s ^ 2 = 1 + α * -1 := Real.sq_sqrt (by linarith)
  have ht : t ^ 2 = 1 + α * 1 := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  set S := Real.sqrt (1 + (-8 / 17 : ℝ) * -1)
  set T := Real.sqrt (1 + (-8 / 17 : ℝ) * 1)
  have hS : S ^ 2 = 25 / 17 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hT : T ^ 2 = 9 / 17 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hST : S = 5 / 3 * T := by
    have : S ^ 2 = (5 / 3 * T) ^ 2 := by rw [hS, mul_pow, hT]; norm_num
    exact (pow_left_inj₀ hS0 (by positivity) two_ne_zero).mp this
  have hL : (1 / 2 * s + 3 / 10 * t) ^ 2 ≤ (1 / 2 * S + 3 / 10 * T) ^ 2 := by
    rw [hST]
    nlinarith [sq_nonneg (3 / 10 * s - 1 / 2 * t)]
  nlinarith [sq_nonneg (1 / 2 * s + 3 / 10 * t - (1 / 2 * S + 3 / 10 * T))]

end RMFCex

open RMFCex in
theorem solution : ¬ (∀ (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Qj Qk : Measure ℝ) [IsProbabilityMeasure Qj] [IsProbabilityMeasure Qk]
    (hNAj : ¬ ∃ a : ℝ, (∀ᵐ y ∂Qj, 0 ≤ a * y) ∧ Qj {y | 0 < a * y} > 0)
    (hNAk : ¬ ∃ a : ℝ, (∀ᵐ y ∂Qk, 0 ≤ a * y) ∧ Qk {y | 0 < a * y} > 0)
    (hintj : Integrable id Qj) (hintk : Integrable id Qk)
    (hnrj : Qj {y | y ≠ 0} ≠ 0) (hnrk : Qk {y | y ≠ 0} ≠ 0)
    (Atilde : Set ℝ) (hAj : Atilde = {α | ∀ᵐ y ∂Qj, 0 ≤ 1 + α * y})
    (hAk : Atilde = {α | ∀ᵐ y ∂Qk, 0 ≤ 1 + α * y})
    (hicv : LEIncreasingConcaveOrder Qj Qk)
    (αj αk : ℝ) (hαj_mem : αj ∈ Atilde)
    (hαj_opt : ∀ α ∈ Atilde, ∫ y, (1 + α * y) ^ γ ∂Qj ≤ ∫ y, (1 + αj * y) ^ γ ∂Qj)
    (hαk_mem : αk ∈ Atilde)
    (hαk_opt : ∀ α ∈ Atilde, ∫ y, (1 + α * y) ^ γ ∂Qk ≤ ∫ y, (1 + αk * y) ^ γ ∂Qk),
    αj ≤ αk) := by
  intro h
  have := h (1 / 2) (by norm_num) (by norm_num) RMFCex.Qj RMFCex.Qk NAj NAk (int_Qj _) (int_Qk _)
    nrj nrk (Set.Icc (-1) 1) Aj Ak icv (-5 / 13) (-8 / 17) (by norm_num) optj (by norm_num) optk
  norm_num at this

#print axioms solution
