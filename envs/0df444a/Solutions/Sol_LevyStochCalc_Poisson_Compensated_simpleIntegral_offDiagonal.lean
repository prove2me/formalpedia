-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.simpleIntegral_offDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:55:45.371193+00:00
-- url     : https://prove2.me/submissions/980bc894-969c-4a82-89f0-75fd3a381eb6

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of compensated-Poisson increments along a simple integrand

For a simple predictable integrand `φ` adapted to a filtration carrying the Poisson random
measure `N`, with boxes `B_i = (t_i, t_{i+1}] × A_i`: the diagonal identity
`∫⁻ ‖ξ_i · Ñ(B_i)‖² ∂P = ν̂(B_i) · ∫⁻ ‖ξ_i‖² ∂P` and the off-diagonal vanishing
`∫ (ξ_i · Ñ(B_i)) · (ξ_j · Ñ(B_j)) ∂P = 0` for `i < j`, both coming from the independence
of the past at `t_i` from the increment over `(t_i, t_{i+1}]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace PoisM
open LevyStochCalc.Poisson.Compensated (summable_pow_div_factorial_mul_nat)
lemma poisson_term_succ_eq (r : ℝ) (n : ℕ) :
    r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ)
    = r * (r ^ n / (n.factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Series identity for Poisson mean.** `∑' n, r^n / n! · n = r · exp(r)`. -/
lemma tsum_pow_div_factorial_mul_nat (r : ℝ) :
    ∑' n : ℕ, r ^ n / (n.factorial : ℝ) * (n : ℝ) = r * Real.exp r := by
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ))
            = fun n => r * (r ^ n / (n.factorial : ℝ)) from
      funext (poisson_term_succ_eq r)]
    exact (Real.summable_pow_div_factorial r).mul_left r
  rw [tsum_eq_zero_add' h_summable_succ]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    Nat.cast_zero, mul_zero, zero_add]
  simp_rw [poisson_term_succ_eq r]
  rw [tsum_mul_left]
  congr 1
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Mean of `poissonMeasure r` is `r`.** Derived from `integral_poissonMeasure`
+ the series identity `∑' n, r^n / n! · n = r · exp(r)`. -/
lemma poissonMeasure_integral_id (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r) = (r : ℝ) := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  have h_smul_eq : ∀ n : ℕ,
      (Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ)) • ((n : ℝ))
      = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
    intro n
    change Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
        = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ))
    ring
  simp_rw [h_smul_eq]
  rw [tsum_mul_left]
  rw [tsum_pow_div_factorial_mul_nat]
  rw [show Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) * Real.exp (↑r))
        = (↑r : ℝ) * (Real.exp (-(↑r : ℝ)) * Real.exp (↑r)) from by ring]
  rw [← Real.exp_add]
  rw [show (-(↑r : ℝ) + (↑r : ℝ)) = 0 from by ring]
  rw [Real.exp_zero, mul_one]
/-- **Summability of `r^n / n! · n` for r ≥ 0.** Used for integrability of `(n : ℝ)`
w.r.t. `poissonMeasure r`. -/
lemma poisson_term_succ_sq_eq (r : ℝ) (n : ℕ) :
    r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2
    = r * ((n + 1 : ℕ) : ℝ) * (r ^ n / (n.factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
/-- **Summability of `r^n / n! · n²`** for any real `r`. -/
lemma summable_pow_div_factorial_mul_nat_sq (r : ℝ) :
    Summable fun n : ℕ => r ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 2 := by
  have h_split : ∀ n : ℕ,
      r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2
      = r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
        + r * (r ^ n / (n.factorial : ℝ)) := by
    intro n
    rw [poisson_term_succ_sq_eq r]
    push_cast
    ring
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2)
            = fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
              + r * (r ^ n / (n.factorial : ℝ)) from
      funext h_split]
    refine Summable.add ?_ ?_
    · have h_eq : (fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)))
              = fun n : ℕ => r * (r ^ n / (n.factorial : ℝ) * (n : ℝ)) := by
        funext n; ring
      rw [h_eq]
      exact (summable_pow_div_factorial_mul_nat r).mul_left r
    · exact (Real.summable_pow_div_factorial r).mul_left r
  exact (summable_nat_add_iff 1).mp h_summable_succ
set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Series identity:** `∑' n, r^n / n! · n² = (r² + r) · exp(r)`. -/
lemma tsum_pow_div_factorial_mul_nat_sq (r : ℝ) :
    ∑' n : ℕ, r ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 2 = (r ^ 2 + r) * Real.exp r := by
  have h_split : ∀ n : ℕ,
      r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2
      = r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
        + r * (r ^ n / (n.factorial : ℝ)) := by
    intro n
    rw [poisson_term_succ_sq_eq r]
    push_cast
    ring
  have h_summable_n : Summable fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)) := by
    have h_eq : (fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)))
            = fun n : ℕ => r * (r ^ n / (n.factorial : ℝ) * (n : ℝ)) := by
      funext n; ring
    rw [h_eq]
    exact (summable_pow_div_factorial_mul_nat r).mul_left r
  have h_summable_const : Summable fun n : ℕ => r * (r ^ n / (n.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial r).mul_left r
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2)
            = fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
              + r * (r ^ n / (n.factorial : ℝ)) from
      funext h_split]
    exact h_summable_n.add h_summable_const
  rw [tsum_eq_zero_add' h_summable_succ]
  -- 0 term: r^0/0! * 0² = 0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_add]
  simp_rw [h_split]
  rw [Summable.tsum_add h_summable_n h_summable_const]
  -- Goal: (∑' n, r * n * (r^n/n!)) + (∑' n, r * (r^n/n!)) = (r² + r) * exp(r)
  rw [show (fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)))
          = fun n : ℕ => r * (r ^ n / (n.factorial : ℝ) * (n : ℝ)) from by
    funext n; ring]
  rw [tsum_mul_left, tsum_pow_div_factorial_mul_nat]
  rw [tsum_mul_left]
  have h_exp : ∑' n : ℕ, r ^ n / (n.factorial : ℝ) = Real.exp r := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [h_exp]
  ring
set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Second moment of `poissonMeasure r`:** `∫ n, (n : ℝ)² ∂poissonMeasure r = r² + r`. -/
lemma poissonMeasure_integral_id_sq (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
      = (r : ℝ) ^ 2 + (r : ℝ) := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  have h_smul_eq : ∀ n : ℕ,
      (Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ)) • ((n : ℝ) ^ 2)
      = Real.exp (-(↑r : ℝ))
        * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ) ^ 2) := by
    intro n
    change Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ) ^ 2
        = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ) ^ 2)
    ring
  simp_rw [h_smul_eq]
  rw [tsum_mul_left]
  rw [tsum_pow_div_factorial_mul_nat_sq]
  rw [show Real.exp (-(↑r : ℝ)) * (((↑r : ℝ) ^ 2 + (↑r : ℝ)) * Real.exp (↑r))
        = ((↑r : ℝ) ^ 2 + (↑r : ℝ))
          * (Real.exp (-(↑r : ℝ)) * Real.exp (↑r)) from by ring]
  rw [← Real.exp_add]
  rw [show (-(↑r : ℝ) + (↑r : ℝ)) = 0 from by ring]
  rw [Real.exp_zero, mul_one]
/-- Integrability of `(n : ℝ)` w.r.t. `poissonMeasure r`. -/
lemma integrable_id_poissonMeasure (r : ℝ≥0) :
    MeasureTheory.Integrable (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have h_norm : ∀ n : ℕ, ‖((n : ℝ))‖ = (n : ℝ) := fun n => by
    rw [Real.norm_eq_abs]; exact abs_of_nonneg (Nat.cast_nonneg n)
  simp_rw [h_norm]
  have h_eq : ∀ n : ℕ,
      Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
      = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
    intro n; ring
  simp_rw [h_eq]
  exact (summable_pow_div_factorial_mul_nat (↑r)).mul_left _
/-- Integrability of `(n : ℝ)²` w.r.t. `poissonMeasure r`. -/
lemma integrable_id_sq_poissonMeasure (r : ℝ≥0) :
    MeasureTheory.Integrable
      (fun n : ℕ => (n : ℝ) ^ 2) (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have h_norm : ∀ n : ℕ, ‖((n : ℝ) ^ 2)‖ = (n : ℝ) ^ 2 := fun n => by
    rw [Real.norm_eq_abs]; exact abs_of_nonneg (sq_nonneg _)
  simp_rw [h_norm]
  have h_eq : ∀ n : ℕ,
      Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)^2
      = Real.exp (-(↑r : ℝ))
        * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)^2) := by
    intro n; ring
  simp_rw [h_eq]
  exact (summable_pow_div_factorial_mul_nat_sq (↑r)).mul_left _
set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Variance of `poissonMeasure r`:** `∫ n, ((n:ℝ) − r)² ∂poissonMeasure r = r`.
Mean `r`, second moment `r²+r`, variance `(r²+r) − r² = r`. -/
lemma poissonMeasure_variance (r : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) - (r : ℝ)) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
      = (r : ℝ) := by
  have h_int_n := integrable_id_poissonMeasure r
  have h_int_nsq := integrable_id_sq_poissonMeasure r
  have h_int_const : MeasureTheory.Integrable
      (fun _ : ℕ => (r : ℝ) ^ 2) (ProbabilityTheory.poissonMeasure r) :=
    MeasureTheory.integrable_const _
  have h_int_2rn : MeasureTheory.Integrable
      (fun n : ℕ => 2 * (r : ℝ) * (n : ℝ)) (ProbabilityTheory.poissonMeasure r) :=
    h_int_n.const_mul (2 * (r : ℝ))
  -- Expand (n - r)² = n² - 2rn + r², explicitly stated as ((n² - 2rn) + r²) for additivity.
  have h_expand : ∀ n : ℕ, ((n : ℝ) - (r : ℝ)) ^ 2
      = ((n : ℝ) ^ 2 - 2 * (r : ℝ) * (n : ℝ)) + (r : ℝ) ^ 2 := by
    intro n; ring
  simp_rw [h_expand]
  -- Use integral linearity step-by-step. To avoid Pi.sub_apply matching issues,
  -- compute each integral as a have-hypothesis and combine via calc.
  have h_e_nsq : ∫ n : ℕ, (n : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
      = (↑r : ℝ) ^ 2 + (↑r : ℝ) := poissonMeasure_integral_id_sq r
  have h_e_2rn : ∫ n : ℕ, 2 * (↑r : ℝ) * (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r)
      = 2 * (↑r : ℝ) * (↑r : ℝ) := by
    rw [MeasureTheory.integral_const_mul]
    rw [poissonMeasure_integral_id]
  have h_e_csq :
      ∫ _ : ℕ, (↑r : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r) = (↑r : ℝ) ^ 2 := by
    rw [MeasureTheory.integral_const]
    rw [show (ProbabilityTheory.poissonMeasure r).real Set.univ = 1 from by
      rw [MeasureTheory.measureReal_def]; simp [MeasureTheory.measure_univ]]
    rw [one_smul]
  -- ∫ ((n² - 2rn) + r²) = ∫ (n² - 2rn) + ∫ r²
  rw [show
      ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (↑r : ℝ) * (n : ℝ)) + (↑r : ℝ) ^ 2
        ∂(ProbabilityTheory.poissonMeasure r)
      = ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (↑r : ℝ) * (n : ℝ))
          ∂(ProbabilityTheory.poissonMeasure r)
        + ∫ _ : ℕ, (↑r : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r) from
    MeasureTheory.integral_add (h_int_nsq.sub h_int_2rn) h_int_const]
  -- ∫ (n² - 2rn) = ∫ n² - ∫ 2rn
  rw [show
      ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (↑r : ℝ) * (n : ℝ))
        ∂(ProbabilityTheory.poissonMeasure r)
      = ∫ n : ℕ, (n : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
        - ∫ n : ℕ, 2 * (↑r : ℝ) * (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r) from
    MeasureTheory.integral_sub h_int_nsq h_int_2rn]
  rw [h_e_nsq, h_e_2rn, h_e_csq]
  ring

end PoisM

open PoisM

/-- Transfer: an integral of `g (N B)` is an integral against the Poisson law. -/
lemma pois_transfer {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (g : ℝ≥0∞ → ℝ) (hg : Measurable g) :
    (∫ ω, g (N.N ω B) ∂P = ∫ n : ℕ, g n
        ∂(poissonMeasure (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal)) ∧
    (Integrable (fun ω => g (N.N ω B)) P ↔ Integrable (fun n : ℕ => g n)
        (poissonMeasure (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal)) := by
  have hm := N.measurable_eval hB
  have hlaw := N.poisson_law hB h_finite
  have hc : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := measurable_of_countable _
  constructor
  · rw [← integral_map hm.aemeasurable hg.aestronglyMeasurable, hlaw,
      LevyStochCalc.Poisson.poissonMeasureENN,
      integral_map hc.aemeasurable hg.aestronglyMeasurable]
  · show Integrable (g ∘ fun ω => N.N ω B) P ↔ Integrable (g ∘ fun n : ℕ => (n : ℝ≥0∞)) _
    rw [← integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable, hlaw,
      LevyStochCalc.Poisson.poissonMeasureENN,
      integrable_map_measure hg.aestronglyMeasurable hc.aemeasurable]

lemma comp_eq {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (B : Set (ℝ × E))
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) (ω : Ω) :
    N.compensated B ω = (N.N ω B).toReal
      - (((LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal : ℝ)) := by
  rw [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]; rfl


namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]



theorem _root_.solution
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) {i j : Fin φ.N} (hij : i < j)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    (h_adapt_j : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition j.castSucc)) (φ.ξ j)) :
    ∫ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) *
         (φ.ξ j ω * N.compensated (φ.timeRect j T) ω) ∂P = 0 := by
  classical
  set a := φ.partition j.castSucc with ha
  set b := φ.partition j.succ with hb
  have hab0 : a < b := φ.partition_strictMono Fin.castSucc_lt_succ
  have hmono := φ.partition_strictMono.monotone
  have hsucc_le : φ.partition i.succ ≤ a := hmono (by rw [Fin.le_def]; simp; omega)
  have hti_le : φ.partition i.castSucc ≤ a := hmono (by rw [Fin.le_def]; simp; omega)
  have ha0 : 0 ≤ a := by
    have := hmono (Fin.zero_le j.castSucc); rwa [φ.partition_zero] at this
  set Ri := φ.timeRect i T with hRi
  set Rj := φ.timeRect j T with hRj
  have hRjdef : Rj = Set.Ioc (min a T) (min b T) ×ˢ φ.A j := rfl
  have hRidef : Ri = Set.Ioc (min (φ.partition i.castSucc) T) (min (φ.partition i.succ) T) ×ˢ φ.A i := rfl
  have hRim : MeasurableSet Ri := hRidef ▸ measurableSet_Ioc.prod (φ.A_measurable i)
  have hRjm : MeasurableSet Rj := hRjdef ▸ measurableSet_Ioc.prod (φ.A_measurable j)
  have hint_eq : ∀ ω, (φ.ξ i ω * N.compensated Ri ω) * (φ.ξ j ω * N.compensated Rj ω)
      = (φ.ξ i ω * N.compensated Ri ω * φ.ξ j ω) * N.compensated Rj ω := fun ω => by ring
  simp_rw [hint_eq]
  by_cases hlt : min a T < min b T
  · have haT : a ≤ T := by
      by_contra h; push Not at h
      have : min a T = T := min_eq_right h.le
      have : min b T = T := min_eq_right (h.trans hab0).le
      linarith
    have hmin : min a T = a := min_eq_left haT
    have hRjdef' : Rj = Set.Ioc a (min b T) ×ˢ φ.A j := by rw [hRjdef, hmin]
    have hRjfin : LevyStochCalc.Poisson.referenceIntensity ν Rj ≠ ⊤ := by
      rw [hRjdef, LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod]
      refine ENNReal.mul_ne_top ?_ (φ.A_finite j)
      rw [Measure.restrict_apply measurableSet_Ioc]
      exact ((measure_mono Set.inter_subset_left).trans_lt measure_Ioc_lt_top).ne
    have hind := hℱ.indep (s := a) (t := min b T) ha0 (hmin ▸ hlt) (φ.A_measurable j) (φ.A_finite j)
    rw [← hRjdef'] at hind
    -- measurability of the past factor
    have hNi : Measurable[ℱ a] (fun ω => N.N ω Ri) := by
      refine hℱ.measurable ?_ hRim
      intro x hx
      rw [hRidef] at hx
      exact ⟨hx.1.2.trans ((min_le_left _ _).trans hsucc_le), Set.mem_univ _⟩
    have hci : Measurable[ℱ a] (fun ω => N.compensated Ri ω) :=
      (ENNReal.measurable_toReal.comp hNi).sub_const _
    have hξi : Measurable[ℱ a] (φ.ξ i) :=
      h_adapt_i.measurable.mono (ℱ.mono hti_le) le_rfl
    have hξj : Measurable[ℱ a] (φ.ξ j) := h_adapt_j.measurable
    have hX : Measurable[ℱ a] (fun ω => φ.ξ i ω * N.compensated Ri ω * φ.ξ j ω) :=
      (hξi.mul hci).mul hξj
    have hF : Measurable (fun x : ℝ≥0∞ => x.toReal - (LevyStochCalc.Poisson.referenceIntensity ν Rj).toReal) := by
      fun_prop
    have hY : Measurable[MeasurableSpace.comap (fun ω => N.N ω Rj) inferInstance]
        (fun ω => N.compensated Rj ω) := hF.comp (comap_measurable _)
    have hindXY : IndepFun (fun ω => φ.ξ i ω * N.compensated Ri ω * φ.ξ j ω)
        (fun ω => N.compensated Rj ω) P := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hX.comap_le) hY.comap_le
    have hXg : Measurable (fun ω => φ.ξ i ω * N.compensated Ri ω * φ.ξ j ω) := hX.mono (ℱ.le a) le_rfl
    have hYg : Measurable (fun ω => N.compensated Rj ω) :=
      hY.mono (N.measurable_eval hRjm).comap_le le_rfl
    rw [hindXY.integral_fun_mul_eq_mul_integral hXg.aestronglyMeasurable hYg.aestronglyMeasurable]
    have hmean : ∫ ω, N.compensated Rj ω ∂P = 0 := by
      have ht := pois_transfer N hRjm hRjfin
        (fun x : ℝ≥0∞ => (x.toReal - (((LevyStochCalc.Poisson.referenceIntensity ν Rj).toNNReal : ℝ))))
        (by fun_prop)
      simp_rw [comp_eq N Rj hRjfin]
      rw [ht.1]
      simp only [ENNReal.toReal_natCast]
      rw [integral_sub (integrable_id_poissonMeasure _) (integrable_const _), poissonMeasure_integral_id,
        integral_const, probReal_univ, one_smul, sub_self]
    rw [hmean, mul_zero]
  · have hempty : Rj = ∅ := by
      rw [hRjdef, Set.Ioc_eq_empty hlt, Set.empty_prod]
    have hc : ∀ ω, N.compensated Rj ω = 0 := by
      intro ω
      simp [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated, hempty]
    simp_rw [hc]; simp

