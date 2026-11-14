-- Prove2me | solution 1 for KSATSingleFlip.Connect.compound_poisson_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:25:57.012355+00:00
-- url     : https://prove2.me/submissions/fae134d9-0dc5-4b71-ba31-f2dc82e42198

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory KSATSingleFlip.Connect
open scoped ENNReal NNReal

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] : compoundPoisson μ Set.univ = 1 := by
  have hfin : μ Set.univ ≠ ∞ := measure_ne_top μ _
  have hf : ∀ j : ℕ, IsFiniteMeasure (convPow μ j) := by
    intro j
    induction j with
    | zero => simp [convPow]; infer_instance
    | succ j ih =>
      letI := ih
      change IsFiniteMeasure (μ ∗ convPow μ j)
      infer_instance
  have hmass : ∀ j : ℕ, convPow μ j Set.univ = (μ Set.univ)^j := by
    intro j
    induction j with
    | zero => simp [convPow]
    | succ j ih =>
      letI := hf j
      change (μ ∗ convPow μ j) Set.univ = (μ Set.univ)^(j+1)
      rw [Measure.conv, Measure.map_apply (by fun_prop) MeasurableSet.univ]
      simp only [Set.preimage_univ]
      rw [← Set.univ_prod_univ, Measure.prod_prod, ih, pow_succ]
      exact mul_comm _ _
  unfold compoundPoisson
  rw [if_neg hfin, Measure.sum_apply]
  · simp_rw [Measure.smul_apply, smul_eq_mul, hmass]
    let r : ℝ≥0 := ⟨(μ Set.univ).toReal, ENNReal.toReal_nonneg⟩
    have hr : ENNReal.ofReal (r:ℝ) = μ Set.univ := ENNReal.ofReal_toReal hfin
    have hsum := ProbabilityTheory.hasSum_one_poissonMeasure r
    have hsum' : (∑' j : ℕ, ENNReal.ofReal (Real.exp (-(r:ℝ))*(r:ℝ)^j/(j.factorial:ℝ))) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum.summable, hsum.tsum_eq]
      exact ENNReal.ofReal_one
    have heq (j : ℕ) : ENNReal.ofReal (Real.exp (-(μ Set.univ).toReal)/(j.factorial:ℝ)) *
        (μ Set.univ)^j = ENNReal.ofReal (Real.exp (-(r:ℝ))*(r:ℝ)^j/(j.factorial:ℝ)) := by
      rw [← hr, ENNReal.toReal_ofReal r.coe_nonneg, ← ENNReal.ofReal_pow r.coe_nonneg]
      rw [← ENNReal.ofReal_mul (show 0 ≤ Real.exp (-(r:ℝ))/(j.factorial:ℝ) by positivity)]
      congr 1
      ring
    simp_rw [heq]
    exact hsum'

  · exact MeasurableSet.univ
