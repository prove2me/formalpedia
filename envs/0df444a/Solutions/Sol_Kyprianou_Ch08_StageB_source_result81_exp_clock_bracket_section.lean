-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_exp_clock_bracket_section
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T18:12:36.556808+00:00
-- url     : https://prove2.me/submissions/47c4a6ab-7bfd-4567-8360-1c958f752011

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real

open AvramDividend.Classical
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private lemma clock_expMeasure_ae_pos (q : ℝ) (hq : 0 < q) :
    ∀ᵐ r ∂expMeasure q, 0 < r := by
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  have h1 : expMeasure q (Ioi (0 : ℝ)) = 1 := by
    simpa only [mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one] using
      avram_ws01e_b_expMeasure_strict_survival_real q 0 hq le_rfl
  rw [ae_iff]
  simp only [not_lt]
  change expMeasure q (Iic (0 : ℝ)) = 0
  simpa [h1] using
    (prob_compl_eq_one_sub (μ := expMeasure q)
      (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))))

private lemma clock_expMeasure_ae_ne (q : ℝ) (u : ℝ≥0) :
    ∀ᵐ r ∂expMeasure q, r ≠ (u : ℝ) := by
  letI : NullSingletonClass (expMeasure q) := by
    rw [expMeasure, gammaMeasure]
    infer_instance
  exact Measure.ae_ne (expMeasure q) (u : ℝ)

private lemma clock_bracket_ae (q : ℝ) (hq : 0 < q) (τ : WithTop ℝ≥0)
    (u : ℝ≥0) (hτ : τ = (u : WithTop ℝ≥0)) (E : Set ℝ)
    (hE : ∀ r : ℝ,
      (τ < (r.toNNReal : WithTop ℝ≥0) → r ∈ E) ∧
      (r ∈ E → τ ≤ (r.toNNReal : WithTop ℝ≥0))) :
    E =ᵐ[expMeasure q] Ioi (u : ℝ) := by
  filter_upwards [clock_expMeasure_ae_pos q hq, clock_expMeasure_ae_ne q u] with r hr hru
  have hcast : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr.le
  apply propext
  constructor
  · intro h
    have ht := (hE r).2 h
    rw [hτ] at ht
    have hh := WithTop.coe_le_coe.mp ht
    have hh' : (u : ℝ) ≤ (r.toNNReal : ℝ) := by exact_mod_cast hh
    rw [hcast] at hh'
    exact lt_of_le_of_ne hh' (Ne.symm hru)
  · intro h
    have hh' : (u : ℝ) < (r.toNNReal : ℝ) := by
      rw [hcast]
      exact (Set.mem_Ioi.mp h)
    have hh : u < r.toNNReal := by exact_mod_cast hh'
    apply (hE r).1
    rw [hτ]
    exact WithTop.coe_lt_coe.mpr hh

theorem solution
    (q : ℝ) (hq : 0 < q) (τ : WithTop ℝ≥0) (E : Set ℝ)
    (hE : ∀ r : ℝ,
      (τ < (r.toNNReal : WithTop ℝ≥0) → r ∈ E) ∧
      (r ∈ E → τ ≤ (r.toNNReal : WithTop ℝ≥0))) :
    (expMeasure q).real E = discountedAt q τ := by
  classical
  let Q := expMeasure q
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_expMeasure hq
  change Q.real E = _
  by_cases htop : τ = ⊤
  · have hEmpty : E = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have ht := (hE r).2 hr
      rw [htop] at ht
      exact WithTop.coe_ne_top (top_le_iff.mp ht)
    simp [hEmpty, htop, discountedAt, Measure.real_def]
  · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp htop
    have hτ : τ = (u : WithTop ℝ≥0) := hu.symm
    have hEa : E =ᵐ[Q] Ioi (u : ℝ) := by
      simpa [Q] using clock_bracket_ae q hq τ u hτ E hE
    rw [Measure.real_def, measure_congr hEa, hτ]
    change (expMeasure q (Ioi (u : ℝ))).toReal = Real.exp (-q * (u : ℝ))
    rw [avram_ws01e_b_expMeasure_strict_survival_real q (u : ℝ) hq u.coe_nonneg,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, neg_mul]
