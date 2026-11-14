-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_recursion_mass
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:25:56.958385+00:00
-- url     : https://prove2.me/submissions/e2c4ea91-3689-49a0-95d9-60a3d137ee55

import Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_probability
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem solution (ν : Measure ℝ) [IsFiniteMeasure ν] (β : ℝ) (hβ : 0 ≤ β)
    (hfin : (ν.withDensity fun z => ENNReal.ofReal (wInt z)) Set.univ ≠ ∞) :
    Kmeas ν Set.univ = 1 ∧ (massM (Rbeta β ν)).toReal = β * Real.exp (hPot ν) := by
  let μ : Measure ℝ := Measure.map aShift (ν.withDensity fun z => ENNReal.ofReal (wInt z))
  have hma : Measurable aShift := by unfold aShift; fun_prop
  have hmu : μ Set.univ ≠ ∞ := by
    dsimp [μ]
    rw [Measure.map_apply hma MeasurableSet.univ]
    simpa using hfin
  letI : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hmu⟩
  have hx := compound_poisson_probability μ
  let P := compoundPoisson μ
  letI : IsProbabilityMeasure P := ⟨hx⟩
  have hK : Kmeas ν Set.univ = 1 := by
    change (P ∗ Measure.map (fun z : ℝ => -z) P) Set.univ = 1
    rw [Measure.conv, Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp only [Set.preimage_univ]
    rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ]
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  refine ⟨hK,?_⟩
  unfold massM Rbeta
  rw [Measure.smul_apply, smul_eq_mul, hK, mul_one]
  rw [ENNReal.toReal_ofReal (mul_nonneg hβ (le_of_lt (Real.exp_pos _)))]
