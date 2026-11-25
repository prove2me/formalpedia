-- Prove2me | solution 1 for Kyprianou.Ch04.independentWeightedCompensatedCellL2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:49:30.758784+00:00
-- url     : https://prove2.me/submissions/b6f98e97-a2ff-47f8-a6ce-243cbf050620

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure

open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A past-independent square-integrable weight preserves the exact
quadratic energy of one finite-intensity compensated marked-Poisson cell.
This is the one-cell building block of Exercise 4.4. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P ν)
    {B : Set (ℝ × ℝ)} (_hB : MeasurableSet B)
    (_hFin : referenceIntensity ν B ≠ ⊤)
    (H : Ω → ℝ) (hH2 : Integrable (fun ω => H ω ^ 2) P)
    (hInt : Integrable (fun ω => (N.compensated B ω) ^ 2) P)
    (hSecondMoment : (∫ ω, (N.compensated B ω) ^ 2 ∂P) =
      (referenceIntensity ν B).toReal)
    (hIndep : IndepFun H (fun ω => N.N ω B) P) :
    Integrable (fun ω => (H ω * N.compensated B ω) ^ 2) P ∧
      (∫ ω, (H ω * N.compensated B ω) ^ 2 ∂P) =
        (referenceIntensity ν B).toReal *
          ∫ ω, H ω ^ 2 ∂P := by
  let g : ENNReal → ℝ :=
    fun x => (x.toReal - (referenceIntensity ν B).toReal) ^ 2
  have hg : Measurable g := by fun_prop
  have hIndepSq :
      IndepFun (fun ω => H ω ^ 2)
        (fun ω => (N.compensated B ω) ^ 2) P := by
    simpa only [Function.comp_def, g,
      LevyStochCalc.Poisson.PoissonRandomMeasure.compensated] using
      hIndep.comp (by fun_prop : Measurable (fun x : ℝ => x ^ 2)) hg
  have hProdInt :
      Integrable (fun ω => H ω ^ 2 * (N.compensated B ω) ^ 2) P := by
    have hEq :
        (fun ω => H ω ^ 2 * (N.compensated B ω) ^ 2) =
          (fun ω => H ω ^ 2) *
          (fun ω => (N.compensated B ω) ^ 2) := by
      funext ω
      rfl
    rw [hEq]
    exact hIndepSq.integrable_mul hH2 hInt
  have hMean :
      (∫ ω, H ω ^ 2 * (N.compensated B ω) ^ 2 ∂P) =
        (∫ ω, H ω ^ 2 ∂P) *
          (∫ ω, (N.compensated B ω) ^ 2 ∂P) := by
    simpa only [Pi.mul_apply] using
      hIndepSq.integral_fun_mul_eq_mul_integral
        hH2.aestronglyMeasurable hInt.aestronglyMeasurable
  have hSquare :
      (fun ω => (H ω * N.compensated B ω) ^ 2) =
        (fun ω => H ω ^ 2 * (N.compensated B ω) ^ 2) := by
    funext ω
    ring
  constructor
  · rw [hSquare]
    exact hProdInt
  · rw [hSquare, hMean, hSecondMoment]
    ring
