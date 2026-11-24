-- Prove2me | solution 1 for Kyprianou.Ch02.poissonRegionTwoOrMoreBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:56:47.890858+00:00
-- url     : https://prove2.me/submissions/2fbf14ad-d3ce-4f79-be5e-6419caae7892

import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hR : MeasurableSet R)
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤) :
    (P {ω | 1 < N.N ω R}).toReal ≤
      (LevyStochCalc.Poisson.referenceIntensity ν R).toReal ^ 2 := by
  let r := (LevyStochCalc.Poisson.referenceIntensity ν R).toNNReal
  let μ := poissonMeasure r
  let E : Set ℕ := Set.Ioi 1
  have hE : MeasurableSet E := measurableSet_Ioi
  have hcompl : Eᶜ = ({0} ∪ {1} : Set ℕ) := by
    ext n
    simp [E]
    omega
  have hdisj : Disjoint ({0} : Set ℕ) {1} := by simp
  have hsum := measureReal_add_measureReal_compl (μ := μ) hE
  rw [hcompl, measureReal_union hdisj (measurableSet_singleton 1)] at hsum
  have h0 : μ.real {0} = Real.exp (-(r : ℝ)) := by
    dsimp [μ]
    rw [poissonMeasure_real_singleton]
    simp
  have h1 : μ.real {1} = Real.exp (-(r : ℝ)) * (r : ℝ) := by
    dsimp [μ]
    rw [poissonMeasure_real_singleton]
    simp
  rw [h0, h1, probReal_univ] at hsum
  have hexp := Real.add_one_le_exp (-(r : ℝ))
  have hr : 0 ≤ (r : ℝ) := r.2
  have hineq : (1 - (r : ℝ)) * (1 + (r : ℝ)) ≤
      Real.exp (-(r : ℝ)) * (1 + (r : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hP : P {ω | 1 < N.N ω R} = μ E := by
    have h := N.poisson_law hR hfin
    have happly := congrArg (fun m : Measure ℝ≥0∞ => m (Set.Ioi 1)) h
    rw [Measure.map_apply (N.measurable_eval hR) measurableSet_Ioi] at happly
    change P {ω | 1 < N.N ω R} =
      (μ.map (fun n : ℕ => (n : ℝ≥0∞))) (Set.Ioi 1) at happly
    rw [Measure.map_apply (by fun_prop) measurableSet_Ioi] at happly
    convert happly using 1
    congr 1
    ext n
    simp [E]
  rw [hP]
  have hrreal : (r : ℝ) = (LevyStochCalc.Poisson.referenceIntensity ν R).toReal := rfl
  rw [← hrreal]
  change μ.real E ≤ (r : ℝ) ^ 2
  nlinarith
