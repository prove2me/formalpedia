-- Prove2me | solution 1 for Malliavin.integral_predictableProjection_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:09.622069+00:00
-- url     : https://prove2.me/submissions/f6805748-d5a8-4bcb-b1e7-ef6e2d43a1be

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (U : TimeProcessL2 P) (a b : ℝ≥0) {A : Set W}
    (hA : MeasurableSet[𝓕 a] A) :
    ∫ t in Set.Ioc a b, ∫ ω in A,
        (predictableProjection 𝓕 U : (ℝ≥0 × W) → ℝ) (t, ω) ∂P
        ∂nonnegativeLebesgueMeasure =
      ∫ t in Set.Ioc a b, ∫ ω in A, U (t, ω) ∂P
        ∂nonnegativeLebesgueMeasure := by
  let μ := nonnegativeLebesgueMeasure.prod P
  have hrect : μ (Set.Ioc a b ×ˢ A) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne (measure_lt_top P A).ne
  have hQ := integrableOn_Lp_of_measure_ne_top
    (predictableProjection 𝓕 U : TimeProcessL2 P)
    fact_one_le_two_ennreal.elim hrect
  have hU := integrableOn_Lp_of_measure_ne_top
    U fact_one_le_two_ennreal.elim hrect
  rw [← setIntegral_prod _ hQ, ← setIntegral_prod _ hU]
  exact integral_condExpL2_eq (predictable_le_prod 𝓕) U
    (measurableSet_predictable_Ioc_prod a b hA) hrect
end Malliavin
