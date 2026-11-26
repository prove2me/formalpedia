-- Prove2me | solution 1 for Malliavin.setIntegral_timeSection_sub_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:59.414959+00:00
-- url     : https://prove2.me/submissions/85ffbcf7-1d77-4f6d-a78b-993fc37988de

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_setIntegral_predictableProjection

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution (U : TimeProcessL2 P) {a : ℝ≥0} {A : Set W}
    (hA : MeasurableSet[𝓕 a] A)
    (D : TimeProcessL2 P)
    (hD : (D : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun x ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) x - U x)
    {c d : ℝ≥0} (hac : a ≤ c) :
    ∫ t in Set.Ioc c d, ∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P
      ∂nonnegativeLebesgueMeasure = 0 := by
  set μ := nonnegativeLebesgueMeasure.prod P with hμ
  have hrect : μ (Set.Ioc c d ×ˢ A) ≠ ∞ := by
    rw [hμ, Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne (measure_lt_top P A).ne
  have hDint := integrableOn_Lp_of_measure_ne_top D fact_one_le_two_ennreal.elim hrect
  have hQint := integrableOn_Lp_of_measure_ne_top
    (predictableProjection 𝓕 U : TimeProcessL2 P) fact_one_le_two_ennreal.elim hrect
  have hUint := integrableOn_Lp_of_measure_ne_top U fact_one_le_two_ennreal.elim hrect
  have hprod : ∫ x in Set.Ioc c d ×ˢ A, (D : ℝ≥0 × W → ℝ) x ∂μ = 0 := by
    calc ∫ x in Set.Ioc c d ×ˢ A, (D : ℝ≥0 × W → ℝ) x ∂μ
        = ∫ x in Set.Ioc c d ×ˢ A,
            ((predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) x - U x) ∂μ :=
          setIntegral_congr_ae ((measurableSet_Ioc.prod (𝓕.le a A hA)))
            (hD.mono fun x hx _ ↦ hx)
      _ = (∫ x in Set.Ioc c d ×ˢ A, (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) x ∂μ) -
            ∫ x in Set.Ioc c d ×ˢ A, U x ∂μ := integral_sub hQint hUint
      _ = 0 := by
          rw [setIntegral_predictableProjection 𝓕 U
            (measurableSet_predictable_Ioc_prod c d (𝓕.mono hac A hA)) hrect, sub_self]
  rw [setIntegral_prod _ hDint] at hprod
  exact hprod
end Malliavin
