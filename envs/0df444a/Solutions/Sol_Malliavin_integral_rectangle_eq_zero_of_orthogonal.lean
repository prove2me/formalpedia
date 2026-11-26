-- Prove2me | solution 1 for Malliavin.integral_rectangle_eq_zero_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:33:02.332855+00:00
-- url     : https://prove2.me/submissions/dc6c5cb7-ee9b-4c97-b84d-70f6ea61ac10

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
import Theorems.Thm_Malliavin_inner_elementaryPredictable_adaptedIndicator
import Theorems.Thm_Malliavin_elementaryPredictable_mem_span

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W))
    (g : PredictableProcessL2 𝓕 P)
    (horth : ∀ U : PredictableProcessL2 𝓕 P,
      U ∈ elementaryPredictableSpan (P := P) 𝓕 → ⟪U, g⟫_ℝ = 0) :
    ∀ R ∈ predictableRectangle 𝓕,
      ∫ z in R, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P = 0 := by
  intro R hR
  rcases hR with ⟨F₀, hF₀, rfl⟩ | ⟨a, b, F, hab, hF, rfl⟩
  · apply setIntegral_measure_zero
    rw [Measure.prod_prod, measure_singleton, zero_mul]
  · rw [← inner_elementaryPredictable_adaptedIndicator 𝓕 a b hF g]
    exact horth _ (elementaryPredictable_mem_span 𝓕 a b hab.le
      (adaptedIndicator (P := P) 𝓕 a hF))
end Malliavin
