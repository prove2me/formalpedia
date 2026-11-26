-- Prove2me | solution 1 for Malliavin.measureDense_pastCylinderEvents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:49:06.701106+00:00
-- url     : https://prove2.me/submissions/b13c11f1-414d-43bb-b7c8-da2a0d594842

import Definitions.Def_Malliavin_NaturalClarkOcone
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_PastCylinderDensity
import Theorems.Thm_Malliavin_isSetAlgebra_pastCylinderEvents

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E F W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (a : ℝ≥0) :
    @Measure.MeasureDense W (𝓕 a) (P.trim (𝓕.le a))
      (pastCylinderEvents B a) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hgen : 𝓕 a = MeasurableSpace.generateFrom (pastCylinderEvents B a) := by
    rw [hnat]
    exact natural_eq_generateFrom_pastCylinderEvents hsm a
  let _ : MeasurableSpace W := 𝓕 a
  exact Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
    (μ := P.trim (𝓕.le a)) (isSetAlgebra_pastCylinderEvents B a) hgen
end Malliavin
