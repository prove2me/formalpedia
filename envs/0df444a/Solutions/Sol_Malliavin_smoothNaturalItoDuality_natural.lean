-- Prove2me | solution 1 for Malliavin.smoothNaturalItoDuality_natural
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:56:42.068173+00:00
-- url     : https://prove2.me/submissions/ff03f275-6c4c-4bee-89d6-ca37ad3dcef9

import Definitions.Def_Malliavin_NaturalClarkOcone
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_PastCylinderDensity
import Theorems.Thm_Malliavin_smoothElementaryNaturalItoDuality_natural
import Theorems.Thm_Malliavin_smoothNaturalItoDuality_of_elementary


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
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) :
    SmoothNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat := by
  exact smoothNaturalItoDuality_of_elementary
    hB coordinate coordinate_apply generated hsm hnat
      (smoothElementaryNaturalItoDuality_natural
        hB coordinate coordinate_apply generated hsm hnat)
end Malliavin
