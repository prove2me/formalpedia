-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.condExp_filtrationPred_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:44.364594+00:00
-- url     : https://prove2.me/submissions/16584147-a4ee-4dca-9fba-a01cb619b3b2

import Definitions.Def_Malliavin_PointwiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Theorems.Thm_Malliavin_condExp_natural_filtrationPred_ae_eq

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
namespace Malliavin
namespace ClarkOconeFamily
theorem _root_.solution
    (C : ClarkOconeFamily B P 𝓕) (t : ℝ≥0) (ht : 0 < t)
    (X : W → ℝ) (hX : Integrable X P) :
    P[X | filtrationPred 𝓕 t] =ᵐ[P] P[X | 𝓕 t] := by
  rw [C.naturalFiltration]
  exact condExp_natural_filtrationPred_ae_eq
    C.isPreBrownian C.stronglyMeasurable t ht X hX
end ClarkOconeFamily
end Malliavin
