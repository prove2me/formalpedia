-- Prove2me | solution 1 for Malliavin.setIntegral_predictableProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:33.581719+00:00
-- url     : https://prove2.me/submissions/728d1747-dc8b-4cec-a5de-f946164c117d

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) {s : Set (ℝ≥0 × W)}
    (hs : MeasurableSet[𝓕.predictable] s) (hμs : (nonnegativeLebesgueMeasure.prod P) s ≠ ∞) :
    ∫ x in s, (predictableProjection 𝓕 U : (ℝ≥0 × W) → ℝ) x ∂(nonnegativeLebesgueMeasure.prod P)
      = ∫ x in s, U x ∂(nonnegativeLebesgueMeasure.prod P) :=
  integral_condExpL2_eq (predictable_le_prod 𝓕) U hs hμs
end Malliavin
