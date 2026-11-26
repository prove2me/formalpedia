-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.hasSum_brownianPositiveTowerLI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:31.749475+00:00
-- url     : https://prove2.me/submissions/09d557f7-deb1-4023-a37e-271f0ae0b602

import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianChaosHilbertSum

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (f : IteratedIntegralConstruction.PositiveKernelSum) :
    HasSum (fun n => simplexIntegral hB (n + 1) (f n))
      (brownianPositiveTowerLI hB hsm f) := by
  exact (brownianSimplexIntegralLI_orthogonalFamily hB hsm
    ).hasSum_linearIsometry f
end Malliavin.BrownianIteratedConstruction
