-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.inner_itoIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:13.620688+00:00
-- url     : https://prove2.me/submissions/9324bc5b-7a30-4c30-96c8-8765cff7f28e

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
namespace Malliavin
namespace ClarkOconeFamily
theorem _root_.solution {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (u v : PredictableProcessL2 𝓕 P) :
    inner ℝ (C.itoIntegral u) (C.itoIntegral v) = inner ℝ u v :=
  C.itoIntegralₗᵢ.inner_map_map u v
end ClarkOconeFamily
end Malliavin
