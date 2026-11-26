-- Prove2me | solution 1 for Malliavin.adaptedMono_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:03:53.589981+00:00
-- url     : https://prove2.me/submissions/2b3ddc7f-9699-4c55-8cc1-f5fec072a2e9

import Definitions.Def_Malliavin_ElementaryIto
import Definitions.Def_Malliavin_PredictableDensity
import Definitions.Def_Malliavin_ItoConstruction

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {a c : ℝ≥0} (hac : a ≤ c)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (adaptedMono 𝓕 hac Z : RandomL2 P) = (Z : RandomL2 P) :=
  rfl
end Malliavin
