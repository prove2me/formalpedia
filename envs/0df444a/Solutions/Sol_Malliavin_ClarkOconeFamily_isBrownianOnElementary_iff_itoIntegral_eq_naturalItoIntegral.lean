-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.isBrownianOnElementary_iff_itoIntegral_eq_naturalItoIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:04:52.609268+00:00
-- url     : https://prove2.me/submissions/1f4f31a5-2658-4ba4-8556-dab4bfa70179

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
import Theorems.Thm_Malliavin_ClarkOconeFamily_isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral
import Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnElementary_itoIntegral_eq_naturalItoIntegral


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
namespace Malliavin
namespace ClarkOconeFamily
theorem _root_.solution
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓅) :
    C.IsBrownianOnElementary ↔
      C.itoIntegral = naturalItoIntegral C.isPreBrownian C.stronglyMeasurable
        C.naturalFiltration :=
  ⟨fun hC ↦ hC.itoIntegral_eq_naturalItoIntegral,
    C.isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral⟩
end ClarkOconeFamily
end Malliavin
