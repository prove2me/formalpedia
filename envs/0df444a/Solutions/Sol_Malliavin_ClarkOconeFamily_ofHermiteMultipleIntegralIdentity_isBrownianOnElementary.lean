-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.ofHermiteMultipleIntegralIdentity_isBrownianOnElementary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:33.774373+00:00
-- url     : https://prove2.me/submissions/32e1a4ef-0017-4692-9b4d-1d4e630cec1c

import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianHermiteClarkOcone
import Theorems.Thm_Malliavin_ClarkOconeFamily_isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
open BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
namespace ClarkOconeFamily
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    (ClarkOconeFamily.ofHermiteMultipleIntegralIdentity
      hB coordinate coordinate_apply generated hsm hnat hid
      ).IsBrownianOnElementary := by
  apply ClarkOconeFamily.isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral
  rfl
end ClarkOconeFamily
end Malliavin
