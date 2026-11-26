-- Prove2me | solution 1 for Malliavin.naturalClarkOcone_polynomial_brownian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:38.363193+00:00
-- url     : https://prove2.me/submissions/4c8d63f3-d100-402b-82d3-12a8eedbe31e

import Definitions.Def_Malliavin_BrownianHermiteClarkOcone
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Definitions.Def_Malliavin_BrownianClarkOconeCapstone
import Theorems.Thm_Malliavin_clarkOcone_polynomial_brownian


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
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (p : Polynomial ℝ) (T : ℝ≥0) :
    (memLp_polynomial_brownian coordinate coordinate_apply p T).toLp _ =
      expectationL2 ((memLp_polynomial_brownian coordinate coordinate_apply p T).toLp _)
        + naturalItoIntegral hB hsm hnat (predictableProjection filtration
          (tensor (intervalIndicator T)
            ((memLp_polynomial_derivative_brownian coordinate coordinate_apply p T).toLp
              _))) :=
  clarkOcone_polynomial_brownian
    (ClarkOconeFamily.ofGenerated hB coordinate coordinate_apply generated hsm hnat) p T
end Malliavin
