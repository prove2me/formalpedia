-- Prove2me | solution 1 for Malliavin.naturalClarkOcone_comp_brownian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:00.902304+00:00
-- url     : https://prove2.me/submissions/aa7c67a9-afc5-4d51-a918-a148e0bdadbd

import Definitions.Def_Malliavin_BrownianHermiteClarkOcone
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Definitions.Def_Malliavin_BrownianClarkOconeCapstone
import Theorems.Thm_Malliavin_clarkOcone_comp_brownian


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
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {K c : ℝ} (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ K * Real.exp (c * |x|))
    (hgb' : ∀ x, |deriv g x| ≤ K * Real.exp (c * |x|)) (T : ℝ≥0) :
    (memLp_comp_brownian coordinate coordinate_apply hg hK hc hgb T).toLp _ =
      expectationL2 ((memLp_comp_brownian coordinate coordinate_apply hg hK hc hgb T).toLp _)
        + naturalItoIntegral hB hsm hnat (predictableProjection filtration
          (tensor (intervalIndicator T)
            ((memLp_deriv_comp_brownian coordinate coordinate_apply hg hK hc hgb' T).toLp
              _))) :=
  clarkOcone_comp_brownian
    (ClarkOconeFamily.ofGenerated hB coordinate coordinate_apply generated hsm hnat)
    hg hK hc hgb hgb' T
end Malliavin
