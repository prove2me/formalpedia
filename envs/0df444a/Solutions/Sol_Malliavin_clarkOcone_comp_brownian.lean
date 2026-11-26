-- Prove2me | solution 1 for Malliavin.clarkOcone_comp_brownian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:38:43.671902+00:00
-- url     : https://prove2.me/submissions/3e78f53f-df31-46e9-8e3b-2d55fd9c5171

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_predictableDerivative_compBrownianD12
import Theorems.Thm_Malliavin_clarkOcone


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {K c : ℝ} (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ K * Real.exp (c * |x|))
    (hgb' : ∀ x, |deriv g x| ≤ K * Real.exp (c * |x|)) (T : ℝ≥0) :
    (memLp_comp_brownian C.coordinate C.coordinate_apply hg hK hc hgb T).toLp _ =
      expectationL2 ((memLp_comp_brownian C.coordinate C.coordinate_apply hg hK hc hgb T).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (tensor (intervalIndicator T)
          ((memLp_deriv_comp_brownian C.coordinate C.coordinate_apply hg hK hc hgb' T).toLp
            _))) := by
  have h := clarkOcone C (compBrownianD12 C.coordinate C.coordinate_apply hg hK hc hgb hgb' T)
  rw [clarkOconeIntegral, predictableDerivative_compBrownianD12] at h
  exact h
end Malliavin
