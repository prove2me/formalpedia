-- Prove2me | solution 1 for Malliavin.clarkOcone_comp_pi_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:49:23.321356+00:00
-- url     : https://prove2.me/submissions/a2300db4-6d8b-4e2c-b037-70ac232d44e6

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_predictableDerivative_compPiWienerIntegralD12
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
    (C : ClarkOconeFamily B P 𝓕) {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (g : Fin n → Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (memLp_comp_pi P hf hK fun i ↦ wienerIntegral C.isPreBrownian (g i)).toLp _ =
      expectationL2
          ((memLp_comp_pi P hf hK fun i ↦ wienerIntegral C.isPreBrownian (g i)).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (∑ i, tensor (g i)
          ((memLp_fderiv_pi_comp hf hK (fun i ↦ wienerIntegral C.isPreBrownian (g i)) i).toLp
            _))) := by
  have h := clarkOcone C (compPiWienerIntegralD12 C.isPreBrownian C.coordinate
    C.coordinate_apply C.generated hf hK g)
  rw [clarkOconeIntegral, predictableDerivative_compPiWienerIntegralD12] at h
  exact h
end Malliavin
