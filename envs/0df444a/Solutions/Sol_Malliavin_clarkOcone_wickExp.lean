-- Prove2me | solution 1 for Malliavin.clarkOcone_wickExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:48:13.99175+00:00
-- url     : https://prove2.me/submissions/dcc1c843-a27e-41cd-9d86-be699e7b8745

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_ClarkOconeFamily_timeDerivative_apply
import Theorems.Thm_Malliavin_clarkOcone
import Theorems.Thm_Malliavin_comp_brownian_mem_domD12
import Theorems.Thm_Malliavin_deriv_exp_sub
import Theorems.Thm_Malliavin_timeDerivative_mderivClosure_wickExp_brownian


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
    (C : ClarkOconeFamily B P 𝓕) (T : ℝ≥0) :
    (memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _ =
      expectationL2 ((memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (tensor (intervalIndicator T)
          ((memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _))) := by
  have hmem : (memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _ ∈ domD12 P :=
    (comp_brownian_mem_domD12 C.coordinate C.coordinate_apply (contDiff_exp_sub (T / 2))
      zero_le_one zero_le_one (fun x ↦ abs_exp_sub_le_exp_abs (T / 2) x (by positivity))
      (fun x ↦ by rw [deriv_exp_sub]; exact abs_exp_sub_le_exp_abs (T / 2) x (by positivity)) T)
  have h := clarkOcone C ⟨_, hmem⟩
  rw [clarkOconeIntegral, predictableDerivative, mderivD12_apply,
    ClarkOconeFamily.timeDerivative_apply] at h
  change (memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _ =
    expectationL2 ((memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _) +
      C.itoIntegral (predictableProjection 𝓕 (timeDerivative C.isPreBrownian C.coordinate
        C.coordinate_apply C.generated (mderivClosure P
          ((memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _)))) at h
  rwa [timeDerivative_mderivClosure_wickExp_brownian C.isPreBrownian C.coordinate
    C.coordinate_apply C.generated T] at h
end Malliavin
