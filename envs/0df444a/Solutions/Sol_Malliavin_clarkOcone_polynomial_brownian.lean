-- Prove2me | solution 1 for Malliavin.clarkOcone_polynomial_brownian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:40:39.369262+00:00
-- url     : https://prove2.me/submissions/08ba8cc2-cd26-49fb-bc7f-4bf3d83b5fe1

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_clarkOcone_comp_brownian
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_P2M_Malliavin_abs_polynomial_deriv_le__df93b7f4181a
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



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
    (C : ClarkOconeFamily B P 𝓕) (p : Polynomial ℝ) (T : ℝ≥0) :
    (memLp_polynomial_brownian C.coordinate C.coordinate_apply p T).toLp _ =
      expectationL2 ((memLp_polynomial_brownian C.coordinate C.coordinate_apply p T).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (tensor (intervalIndicator T)
          ((memLp_polynomial_derivative_brownian C.coordinate C.coordinate_apply p T).toLp
            _))) := by
  have h := clarkOcone_comp_brownian C (contDiff_polynomial_eval p)
    (add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)) (Nat.cast_nonneg _)
    (abs_polynomial_eval_le' p) (abs_polynomial_deriv_le' p) T
  simpa only [Polynomial.deriv] using h
end Malliavin
