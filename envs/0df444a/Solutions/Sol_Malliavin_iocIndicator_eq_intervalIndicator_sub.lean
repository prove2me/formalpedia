-- Prove2me | solution 1 for Malliavin.iocIndicator_eq_intervalIndicator_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:47:42.692108+00:00
-- url     : https://prove2.me/submissions/c6310beb-d0fa-4cf1-868d-eeacb98ef13f

import Definitions.Def_Malliavin_KernelIdentification
import Definitions.Def_Malliavin_NaturalClarkOcone
import Theorems.Thm_Malliavin_wienerIntegral_indicatorConstLp_Ioc
import Theorems.Thm_Malliavin_wienerIntegral_intervalIndicator


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
    (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b) :
    iocIndicator a b = intervalIndicator b - intervalIndicator a := by
  apply (wienerIntegralₗᵢ hB).injective
  change wienerIntegral hB (iocIndicator a b) =
    wienerIntegral hB (intervalIndicator b - intervalIndicator a)
  rw [iocIndicator, wienerIntegral_indicatorConstLp_Ioc hB hab, map_sub,
    wienerIntegral_intervalIndicator, wienerIntegral_intervalIndicator]
end Malliavin
