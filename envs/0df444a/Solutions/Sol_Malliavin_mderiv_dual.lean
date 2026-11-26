-- Prove2me | solution 1 for Malliavin.mderiv_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:32.206812+00:00
-- url     : https://prove2.me/submissions/ad161015-9c9c-4e0d-bc14-36bc32d9dea0

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
import Theorems.Thm_Malliavin_CameronMartin_apply_inclusion


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin
theorem _root_.solution (L : StrongDual ℝ W) (x : W) : mderiv μ (⇑L) x = ofDual μ L := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_mderiv, L.fderiv, apply_inclusion]
end Malliavin
