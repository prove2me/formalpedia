-- Prove2me | solution 1 for Malliavin.deriv_eq_inner_mderiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:04.849189+00:00
-- url     : https://prove2.me/submissions/5ae8d5af-daa7-4fa3-9a8c-e2a68af5c69b

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
import Theorems.Thm_Malliavin_hasDerivAt_inner_mderiv

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
theorem _root_.solution {F : W → ℝ} {x : W} (hF : DifferentiableAt ℝ F x)
    (h : Space μ) :
    deriv (fun ε : ℝ ↦ F (x + ε • inclusion μ h)) 0 = ⟪mderiv μ F x, h⟫_ℝ :=
  (hasDerivAt_inner_mderiv μ hF h).deriv
end Malliavin
