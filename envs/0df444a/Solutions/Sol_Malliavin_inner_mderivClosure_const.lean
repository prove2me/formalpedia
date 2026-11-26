-- Prove2me | solution 1 for Malliavin.inner_mderivClosure_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:54.762893+00:00
-- url     : https://prove2.me/submissions/04f2f908-c930-4c3f-806c-06ca4fa4e288

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
import Theorems.Thm_Malliavin_inner_mderivClosure_simpleVec
import Theorems.Thm_Malliavin_simpleVec_one
import Theorems.Thm_Malliavin_simpleDiv_one

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
theorem _root_.solution {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) (h : Space μ) :
    ⟪mderivClosure μ F, (memLp_const h).toLp (fun _ ↦ h)⟫_ℝ = ⟪F, (h : Lp ℝ 2 μ)⟫_ℝ := by
  have := inner_mderivClosure_simpleVec μ hF (⟨fun _ ↦ 1, IsSmoothBounded.const 1⟩, h)
  rwa [simpleVec_one, simpleDiv_one] at this
end Malliavin
