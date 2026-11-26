-- Prove2me | solution 1 for Malliavin.mderivClosure_eq_of_forall_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:09.313083+00:00
-- url     : https://prove2.me/submissions/334beead-4627-448c-bde0-d1260aa427c0

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
import Theorems.Thm_Malliavin_inner_mderivClosure_simpleVec

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
theorem _root_.solution {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ)
    {η : Lp (Space μ) 2 μ} (hη : ∀ k, ⟪η, simpleVec μ k⟫_ℝ = ⟪F, simpleDiv μ k⟫_ℝ) :
    mderivClosure μ F = η := by
  rw [← sub_eq_zero]
  apply isTotal_simpleVec μ
  intro k
  have hsub := inner_sub_left (𝕜 := ℝ) (mderivClosure μ F) η (simpleVec μ k)
  rw [hsub, inner_mderivClosure_simpleVec μ hF k, hη k, sub_self]
end Malliavin
