-- Prove2me | solution 1 for Malliavin.mderivClosure_comp_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:14.001487+00:00
-- url     : https://prove2.me/submissions/342f610b-0d0e-4f87-b3c9-c4bd3450336a

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
import Theorems.Thm_Malliavin_coeFn_smulLp
import Theorems.Thm_Malliavin_coe_space_mem_domD12
import Theorems.Thm_Malliavin_constLp_apply


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  {φ : ℝ → ℝ} {K : ℝ≥0}
namespace Malliavin
theorem _root_.solution (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    (h : Space P) :
    mderivClosure P ((memLp_comp_of_deriv_le P hφ hK (h : Lp ℝ 2 P)).toLp _) =
      smulLp h ((memLp_deriv_comp hφ hK (h : Lp ℝ 2 P)).toLp _) := by
  rw [(comp_mem_domD12 P hφ hK (coe_space_mem_domD12 P h).1).2]
  have hc : (mderivClosure P (h : Lp ℝ 2 P) : W → Space P) =ᵐ[P] fun _ ↦ h := by
    rw [(coe_space_mem_domD12 P h).2, constLp_apply]
    exact Lp.coeFn_const 2 P h
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp
      (memLp_deriv_smul_of_deriv_le P hφ hK (h : Lp ℝ 2 P) (mderivClosure P (h : Lp ℝ 2 P))),
    coeFn_smulLp h ((memLp_deriv_comp hφ hK (h : Lp ℝ 2 P)).toLp _),
    MemLp.coeFn_toLp (memLp_deriv_comp hφ hK (h : Lp ℝ 2 P)), hc] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
end Malliavin
