-- Prove2me | solution 1 for Malliavin.cylinder_growth_mem_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:32:33.375172+00:00
-- url     : https://prove2.me/submissions/6215a2fc-8fc2-48f5-9621-b9461b8890b1

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_cylinder_mem_domD12_of_dominated
import Theorems.Thm_Malliavin_growth_truncCoord_le

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin
theorem _root_.solution {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k)
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k) (L : Fin n → StrongDual ℝ W) :
    (memLp_cylinder_growth μ hf hC hfg L).toLp _ ∈ domD12 μ ∧
      mderivClosure μ ((memLp_cylinder_growth μ hf hC hfg L).toLp _) =
        (memLp_mderiv_cylinder_growth μ hf hC hfg' L).toLp _ :=
  cylinder_mem_domD12_of_dominated μ hf L hfg hfg' (growth_truncCoord_le hC L)
    (growth_coord_le hC L) (integrable_growth_sq μ C L)
end Malliavin
