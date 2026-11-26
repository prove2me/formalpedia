-- Prove2me | solution 1 for Malliavin.cylinder_expGrowth_mem_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:37.743302+00:00
-- url     : https://prove2.me/submissions/3ab819b6-79ff-4dc2-8ffe-88fe19dc3e7c

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_cylinder_mem_domD12_of_dominated
import Theorems.Thm_Malliavin_expGrowth_truncCoord_le

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
theorem _root_.solution {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hfg : ∀ y, |f y| ≤ C * Real.exp (c * ‖y‖))
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖)) (L : Fin n → StrongDual ℝ W) :
    (memLp_cylinder_expGrowth μ hf hC hc hfg L).toLp _ ∈ domD12 μ ∧
      mderivClosure μ ((memLp_cylinder_expGrowth μ hf hC hc hfg L).toLp _) =
        (memLp_mderiv_cylinder_expGrowth μ hf hC hc hfg' L).toLp _ :=
  cylinder_mem_domD12_of_dominated μ hf L (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L i‖) * ‖x‖)))
    hfg hfg' (expGrowth_truncCoord_le hC hc L) (expGrowth_coord_le hC hc L)
    (integrable_expGrowth_sq μ C c _)
end Malliavin
