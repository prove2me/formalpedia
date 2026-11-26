-- Prove2me | solution 1 for Malliavin.cylinder_expGrowth_brownian_mem_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:21.288224+00:00
-- url     : https://prove2.me/submissions/9dcdb86f-6bd8-4379-8c38-3954433217c8

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_expGrowth_truncCoord_le
import Theorems.Thm_Malliavin_cylinder_brownian_mem_domD12_of_dominated

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL
namespace Malliavin
theorem _root_.solution {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hfg : ∀ y, |f y| ≤ C * Real.exp (c * ‖y‖))
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖)) (t : Fin n → ℝ≥0) :
    (memLp_cylinder_expGrowth_brownian L hL hf hC hc hfg t).toLp _ ∈ domD12 P ∧
      mderivClosure P ((memLp_cylinder_expGrowth_brownian L hL hf hC hc hfg t).toLp _) =
        ∑ i, smulLp (ofDual P (L (t i))) (cylinderPartialExp L hL hf hC hc hfg' t i) :=
  cylinder_brownian_mem_domD12_of_dominated L hL hf hfg hfg' t
    (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L (t i)‖) * ‖x‖))) (expGrowth_truncCoord_le hC hc _)
    (expGrowth_coord_le hC hc _) (integrable_expGrowth_sq P C c _)
end Malliavin
