-- Prove2me | solution 1 for Malliavin.expGrowth_truncCoord_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:36:17.597923+00:00
-- url     : https://prove2.me/submissions/e9ea4d50-3c95-4a30-a9dd-94bc1e9dbcb9

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_norm_truncCoord_le_norm

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution {n : ℕ} {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (L : Fin n → StrongDual ℝ W) (m : ℕ) (x : W) :
    C * Real.exp (c * ‖truncCoord m L x‖) ≤ C * Real.exp (c * ((∑ i, ‖L i‖) * ‖x‖)) := by
  gcongr
  exact (norm_truncCoord_le_norm m L x).trans (norm_coord_le L x)
end Malliavin
