-- Prove2me | solution 1 for Malliavin.deriv_exp_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:08.052938+00:00
-- url     : https://prove2.me/submissions/230c5cdc-3b34-475b-8d40-8a357cba1e59

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {g : ℝ → ℝ}
namespace Malliavin
theorem _root_.solution (c : ℝ) : deriv (fun x ↦ Real.exp (x - c)) = fun x ↦ Real.exp (x - c) := by
  funext x
  have h : HasDerivAt (fun x ↦ Real.exp (x - c)) (Real.exp (x - c) * 1) x :=
    ((hasDerivAt_id x).sub_const c).exp
  rw [h.deriv, mul_one]
end Malliavin
