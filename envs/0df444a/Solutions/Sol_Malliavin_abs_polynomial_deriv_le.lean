-- Prove2me | solution 1 for Malliavin.abs_polynomial_deriv_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:36:02.942855+00:00
-- url     : https://prove2.me/submissions/55505e79-50bf-40a2-ad6c-e36bcfa1af0c

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
theorem _root_.solution (p : Polynomial ℝ) {n : ℕ} (hn : p.natDegree ≤ n) (x : ℝ) :
    |deriv (fun x ↦ p.eval x) x| ≤
      (∑ i ∈ Finset.range (p.derivative.natDegree + 1), |p.derivative.coeff i|) *
        Real.exp (n * |x|) := by
  rw [Polynomial.deriv]
  exact abs_polynomial_eval_le p.derivative
    (p.natDegree_derivative_le.trans ((Nat.sub_le _ _).trans hn)) x
end Malliavin
