-- Prove2me | solution 1 for MetricCodes.Spherical.HigherChannel.channelNumeratorPolynomial_eval_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/e8c6d1b1-9bca-4999-a1f1-ef4df276fe0d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherChannel
theorem _root_.solution {r : ℕ}
    (rho : ℝ) (M : Fin r → ℝ) (t : ℝ) :
    (channelNumeratorPolynomial rho M).eval t =
      (t + rho) * ∏ m : Fin r, ((t + 1 / 2) ^ 2 - M m ^ 2) := by
  unfold channelNumeratorPolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro m _
  ring
end MetricCodes.Spherical.HigherChannel
