-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyStieltjesRatio_prepend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/ef365837-d8cf-4acf-9ab4-8aaeab799143

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (u v t : ℝ) :
    hierarchyStieltjesRatio (prependAmbient u a)
      (prependStabilizer v b) t =
        (t + quadraticCoordinate v) / (t + quadraticCoordinate u) *
          hierarchyStieltjesRatio a b t := by
  simp [hierarchyStieltjesRatio, prependAmbient, prependStabilizer,
    Fin.prod_univ_succ, div_eq_mul_inv, mul_inv_rev]
  ring
end MetricCodes.Spherical.HigherHierarchy
