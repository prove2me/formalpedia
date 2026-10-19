-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyStieltjesRatio_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/ea6eaac9-80d4-4801-8deb-b94a90c26974

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
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {k r : ℕ}
    (u v : Fin k → ℝ)
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) :
    hierarchyStieltjesRatio
        (Fin.append (m := k) (n := r + 1) u a)
        (Fin.append (m := k) (n := r) v b) t =
      (∏ p : Fin k,
        (t + quadraticCoordinate (v p)) /
          (t + quadraticCoordinate (u p))) *
        hierarchyStieltjesRatio a b t := by
  unfold hierarchyStieltjesRatio
  change
    ((∏ p : Fin (k + r), _) /
      (∏ p : Fin (k + (r + 1)), _)) = _
  rw [Fin.prod_univ_add (a := k) (b := r),
    Fin.prod_univ_add (a := k) (b := r + 1)]
  simp only [Fin.append_left, Fin.append_right]
  rw [Finset.prod_div_distrib]
  simp [div_eq_mul_inv, mul_inv_rev]
  ring
end MetricCodes.Spherical.HigherHierarchy
