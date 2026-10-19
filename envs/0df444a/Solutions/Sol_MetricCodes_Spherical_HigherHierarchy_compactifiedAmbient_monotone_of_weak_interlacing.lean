-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactifiedAmbient_monotone_of_weak_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/5a15ee36-482c-43c3-98ea-60115043e00e

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
open Set Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ}
    (hinter : ∀ i : Fin r,
      A i.castSucc ≤ B i ∧ B i ≤ A i.succ) :
    Monotone A := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  exact (hinter i).1.trans (hinter i).2
end MetricCodes.Spherical.HigherHierarchy
