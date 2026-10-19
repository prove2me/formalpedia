-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.WeakInterlacing.ambient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/fd38092a-ed56-4515-af7a-87e11565dd39

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
namespace WeakInterlacing
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : WeakInterlacing a b) (i : Fin (r + 1)) : 0 ≤ a i :=
  h.1.trans (h.antitone_ambient i.le_last)
end WeakInterlacing
end MetricCodes.Spherical.HigherHierarchy
