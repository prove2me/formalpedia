-- Prove2me | solution 1 for MetricCodes.Spherical.HigherRepresentationGraph.StrictInterlaces.interlaces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/bb990b94-e0a8-45fc-97cf-1f58bd384b14

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
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherRepresentationGraph
namespace MetricCodes.Spherical.HigherRepresentationGraph
namespace StrictInterlaces
theorem _root_.solution {r : ℕ}
    {lam : AmbientWeight r} {μ : StabilizerWeight r}
    (h : StrictInterlaces lam μ) : Interlaces lam μ := by
  intro i
  exact ⟨(h i).1.le, (h i).2.le⟩
end StrictInterlaces
end MetricCodes.Spherical.HigherRepresentationGraph
