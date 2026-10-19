-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.eventually_vertexDimension_pos_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/c72c7904-5b1f-46c2-8a88-599c6467dc2f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_eventually_signature_strictAnti

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
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.RectangularVertices
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy.RectangularVertices
theorem _root_.solution {r m : ℕ}
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 < a i) (hanti : StrictAnti a) :
    ∀ᶠ n : ℕ in atTop, ∀ v : Vertex r m,
      0 < vertexDimension a n v := by
  have hdominant :
      ∀ᶠ n : ℕ in atTop, ∀ v : Vertex r m,
        StrictAnti (signature a n v) := by
    apply eventually_all.2
    intro v
    exact eventually_signature_strictAnti a
      (fun i => (ha i).le) hanti (fun _ => v)
  filter_upwards [hdominant, eventually_ge_atTop (2 * r + 4)]
    with n hn hstable v
  exact Weyl.dimension_pos hstable (hn v).antitone
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
