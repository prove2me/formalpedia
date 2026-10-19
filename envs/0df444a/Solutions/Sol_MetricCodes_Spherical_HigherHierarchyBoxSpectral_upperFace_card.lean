-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxSpectral.upperFace_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/0b3f1004-dc86-4fce-90b5-d2cfa70eb571

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
open Filter Topology
open scoped BigOperators Matrix Topology
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchyBoxSpectral
theorem _root_.solution {r m : ℕ} (i : Fin (r + 1)) :
    ((Finset.univ : Finset (BoxVertex r m)).filter
      (fun v => v i = Fin.last m)).card = (m + 1) ^ r := by
  classical
  simpa using
    (Fintype.card_filter_piFinset_const_eq_of_mem
      (Finset.univ : Finset (Fin (m + 1))) i
        (Finset.mem_univ (Fin.last m)))
end MetricCodes.Spherical.HigherHierarchyBoxSpectral
