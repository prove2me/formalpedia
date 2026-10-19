-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn.det_updateCol_last_of_lastRow_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/87ce6781-7ea2-4eda-ab49-6086b2e2df90

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn_det_updateCol_of_row_delta

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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn
namespace MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn
theorem _root_.solution
    {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (v : Fin (r + 1) → R)
    (hrow : ∀ j, M (Fin.last r) j = if j = Fin.last r then 1 else 0) :
    (M.updateCol (Fin.last r) v).det = v (Fin.last r) * M.det :=
  det_updateCol_of_row_delta M (Fin.last r) v hrow
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn
