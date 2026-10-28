-- Prove2me | solution 1 for OAI.RowColumn.occupied_overlap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:00:22.628932+00:00
-- url     : https://prove2.me/submissions/31b0094b-9987-40d8-bf19-cbf54788bf32

import Mathlib
import Definitions.Def_OccupiedOverlap
import Theorems.Thm_OAI_RowColumn_occupied_overlap_endpoint

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Occupied
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-- The occupied row-column overlap bound. -/
theorem RowColumn.occupied_overlap_oai : RowColumn.OccupiedOverlapEndpoint :=
  RowColumn.occupied_overlap_endpoint

end OAI
end

theorem solution : type_of% @OAI.RowColumn.occupied_overlap_oai := @OAI.RowColumn.occupied_overlap_oai
