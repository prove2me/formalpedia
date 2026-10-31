-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_16_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:45:15.653691+00:00
-- url     : https://prove2.me/submissions/98cd11cd-e08c-4cbf-84b4-c789deaf8213

import Mathlib
import Definitions.Def_OAIQ107D128
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates044
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1407_checked : certificate_1407.Valid 15 7 15 certificate_1407_q certificate_1407_edges 8 5 [] := by decide +kernel
theorem certificate_1407_valid : certificate_1407.Valid 15 7 (patternOrder [[],[2,1,2,1,2]]) (patternClique [[],[2,1,2,1,2]]) (patternEdges [[],[2,1,2,1,2]]) (patternAmount [[],[2,1,2,1,2]]) (patternEdgeCount [[],[2,1,2,1,2]]) [] := certificate_1407_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates045
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1408_checked : certificate_1408.Valid 15 7 15 certificate_1408_q certificate_1408_edges 8 4 [] := by decide +kernel
theorem certificate_1408_valid : certificate_1408.Valid 15 7 (patternOrder [[],[2,2],[2,2]]) (patternClique [[],[2,2],[2,2]]) (patternEdges [[],[2,2],[2,2]]) (patternAmount [[],[2,2],[2,2]]) (patternEdgeCount [[],[2,2],[2,2]]) [] := certificate_1408_checked

theorem certificate_1409_checked : certificate_1409.Valid 15 7 11 certificate_1409_q certificate_1409_edges 4 4 [] := by decide +kernel
theorem certificate_1409_valid : certificate_1409.Valid 15 7 (patternOrder [[1],[1],[1,1]]) (patternClique [[1],[1],[1,1]]) (patternEdges [[1],[1],[1,1]]) (patternAmount [[1],[1],[1,1]]) (patternEdgeCount [[1],[1],[1,1]]) [] := certificate_1409_checked

theorem certificate_1410_checked : certificate_1410.Valid 15 7 12 certificate_1410_q certificate_1410_edges 5 4 [] := by decide +kernel
theorem certificate_1410_valid : certificate_1410.Valid 15 7 (patternOrder [[1],[1],[1,2]]) (patternClique [[1],[1],[1,2]]) (patternEdges [[1],[1],[1,2]]) (patternAmount [[1],[1],[1,2]]) (patternEdgeCount [[1],[1],[1,2]]) [] := certificate_1410_checked

theorem certificate_1411_checked : certificate_1411.Valid 15 7 13 certificate_1411_q certificate_1411_edges 6 4 [] := by decide +kernel
theorem certificate_1411_valid : certificate_1411.Valid 15 7 (patternOrder [[1],[1],[1,3]]) (patternClique [[1],[1],[1,3]]) (patternEdges [[1],[1],[1,3]]) (patternAmount [[1],[1],[1,3]]) (patternEdgeCount [[1],[1],[1,3]]) [] := certificate_1411_checked

theorem certificate_1412_checked : certificate_1412.Valid 15 7 14 certificate_1412_q certificate_1412_edges 7 4 [] := by decide +kernel
theorem certificate_1412_valid : certificate_1412.Valid 15 7 (patternOrder [[1],[1],[1,4]]) (patternClique [[1],[1],[1,4]]) (patternEdges [[1],[1],[1,4]]) (patternAmount [[1],[1],[1,4]]) (patternEdgeCount [[1],[1],[1,4]]) [] := certificate_1412_checked

theorem certificate_1413_checked : certificate_1413.Valid 15 7 15 certificate_1413_q certificate_1413_edges 8 4 [] := by decide +kernel
theorem certificate_1413_valid : certificate_1413.Valid 15 7 (patternOrder [[1],[1],[1,5]]) (patternClique [[1],[1],[1,5]]) (patternEdges [[1],[1],[1,5]]) (patternAmount [[1],[1],[1,5]]) (patternEdgeCount [[1],[1],[1,5]]) [] := certificate_1413_checked

theorem certificate_1414_checked : certificate_1414.Valid 15 7 13 certificate_1414_q certificate_1414_edges 6 4 [] := by decide +kernel
theorem certificate_1414_valid : certificate_1414.Valid 15 7 (patternOrder [[1],[1],[2,2]]) (patternClique [[1],[1],[2,2]]) (patternEdges [[1],[1],[2,2]]) (patternAmount [[1],[1],[2,2]]) (patternEdgeCount [[1],[1],[2,2]]) [] := certificate_1414_checked

theorem certificate_1415_checked : certificate_1415.Valid 15 7 14 certificate_1415_q certificate_1415_edges 7 4 [] := by decide +kernel
theorem certificate_1415_valid : certificate_1415.Valid 15 7 (patternOrder [[1],[1],[2,3]]) (patternClique [[1],[1],[2,3]]) (patternEdges [[1],[1],[2,3]]) (patternAmount [[1],[1],[2,3]]) (patternEdgeCount [[1],[1],[2,3]]) [] := certificate_1415_checked

theorem certificate_1416_checked : certificate_1416.Valid 15 7 15 certificate_1416_q certificate_1416_edges 8 4 [] := by decide +kernel
theorem certificate_1416_valid : certificate_1416.Valid 15 7 (patternOrder [[1],[1],[2,4]]) (patternClique [[1],[1],[2,4]]) (patternEdges [[1],[1],[2,4]]) (patternAmount [[1],[1],[2,4]]) (patternEdgeCount [[1],[1],[2,4]]) [] := certificate_1416_checked

theorem certificate_1417_checked : certificate_1417.Valid 15 7 15 certificate_1417_q certificate_1417_edges 8 4 [] := by decide +kernel
theorem certificate_1417_valid : certificate_1417.Valid 15 7 (patternOrder [[1],[1],[3,3]]) (patternClique [[1],[1],[3,3]]) (patternEdges [[1],[1],[3,3]]) (patternAmount [[1],[1],[3,3]]) (patternEdgeCount [[1],[1],[3,3]]) [] := certificate_1417_checked

theorem certificate_1418_checked : certificate_1418.Valid 15 7 12 certificate_1418_q certificate_1418_edges 5 4 [] := by decide +kernel
theorem certificate_1418_valid : certificate_1418.Valid 15 7 (patternOrder [[1],[1,1],[2]]) (patternClique [[1],[1,1],[2]]) (patternEdges [[1],[1,1],[2]]) (patternAmount [[1],[1,1],[2]]) (patternEdgeCount [[1],[1,1],[2]]) [] := certificate_1418_checked

theorem certificate_1419_checked : certificate_1419.Valid 15 7 13 certificate_1419_q certificate_1419_edges 6 4 [] := by decide +kernel
theorem certificate_1419_valid : certificate_1419.Valid 15 7 (patternOrder [[1],[1,1],[3]]) (patternClique [[1],[1,1],[3]]) (patternEdges [[1],[1,1],[3]]) (patternAmount [[1],[1,1],[3]]) (patternEdgeCount [[1],[1,1],[3]]) [] := certificate_1419_checked

theorem certificate_1420_checked : certificate_1420.Valid 15 7 14 certificate_1420_q certificate_1420_edges 7 4 [] := by decide +kernel
theorem certificate_1420_valid : certificate_1420.Valid 15 7 (patternOrder [[1],[1,1],[4]]) (patternClique [[1],[1,1],[4]]) (patternEdges [[1],[1,1],[4]]) (patternAmount [[1],[1,1],[4]]) (patternEdgeCount [[1],[1,1],[4]]) [] := certificate_1420_checked

theorem certificate_1421_checked : certificate_1421.Valid 15 7 15 certificate_1421_q certificate_1421_edges 8 4 [] := by decide +kernel
theorem certificate_1421_valid : certificate_1421.Valid 15 7 (patternOrder [[1],[1,1],[5]]) (patternClique [[1],[1,1],[5]]) (patternEdges [[1],[1,1],[5]]) (patternAmount [[1],[1,1],[5]]) (patternEdgeCount [[1],[1,1],[5]]) [] := certificate_1421_checked

theorem certificate_1422_checked : certificate_1422.Valid 15 7 12 certificate_1422_q certificate_1422_edges 5 5 [] := by decide +kernel
theorem certificate_1422_valid : certificate_1422.Valid 15 7 (patternOrder [[1],[1,1,1,1]]) (patternClique [[1],[1,1,1,1]]) (patternEdges [[1],[1,1,1,1]]) (patternAmount [[1],[1,1,1,1]]) (patternEdgeCount [[1],[1,1,1,1]]) [] := certificate_1422_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns15x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_15_7_16_verified_oai : ∀ D ∈ patterns_15_7_16, PatternVerified 15 7 D := by

  simp only [patterns_15_7_16, List.forall_mem_cons]

  exact ⟨⟨certificate_1407, certificate_1407_valid⟩, ⟨⟨certificate_1408, certificate_1408_valid⟩, ⟨⟨certificate_1409, certificate_1409_valid⟩, ⟨⟨certificate_1410, certificate_1410_valid⟩, ⟨⟨certificate_1411, certificate_1411_valid⟩, ⟨⟨certificate_1412, certificate_1412_valid⟩, ⟨⟨certificate_1413, certificate_1413_valid⟩, ⟨⟨certificate_1414, certificate_1414_valid⟩, ⟨⟨certificate_1415, certificate_1415_valid⟩, ⟨⟨certificate_1416, certificate_1416_valid⟩, ⟨⟨certificate_1417, certificate_1417_valid⟩, ⟨⟨certificate_1418, certificate_1418_valid⟩, ⟨⟨certificate_1419, certificate_1419_valid⟩, ⟨⟨certificate_1420, certificate_1420_valid⟩, ⟨⟨certificate_1421, certificate_1421_valid⟩, ⟨⟨certificate_1422, certificate_1422_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_16_verified_oai := @OAI.CycleClique.patterns_15_7_16_verified_oai
