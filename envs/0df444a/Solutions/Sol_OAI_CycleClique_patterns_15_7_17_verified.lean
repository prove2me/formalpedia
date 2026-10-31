-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_17_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:40:24.907645+00:00
-- url     : https://prove2.me/submissions/cc761782-8e61-4c34-8dbd-0564d4f9ad63

import Mathlib
import Definitions.Def_OAIQ107D128
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates045
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1423_checked : certificate_1423.Valid 15 7 13 certificate_1423_q certificate_1423_edges 6 5 [] := by decide +kernel
theorem certificate_1423_valid : certificate_1423.Valid 15 7 (patternOrder [[1],[1,1,1,2]]) (patternClique [[1],[1,1,1,2]]) (patternEdges [[1],[1,1,1,2]]) (patternAmount [[1],[1,1,1,2]]) (patternEdgeCount [[1],[1,1,1,2]]) [] := certificate_1423_checked

theorem certificate_1424_checked : certificate_1424.Valid 15 7 14 certificate_1424_q certificate_1424_edges 7 5 [] := by decide +kernel
theorem certificate_1424_valid : certificate_1424.Valid 15 7 (patternOrder [[1],[1,1,1,3]]) (patternClique [[1],[1,1,1,3]]) (patternEdges [[1],[1,1,1,3]]) (patternAmount [[1],[1,1,1,3]]) (patternEdgeCount [[1],[1,1,1,3]]) [] := certificate_1424_checked

theorem certificate_1425_checked : certificate_1425.Valid 15 7 15 certificate_1425_q certificate_1425_edges 8 5 [] := by decide +kernel
theorem certificate_1425_valid : certificate_1425.Valid 15 7 (patternOrder [[1],[1,1,1,4]]) (patternClique [[1],[1,1,1,4]]) (patternEdges [[1],[1,1,1,4]]) (patternAmount [[1],[1,1,1,4]]) (patternEdgeCount [[1],[1,1,1,4]]) [] := certificate_1425_checked

theorem certificate_1426_checked : certificate_1426.Valid 15 7 13 certificate_1426_q certificate_1426_edges 6 5 [] := by decide +kernel
theorem certificate_1426_valid : certificate_1426.Valid 15 7 (patternOrder [[1],[1,1,2,1]]) (patternClique [[1],[1,1,2,1]]) (patternEdges [[1],[1,1,2,1]]) (patternAmount [[1],[1,1,2,1]]) (patternEdgeCount [[1],[1,1,2,1]]) [] := certificate_1426_checked

theorem certificate_1427_checked : certificate_1427.Valid 15 7 14 certificate_1427_q certificate_1427_edges 7 5 [] := by decide +kernel
theorem certificate_1427_valid : certificate_1427.Valid 15 7 (patternOrder [[1],[1,1,2,2]]) (patternClique [[1],[1,1,2,2]]) (patternEdges [[1],[1,1,2,2]]) (patternAmount [[1],[1,1,2,2]]) (patternEdgeCount [[1],[1,1,2,2]]) [] := certificate_1427_checked

theorem certificate_1428_checked : certificate_1428.Valid 15 7 15 certificate_1428_q certificate_1428_edges 8 5 [] := by decide +kernel
theorem certificate_1428_valid : certificate_1428.Valid 15 7 (patternOrder [[1],[1,1,2,3]]) (patternClique [[1],[1,1,2,3]]) (patternEdges [[1],[1,1,2,3]]) (patternAmount [[1],[1,1,2,3]]) (patternEdgeCount [[1],[1,1,2,3]]) [] := certificate_1428_checked

theorem certificate_1429_checked : certificate_1429.Valid 15 7 14 certificate_1429_q certificate_1429_edges 7 5 [] := by decide +kernel
theorem certificate_1429_valid : certificate_1429.Valid 15 7 (patternOrder [[1],[1,1,3,1]]) (patternClique [[1],[1,1,3,1]]) (patternEdges [[1],[1,1,3,1]]) (patternAmount [[1],[1,1,3,1]]) (patternEdgeCount [[1],[1,1,3,1]]) [] := certificate_1429_checked

theorem certificate_1430_checked : certificate_1430.Valid 15 7 15 certificate_1430_q certificate_1430_edges 8 5 [] := by decide +kernel
theorem certificate_1430_valid : certificate_1430.Valid 15 7 (patternOrder [[1],[1,1,3,2]]) (patternClique [[1],[1,1,3,2]]) (patternEdges [[1],[1,1,3,2]]) (patternAmount [[1],[1,1,3,2]]) (patternEdgeCount [[1],[1,1,3,2]]) [] := certificate_1430_checked

theorem certificate_1431_checked : certificate_1431.Valid 15 7 15 certificate_1431_q certificate_1431_edges 8 5 [] := by decide +kernel
theorem certificate_1431_valid : certificate_1431.Valid 15 7 (patternOrder [[1],[1,1,4,1]]) (patternClique [[1],[1,1,4,1]]) (patternEdges [[1],[1,1,4,1]]) (patternAmount [[1],[1,1,4,1]]) (patternEdgeCount [[1],[1,1,4,1]]) [] := certificate_1431_checked

theorem certificate_1432_checked : certificate_1432.Valid 15 7 13 certificate_1432_q certificate_1432_edges 6 4 [] := by decide +kernel
theorem certificate_1432_valid : certificate_1432.Valid 15 7 (patternOrder [[1],[1,2],[2]]) (patternClique [[1],[1,2],[2]]) (patternEdges [[1],[1,2],[2]]) (patternAmount [[1],[1,2],[2]]) (patternEdgeCount [[1],[1,2],[2]]) [] := certificate_1432_checked

theorem certificate_1433_checked : certificate_1433.Valid 15 7 14 certificate_1433_q certificate_1433_edges 7 4 [] := by decide +kernel
theorem certificate_1433_valid : certificate_1433.Valid 15 7 (patternOrder [[1],[1,2],[3]]) (patternClique [[1],[1,2],[3]]) (patternEdges [[1],[1,2],[3]]) (patternAmount [[1],[1,2],[3]]) (patternEdgeCount [[1],[1,2],[3]]) [] := certificate_1433_checked

theorem certificate_1434_checked : certificate_1434.Valid 15 7 15 certificate_1434_q certificate_1434_edges 8 4 [] := by decide +kernel
theorem certificate_1434_valid : certificate_1434.Valid 15 7 (patternOrder [[1],[1,2],[4]]) (patternClique [[1],[1,2],[4]]) (patternEdges [[1],[1,2],[4]]) (patternAmount [[1],[1,2],[4]]) (patternEdgeCount [[1],[1,2],[4]]) [] := certificate_1434_checked

theorem certificate_1435_checked : certificate_1435.Valid 15 7 14 certificate_1435_q certificate_1435_edges 7 5 [] := by decide +kernel
theorem certificate_1435_valid : certificate_1435.Valid 15 7 (patternOrder [[1],[1,2,1,2]]) (patternClique [[1],[1,2,1,2]]) (patternEdges [[1],[1,2,1,2]]) (patternAmount [[1],[1,2,1,2]]) (patternEdgeCount [[1],[1,2,1,2]]) [] := certificate_1435_checked

theorem certificate_1436_checked : certificate_1436.Valid 15 7 15 certificate_1436_q certificate_1436_edges 8 5 [] := by decide +kernel
theorem certificate_1436_valid : certificate_1436.Valid 15 7 (patternOrder [[1],[1,2,1,3]]) (patternClique [[1],[1,2,1,3]]) (patternEdges [[1],[1,2,1,3]]) (patternAmount [[1],[1,2,1,3]]) (patternEdgeCount [[1],[1,2,1,3]]) [] := certificate_1436_checked

theorem certificate_1437_checked : certificate_1437.Valid 15 7 14 certificate_1437_q certificate_1437_edges 7 5 [] := by decide +kernel
theorem certificate_1437_valid : certificate_1437.Valid 15 7 (patternOrder [[1],[1,2,2,1]]) (patternClique [[1],[1,2,2,1]]) (patternEdges [[1],[1,2,2,1]]) (patternAmount [[1],[1,2,2,1]]) (patternEdgeCount [[1],[1,2,2,1]]) [] := certificate_1437_checked

theorem certificate_1438_checked : certificate_1438.Valid 15 7 15 certificate_1438_q certificate_1438_edges 8 5 [] := by decide +kernel
theorem certificate_1438_valid : certificate_1438.Valid 15 7 (patternOrder [[1],[1,2,2,2]]) (patternClique [[1],[1,2,2,2]]) (patternEdges [[1],[1,2,2,2]]) (patternAmount [[1],[1,2,2,2]]) (patternEdgeCount [[1],[1,2,2,2]]) [] := certificate_1438_checked

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

theorem patterns_15_7_17_verified_oai : ∀ D ∈ patterns_15_7_17, PatternVerified 15 7 D := by

  simp only [patterns_15_7_17, List.forall_mem_cons]

  exact ⟨⟨certificate_1423, certificate_1423_valid⟩, ⟨⟨certificate_1424, certificate_1424_valid⟩, ⟨⟨certificate_1425, certificate_1425_valid⟩, ⟨⟨certificate_1426, certificate_1426_valid⟩, ⟨⟨certificate_1427, certificate_1427_valid⟩, ⟨⟨certificate_1428, certificate_1428_valid⟩, ⟨⟨certificate_1429, certificate_1429_valid⟩, ⟨⟨certificate_1430, certificate_1430_valid⟩, ⟨⟨certificate_1431, certificate_1431_valid⟩, ⟨⟨certificate_1432, certificate_1432_valid⟩, ⟨⟨certificate_1433, certificate_1433_valid⟩, ⟨⟨certificate_1434, certificate_1434_valid⟩, ⟨⟨certificate_1435, certificate_1435_valid⟩, ⟨⟨certificate_1436, certificate_1436_valid⟩, ⟨⟨certificate_1437, certificate_1437_valid⟩, ⟨⟨certificate_1438, certificate_1438_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_17_verified_oai := @OAI.CycleClique.patterns_15_7_17_verified_oai
