-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_15_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:37:49.130991+00:00
-- url     : https://prove2.me/submissions/eb072553-82c8-479b-b255-44713fef52bb

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

theorem certificate_1391_checked : certificate_1391.Valid 15 7 14 certificate_1391_q certificate_1391_edges 7 4 [] := by decide +kernel
theorem certificate_1391_valid : certificate_1391.Valid 15 7 (patternOrder [[],[1,3,1],[2]]) (patternClique [[],[1,3,1],[2]]) (patternEdges [[],[1,3,1],[2]]) (patternAmount [[],[1,3,1],[2]]) (patternEdgeCount [[],[1,3,1],[2]]) [] := certificate_1391_checked

theorem certificate_1392_checked : certificate_1392.Valid 15 7 15 certificate_1392_q certificate_1392_edges 8 4 [] := by decide +kernel
theorem certificate_1392_valid : certificate_1392.Valid 15 7 (patternOrder [[],[1,3,1],[3]]) (patternClique [[],[1,3,1],[3]]) (patternEdges [[],[1,3,1],[3]]) (patternAmount [[],[1,3,1],[3]]) (patternEdgeCount [[],[1,3,1],[3]]) [] := certificate_1392_checked

theorem certificate_1393_checked : certificate_1393.Valid 15 7 15 certificate_1393_q certificate_1393_edges 8 5 [] := by decide +kernel
theorem certificate_1393_valid : certificate_1393.Valid 15 7 (patternOrder [[],[1,3,1,1,2]]) (patternClique [[],[1,3,1,1,2]]) (patternEdges [[],[1,3,1,1,2]]) (patternAmount [[],[1,3,1,1,2]]) (patternEdgeCount [[],[1,3,1,1,2]]) [] := certificate_1393_checked

theorem certificate_1394_checked : certificate_1394.Valid 15 7 15 certificate_1394_q certificate_1394_edges 8 4 [] := by decide +kernel
theorem certificate_1394_valid : certificate_1394.Valid 15 7 (patternOrder [[],[1,3,2],[2]]) (patternClique [[],[1,3,2],[2]]) (patternEdges [[],[1,3,2],[2]]) (patternAmount [[],[1,3,2],[2]]) (patternEdgeCount [[],[1,3,2],[2]]) [] := certificate_1394_checked

theorem certificate_1395_checked : certificate_1395.Valid 15 7 15 certificate_1395_q certificate_1395_edges 8 4 [] := by decide +kernel
theorem certificate_1395_valid : certificate_1395.Valid 15 7 (patternOrder [[],[1,4,1],[2]]) (patternClique [[],[1,4,1],[2]]) (patternEdges [[],[1,4,1],[2]]) (patternAmount [[],[1,4,1],[2]]) (patternEdgeCount [[],[1,4,1],[2]]) [] := certificate_1395_checked

theorem certificate_1396_checked : certificate_1396.Valid 15 7 13 certificate_1396_q certificate_1396_edges 6 3 [] := by decide +kernel
theorem certificate_1396_valid : certificate_1396.Valid 15 7 (patternOrder [[],[2],[2],[2]]) (patternClique [[],[2],[2],[2]]) (patternEdges [[],[2],[2],[2]]) (patternAmount [[],[2],[2],[2]]) (patternEdgeCount [[],[2],[2],[2]]) [] := certificate_1396_checked

theorem certificate_1397_checked : certificate_1397.Valid 15 7 14 certificate_1397_q certificate_1397_edges 7 3 [] := by decide +kernel
theorem certificate_1397_valid : certificate_1397.Valid 15 7 (patternOrder [[],[2],[2],[3]]) (patternClique [[],[2],[2],[3]]) (patternEdges [[],[2],[2],[3]]) (patternAmount [[],[2],[2],[3]]) (patternEdgeCount [[],[2],[2],[3]]) [] := certificate_1397_checked

theorem certificate_1398_checked : certificate_1398.Valid 15 7 15 certificate_1398_q certificate_1398_edges 8 3 [] := by decide +kernel
theorem certificate_1398_valid : certificate_1398.Valid 15 7 (patternOrder [[],[2],[2],[4]]) (patternClique [[],[2],[2],[4]]) (patternEdges [[],[2],[2],[4]]) (patternAmount [[],[2],[2],[4]]) (patternEdgeCount [[],[2],[2],[4]]) [] := certificate_1398_checked

theorem certificate_1399_checked : certificate_1399.Valid 15 7 14 certificate_1399_q certificate_1399_edges 7 4 [] := by decide +kernel
theorem certificate_1399_valid : certificate_1399.Valid 15 7 (patternOrder [[],[2],[2,1,2]]) (patternClique [[],[2],[2,1,2]]) (patternEdges [[],[2],[2,1,2]]) (patternAmount [[],[2],[2,1,2]]) (patternEdgeCount [[],[2],[2,1,2]]) [] := certificate_1399_checked

theorem certificate_1400_checked : certificate_1400.Valid 15 7 15 certificate_1400_q certificate_1400_edges 8 4 [] := by decide +kernel
theorem certificate_1400_valid : certificate_1400.Valid 15 7 (patternOrder [[],[2],[2,1,3]]) (patternClique [[],[2],[2,1,3]]) (patternEdges [[],[2],[2,1,3]]) (patternAmount [[],[2],[2,1,3]]) (patternEdgeCount [[],[2],[2,1,3]]) [] := certificate_1400_checked

theorem certificate_1401_checked : certificate_1401.Valid 15 7 15 certificate_1401_q certificate_1401_edges 8 4 [] := by decide +kernel
theorem certificate_1401_valid : certificate_1401.Valid 15 7 (patternOrder [[],[2],[2,2,2]]) (patternClique [[],[2],[2,2,2]]) (patternEdges [[],[2],[2,2,2]]) (patternAmount [[],[2],[2,2,2]]) (patternEdgeCount [[],[2],[2,2,2]]) [] := certificate_1401_checked

theorem certificate_1402_checked : certificate_1402.Valid 15 7 15 certificate_1402_q certificate_1402_edges 8 3 [] := by decide +kernel
theorem certificate_1402_valid : certificate_1402.Valid 15 7 (patternOrder [[],[2],[3],[3]]) (patternClique [[],[2],[3],[3]]) (patternEdges [[],[2],[3],[3]]) (patternAmount [[],[2],[3],[3]]) (patternEdgeCount [[],[2],[3],[3]]) [] := certificate_1402_checked

theorem certificate_1403_checked : certificate_1403.Valid 15 7 14 certificate_1403_q certificate_1403_edges 7 5 [] := by decide +kernel
theorem certificate_1403_valid : certificate_1403.Valid 15 7 (patternOrder [[],[2,1,1,1,2]]) (patternClique [[],[2,1,1,1,2]]) (patternEdges [[],[2,1,1,1,2]]) (patternAmount [[],[2,1,1,1,2]]) (patternEdgeCount [[],[2,1,1,1,2]]) [] := certificate_1403_checked

theorem certificate_1404_checked : certificate_1404.Valid 15 7 15 certificate_1404_q certificate_1404_edges 8 5 [] := by decide +kernel
theorem certificate_1404_valid : certificate_1404.Valid 15 7 (patternOrder [[],[2,1,1,1,3]]) (patternClique [[],[2,1,1,1,3]]) (patternEdges [[],[2,1,1,1,3]]) (patternAmount [[],[2,1,1,1,3]]) (patternEdgeCount [[],[2,1,1,1,3]]) [] := certificate_1404_checked

theorem certificate_1405_checked : certificate_1405.Valid 15 7 15 certificate_1405_q certificate_1405_edges 8 5 [] := by decide +kernel
theorem certificate_1405_valid : certificate_1405.Valid 15 7 (patternOrder [[],[2,1,1,2,2]]) (patternClique [[],[2,1,1,2,2]]) (patternEdges [[],[2,1,1,2,2]]) (patternAmount [[],[2,1,1,2,2]]) (patternEdgeCount [[],[2,1,1,2,2]]) [] := certificate_1405_checked

theorem certificate_1406_checked : certificate_1406.Valid 15 7 15 certificate_1406_q certificate_1406_edges 8 4 [] := by decide +kernel
theorem certificate_1406_valid : certificate_1406.Valid 15 7 (patternOrder [[],[2,1,2],[3]]) (patternClique [[],[2,1,2],[3]]) (patternEdges [[],[2,1,2],[3]]) (patternAmount [[],[2,1,2],[3]]) (patternEdgeCount [[],[2,1,2],[3]]) [] := certificate_1406_checked

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

theorem patterns_15_7_15_verified_oai : ∀ D ∈ patterns_15_7_15, PatternVerified 15 7 D := by

  simp only [patterns_15_7_15, List.forall_mem_cons]

  exact ⟨⟨certificate_1391, certificate_1391_valid⟩, ⟨⟨certificate_1392, certificate_1392_valid⟩, ⟨⟨certificate_1393, certificate_1393_valid⟩, ⟨⟨certificate_1394, certificate_1394_valid⟩, ⟨⟨certificate_1395, certificate_1395_valid⟩, ⟨⟨certificate_1396, certificate_1396_valid⟩, ⟨⟨certificate_1397, certificate_1397_valid⟩, ⟨⟨certificate_1398, certificate_1398_valid⟩, ⟨⟨certificate_1399, certificate_1399_valid⟩, ⟨⟨certificate_1400, certificate_1400_valid⟩, ⟨⟨certificate_1401, certificate_1401_valid⟩, ⟨⟨certificate_1402, certificate_1402_valid⟩, ⟨⟨certificate_1403, certificate_1403_valid⟩, ⟨⟨certificate_1404, certificate_1404_valid⟩, ⟨⟨certificate_1405, certificate_1405_valid⟩, ⟨⟨certificate_1406, certificate_1406_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_15_verified_oai := @OAI.CycleClique.patterns_15_7_15_verified_oai
