-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_13_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:34:06.882103+00:00
-- url     : https://prove2.me/submissions/16dd51f4-2f33-46a2-b8f6-66e0c550dfda

import Mathlib
import Definitions.Def_OAIQ107D127
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates043
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1359_checked : certificate_1359.Valid 15 7 14 certificate_1359_q certificate_1359_edges 7 5 [] := by decide +kernel
theorem certificate_1359_valid : certificate_1359.Valid 15 7 (patternOrder [[],[1,1,2,1,2]]) (patternClique [[],[1,1,2,1,2]]) (patternEdges [[],[1,1,2,1,2]]) (patternAmount [[],[1,1,2,1,2]]) (patternEdgeCount [[],[1,1,2,1,2]]) [] := certificate_1359_checked

theorem certificate_1360_checked : certificate_1360.Valid 15 7 15 certificate_1360_q certificate_1360_edges 8 5 [] := by decide +kernel
theorem certificate_1360_valid : certificate_1360.Valid 15 7 (patternOrder [[],[1,1,2,1,3]]) (patternClique [[],[1,1,2,1,3]]) (patternEdges [[],[1,1,2,1,3]]) (patternAmount [[],[1,1,2,1,3]]) (patternEdgeCount [[],[1,1,2,1,3]]) [] := certificate_1360_checked

theorem certificate_1361_checked : certificate_1361.Valid 15 7 14 certificate_1361_q certificate_1361_edges 7 5 [] := by decide +kernel
theorem certificate_1361_valid : certificate_1361.Valid 15 7 (patternOrder [[],[1,1,2,2,1]]) (patternClique [[],[1,1,2,2,1]]) (patternEdges [[],[1,1,2,2,1]]) (patternAmount [[],[1,1,2,2,1]]) (patternEdgeCount [[],[1,1,2,2,1]]) [] := certificate_1361_checked

theorem certificate_1362_checked : certificate_1362.Valid 15 7 15 certificate_1362_q certificate_1362_edges 8 5 [] := by decide +kernel
theorem certificate_1362_valid : certificate_1362.Valid 15 7 (patternOrder [[],[1,1,2,2,2]]) (patternClique [[],[1,1,2,2,2]]) (patternEdges [[],[1,1,2,2,2]]) (patternAmount [[],[1,1,2,2,2]]) (patternEdgeCount [[],[1,1,2,2,2]]) [] := certificate_1362_checked

theorem certificate_1363_checked : certificate_1363.Valid 15 7 15 certificate_1363_q certificate_1363_edges 8 5 [] := by decide +kernel
theorem certificate_1363_valid : certificate_1363.Valid 15 7 (patternOrder [[],[1,1,2,3,1]]) (patternClique [[],[1,1,2,3,1]]) (patternEdges [[],[1,1,2,3,1]]) (patternAmount [[],[1,1,2,3,1]]) (patternEdgeCount [[],[1,1,2,3,1]]) [] := certificate_1363_checked

theorem certificate_1364_checked : certificate_1364.Valid 15 7 14 certificate_1364_q certificate_1364_edges 7 4 [] := by decide +kernel
theorem certificate_1364_valid : certificate_1364.Valid 15 7 (patternOrder [[],[1,1,3],[2]]) (patternClique [[],[1,1,3],[2]]) (patternEdges [[],[1,1,3],[2]]) (patternAmount [[],[1,1,3],[2]]) (patternEdgeCount [[],[1,1,3],[2]]) [] := certificate_1364_checked

theorem certificate_1365_checked : certificate_1365.Valid 15 7 15 certificate_1365_q certificate_1365_edges 8 4 [] := by decide +kernel
theorem certificate_1365_valid : certificate_1365.Valid 15 7 (patternOrder [[],[1,1,3],[3]]) (patternClique [[],[1,1,3],[3]]) (patternEdges [[],[1,1,3],[3]]) (patternAmount [[],[1,1,3],[3]]) (patternEdgeCount [[],[1,1,3],[3]]) [] := certificate_1365_checked

theorem certificate_1366_checked : certificate_1366.Valid 15 7 14 certificate_1366_q certificate_1366_edges 7 5 [] := by decide +kernel
theorem certificate_1366_valid : certificate_1366.Valid 15 7 (patternOrder [[],[1,1,3,1,1]]) (patternClique [[],[1,1,3,1,1]]) (patternEdges [[],[1,1,3,1,1]]) (patternAmount [[],[1,1,3,1,1]]) (patternEdgeCount [[],[1,1,3,1,1]]) [] := certificate_1366_checked

theorem certificate_1367_checked : certificate_1367.Valid 15 7 15 certificate_1367_q certificate_1367_edges 8 5 [] := by decide +kernel
theorem certificate_1367_valid : certificate_1367.Valid 15 7 (patternOrder [[],[1,1,3,1,2]]) (patternClique [[],[1,1,3,1,2]]) (patternEdges [[],[1,1,3,1,2]]) (patternAmount [[],[1,1,3,1,2]]) (patternEdgeCount [[],[1,1,3,1,2]]) [] := certificate_1367_checked

theorem certificate_1368_checked : certificate_1368.Valid 15 7 15 certificate_1368_q certificate_1368_edges 8 5 [] := by decide +kernel
theorem certificate_1368_valid : certificate_1368.Valid 15 7 (patternOrder [[],[1,1,3,2,1]]) (patternClique [[],[1,1,3,2,1]]) (patternEdges [[],[1,1,3,2,1]]) (patternAmount [[],[1,1,3,2,1]]) (patternEdgeCount [[],[1,1,3,2,1]]) [] := certificate_1368_checked

theorem certificate_1369_checked : certificate_1369.Valid 15 7 15 certificate_1369_q certificate_1369_edges 8 4 [] := by decide +kernel
theorem certificate_1369_valid : certificate_1369.Valid 15 7 (patternOrder [[],[1,1,4],[2]]) (patternClique [[],[1,1,4],[2]]) (patternEdges [[],[1,1,4],[2]]) (patternAmount [[],[1,1,4],[2]]) (patternEdgeCount [[],[1,1,4],[2]]) [] := certificate_1369_checked

theorem certificate_1370_checked : certificate_1370.Valid 15 7 15 certificate_1370_q certificate_1370_edges 8 5 [] := by decide +kernel
theorem certificate_1370_valid : certificate_1370.Valid 15 7 (patternOrder [[],[1,1,4,1,1]]) (patternClique [[],[1,1,4,1,1]]) (patternEdges [[],[1,1,4,1,1]]) (patternAmount [[],[1,1,4,1,1]]) (patternEdgeCount [[],[1,1,4,1,1]]) [] := certificate_1370_checked

theorem certificate_1371_checked : certificate_1371.Valid 15 7 13 certificate_1371_q certificate_1371_edges 6 4 [] := by decide +kernel
theorem certificate_1371_valid : certificate_1371.Valid 15 7 (patternOrder [[],[1,2],[1,2]]) (patternClique [[],[1,2],[1,2]]) (patternEdges [[],[1,2],[1,2]]) (patternAmount [[],[1,2],[1,2]]) (patternEdgeCount [[],[1,2],[1,2]]) [] := certificate_1371_checked

theorem certificate_1372_checked : certificate_1372.Valid 15 7 14 certificate_1372_q certificate_1372_edges 7 4 [] := by decide +kernel
theorem certificate_1372_valid : certificate_1372.Valid 15 7 (patternOrder [[],[1,2],[1,3]]) (patternClique [[],[1,2],[1,3]]) (patternEdges [[],[1,2],[1,3]]) (patternAmount [[],[1,2],[1,3]]) (patternEdgeCount [[],[1,2],[1,3]]) [] := certificate_1372_checked

theorem certificate_1373_checked : certificate_1373.Valid 15 7 15 certificate_1373_q certificate_1373_edges 8 4 [] := by decide +kernel
theorem certificate_1373_valid : certificate_1373.Valid 15 7 (patternOrder [[],[1,2],[1,4]]) (patternClique [[],[1,2],[1,4]]) (patternEdges [[],[1,2],[1,4]]) (patternAmount [[],[1,2],[1,4]]) (patternEdgeCount [[],[1,2],[1,4]]) [] := certificate_1373_checked

theorem certificate_1374_checked : certificate_1374.Valid 15 7 14 certificate_1374_q certificate_1374_edges 7 4 [] := by decide +kernel
theorem certificate_1374_valid : certificate_1374.Valid 15 7 (patternOrder [[],[1,2],[2,2]]) (patternClique [[],[1,2],[2,2]]) (patternEdges [[],[1,2],[2,2]]) (patternAmount [[],[1,2],[2,2]]) (patternEdgeCount [[],[1,2],[2,2]]) [] := certificate_1374_checked

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

theorem patterns_15_7_13_verified_oai : ∀ D ∈ patterns_15_7_13, PatternVerified 15 7 D := by

  simp only [patterns_15_7_13, List.forall_mem_cons]

  exact ⟨⟨certificate_1359, certificate_1359_valid⟩, ⟨⟨certificate_1360, certificate_1360_valid⟩, ⟨⟨certificate_1361, certificate_1361_valid⟩, ⟨⟨certificate_1362, certificate_1362_valid⟩, ⟨⟨certificate_1363, certificate_1363_valid⟩, ⟨⟨certificate_1364, certificate_1364_valid⟩, ⟨⟨certificate_1365, certificate_1365_valid⟩, ⟨⟨certificate_1366, certificate_1366_valid⟩, ⟨⟨certificate_1367, certificate_1367_valid⟩, ⟨⟨certificate_1368, certificate_1368_valid⟩, ⟨⟨certificate_1369, certificate_1369_valid⟩, ⟨⟨certificate_1370, certificate_1370_valid⟩, ⟨⟨certificate_1371, certificate_1371_valid⟩, ⟨⟨certificate_1372, certificate_1372_valid⟩, ⟨⟨certificate_1373, certificate_1373_valid⟩, ⟨⟨certificate_1374, certificate_1374_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_13_verified_oai := @OAI.CycleClique.patterns_15_7_13_verified_oai
