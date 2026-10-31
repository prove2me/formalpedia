-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_14_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:41:09.988649+00:00
-- url     : https://prove2.me/submissions/95ba6c71-5be8-4034-9f1a-ec9b1ff57cca

import Mathlib
import Definitions.Def_OAIQ107D026
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

theorem certificate_1375_checked : certificate_1375.Valid 15 7 15 certificate_1375_q certificate_1375_edges 8 4 [] := by decide +kernel
theorem certificate_1375_valid : certificate_1375.Valid 15 7 (patternOrder [[],[1,2],[2,3]]) (patternClique [[],[1,2],[2,3]]) (patternEdges [[],[1,2],[2,3]]) (patternAmount [[],[1,2],[2,3]]) (patternEdgeCount [[],[1,2],[2,3]]) [] := certificate_1375_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates044
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1376_checked : certificate_1376.Valid 15 7 13 certificate_1376_q certificate_1376_edges 6 4 [] := by decide +kernel
theorem certificate_1376_valid : certificate_1376.Valid 15 7 (patternOrder [[],[1,2,1],[2]]) (patternClique [[],[1,2,1],[2]]) (patternEdges [[],[1,2,1],[2]]) (patternAmount [[],[1,2,1],[2]]) (patternEdgeCount [[],[1,2,1],[2]]) [] := certificate_1376_checked

theorem certificate_1377_checked : certificate_1377.Valid 15 7 14 certificate_1377_q certificate_1377_edges 7 4 [] := by decide +kernel
theorem certificate_1377_valid : certificate_1377.Valid 15 7 (patternOrder [[],[1,2,1],[3]]) (patternClique [[],[1,2,1],[3]]) (patternEdges [[],[1,2,1],[3]]) (patternAmount [[],[1,2,1],[3]]) (patternEdgeCount [[],[1,2,1],[3]]) [] := certificate_1377_checked

theorem certificate_1378_checked : certificate_1378.Valid 15 7 15 certificate_1378_q certificate_1378_edges 8 4 [] := by decide +kernel
theorem certificate_1378_valid : certificate_1378.Valid 15 7 (patternOrder [[],[1,2,1],[4]]) (patternClique [[],[1,2,1],[4]]) (patternEdges [[],[1,2,1],[4]]) (patternAmount [[],[1,2,1],[4]]) (patternEdgeCount [[],[1,2,1],[4]]) [] := certificate_1378_checked

theorem certificate_1379_checked : certificate_1379.Valid 15 7 14 certificate_1379_q certificate_1379_edges 7 5 [] := by decide +kernel
theorem certificate_1379_valid : certificate_1379.Valid 15 7 (patternOrder [[],[1,2,1,1,2]]) (patternClique [[],[1,2,1,1,2]]) (patternEdges [[],[1,2,1,1,2]]) (patternAmount [[],[1,2,1,1,2]]) (patternEdgeCount [[],[1,2,1,1,2]]) [] := certificate_1379_checked

theorem certificate_1380_checked : certificate_1380.Valid 15 7 15 certificate_1380_q certificate_1380_edges 8 5 [] := by decide +kernel
theorem certificate_1380_valid : certificate_1380.Valid 15 7 (patternOrder [[],[1,2,1,1,3]]) (patternClique [[],[1,2,1,1,3]]) (patternEdges [[],[1,2,1,1,3]]) (patternAmount [[],[1,2,1,1,3]]) (patternEdgeCount [[],[1,2,1,1,3]]) [] := certificate_1380_checked

theorem certificate_1381_checked : certificate_1381.Valid 15 7 14 certificate_1381_q certificate_1381_edges 7 5 [] := by decide +kernel
theorem certificate_1381_valid : certificate_1381.Valid 15 7 (patternOrder [[],[1,2,1,2,1]]) (patternClique [[],[1,2,1,2,1]]) (patternEdges [[],[1,2,1,2,1]]) (patternAmount [[],[1,2,1,2,1]]) (patternEdgeCount [[],[1,2,1,2,1]]) [] := certificate_1381_checked

theorem certificate_1382_checked : certificate_1382.Valid 15 7 15 certificate_1382_q certificate_1382_edges 8 5 [] := by decide +kernel
theorem certificate_1382_valid : certificate_1382.Valid 15 7 (patternOrder [[],[1,2,1,2,2]]) (patternClique [[],[1,2,1,2,2]]) (patternEdges [[],[1,2,1,2,2]]) (patternAmount [[],[1,2,1,2,2]]) (patternEdgeCount [[],[1,2,1,2,2]]) [] := certificate_1382_checked

theorem certificate_1383_checked : certificate_1383.Valid 15 7 15 certificate_1383_q certificate_1383_edges 8 5 [] := by decide +kernel
theorem certificate_1383_valid : certificate_1383.Valid 15 7 (patternOrder [[],[1,2,1,3,1]]) (patternClique [[],[1,2,1,3,1]]) (patternEdges [[],[1,2,1,3,1]]) (patternAmount [[],[1,2,1,3,1]]) (patternEdgeCount [[],[1,2,1,3,1]]) [] := certificate_1383_checked

theorem certificate_1384_checked : certificate_1384.Valid 15 7 14 certificate_1384_q certificate_1384_edges 7 4 [] := by decide +kernel
theorem certificate_1384_valid : certificate_1384.Valid 15 7 (patternOrder [[],[1,2,2],[2]]) (patternClique [[],[1,2,2],[2]]) (patternEdges [[],[1,2,2],[2]]) (patternAmount [[],[1,2,2],[2]]) (patternEdgeCount [[],[1,2,2],[2]]) [] := certificate_1384_checked

theorem certificate_1385_checked : certificate_1385.Valid 15 7 15 certificate_1385_q certificate_1385_edges 8 4 [] := by decide +kernel
theorem certificate_1385_valid : certificate_1385.Valid 15 7 (patternOrder [[],[1,2,2],[3]]) (patternClique [[],[1,2,2],[3]]) (patternEdges [[],[1,2,2],[3]]) (patternAmount [[],[1,2,2],[3]]) (patternEdgeCount [[],[1,2,2],[3]]) [] := certificate_1385_checked

theorem certificate_1386_checked : certificate_1386.Valid 15 7 15 certificate_1386_q certificate_1386_edges 8 5 [] := by decide +kernel
theorem certificate_1386_valid : certificate_1386.Valid 15 7 (patternOrder [[],[1,2,2,1,2]]) (patternClique [[],[1,2,2,1,2]]) (patternEdges [[],[1,2,2,1,2]]) (patternAmount [[],[1,2,2,1,2]]) (patternEdgeCount [[],[1,2,2,1,2]]) [] := certificate_1386_checked

theorem certificate_1387_checked : certificate_1387.Valid 15 7 15 certificate_1387_q certificate_1387_edges 8 5 [] := by decide +kernel
theorem certificate_1387_valid : certificate_1387.Valid 15 7 (patternOrder [[],[1,2,2,2,1]]) (patternClique [[],[1,2,2,2,1]]) (patternEdges [[],[1,2,2,2,1]]) (patternAmount [[],[1,2,2,2,1]]) (patternEdgeCount [[],[1,2,2,2,1]]) [] := certificate_1387_checked

theorem certificate_1388_checked : certificate_1388.Valid 15 7 15 certificate_1388_q certificate_1388_edges 8 4 [] := by decide +kernel
theorem certificate_1388_valid : certificate_1388.Valid 15 7 (patternOrder [[],[1,2,3],[2]]) (patternClique [[],[1,2,3],[2]]) (patternEdges [[],[1,2,3],[2]]) (patternAmount [[],[1,2,3],[2]]) (patternEdgeCount [[],[1,2,3],[2]]) [] := certificate_1388_checked

theorem certificate_1389_checked : certificate_1389.Valid 15 7 15 certificate_1389_q certificate_1389_edges 8 4 [] := by decide +kernel
theorem certificate_1389_valid : certificate_1389.Valid 15 7 (patternOrder [[],[1,3],[1,3]]) (patternClique [[],[1,3],[1,3]]) (patternEdges [[],[1,3],[1,3]]) (patternAmount [[],[1,3],[1,3]]) (patternEdgeCount [[],[1,3],[1,3]]) [] := certificate_1389_checked

theorem certificate_1390_checked : certificate_1390.Valid 15 7 15 certificate_1390_q certificate_1390_edges 8 4 [] := by decide +kernel
theorem certificate_1390_valid : certificate_1390.Valid 15 7 (patternOrder [[],[1,3],[2,2]]) (patternClique [[],[1,3],[2,2]]) (patternEdges [[],[1,3],[2,2]]) (patternAmount [[],[1,3],[2,2]]) (patternEdgeCount [[],[1,3],[2,2]]) [] := certificate_1390_checked

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

theorem patterns_15_7_14_verified_oai : ∀ D ∈ patterns_15_7_14, PatternVerified 15 7 D := by

  simp only [patterns_15_7_14, List.forall_mem_cons]

  exact ⟨⟨certificate_1375, certificate_1375_valid⟩, ⟨⟨certificate_1376, certificate_1376_valid⟩, ⟨⟨certificate_1377, certificate_1377_valid⟩, ⟨⟨certificate_1378, certificate_1378_valid⟩, ⟨⟨certificate_1379, certificate_1379_valid⟩, ⟨⟨certificate_1380, certificate_1380_valid⟩, ⟨⟨certificate_1381, certificate_1381_valid⟩, ⟨⟨certificate_1382, certificate_1382_valid⟩, ⟨⟨certificate_1383, certificate_1383_valid⟩, ⟨⟨certificate_1384, certificate_1384_valid⟩, ⟨⟨certificate_1385, certificate_1385_valid⟩, ⟨⟨certificate_1386, certificate_1386_valid⟩, ⟨⟨certificate_1387, certificate_1387_valid⟩, ⟨⟨certificate_1388, certificate_1388_valid⟩, ⟨⟨certificate_1389, certificate_1389_valid⟩, ⟨⟨certificate_1390, certificate_1390_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_14_verified_oai := @OAI.CycleClique.patterns_15_7_14_verified_oai
