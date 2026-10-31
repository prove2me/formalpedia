-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_8_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:54:29.755153+00:00
-- url     : https://prove2.me/submissions/fbcfa72c-4bd3-4cef-a900-b189a74754f3

import Mathlib
import Definitions.Def_OAIQ107D126
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates040
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1279_checked : certificate_1279.Valid 15 7 15 certificate_1279_q certificate_1279_edges 8 3 [] := by decide +kernel
theorem certificate_1279_valid : certificate_1279.Valid 15 7 (patternOrder [[],[],[1,4],[3]]) (patternClique [[],[],[1,4],[3]]) (patternEdges [[],[],[1,4],[3]]) (patternAmount [[],[],[1,4],[3]]) (patternEdgeCount [[],[],[1,4],[3]]) [] := certificate_1279_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates041
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1280_checked : certificate_1280.Valid 15 7 15 certificate_1280_q certificate_1280_edges 8 4 [] := by decide +kernel
theorem certificate_1280_valid : certificate_1280.Valid 15 7 (patternOrder [[],[],[1,4,1,2]]) (patternClique [[],[],[1,4,1,2]]) (patternEdges [[],[],[1,4,1,2]]) (patternAmount [[],[],[1,4,1,2]]) (patternEdgeCount [[],[],[1,4,1,2]]) [] := certificate_1280_checked

theorem certificate_1281_checked : certificate_1281.Valid 15 7 15 certificate_1281_q certificate_1281_edges 8 3 [] := by decide +kernel
theorem certificate_1281_valid : certificate_1281.Valid 15 7 (patternOrder [[],[],[1,5],[2]]) (patternClique [[],[],[1,5],[2]]) (patternEdges [[],[],[1,5],[2]]) (patternAmount [[],[],[1,5],[2]]) (patternEdgeCount [[],[],[1,5],[2]]) [] := certificate_1281_checked

theorem certificate_1282_checked : certificate_1282.Valid 15 7 13 certificate_1282_q certificate_1282_edges 6 3 [] := by decide +kernel
theorem certificate_1282_valid : certificate_1282.Valid 15 7 (patternOrder [[],[],[2],[2,2]]) (patternClique [[],[],[2],[2,2]]) (patternEdges [[],[],[2],[2,2]]) (patternAmount [[],[],[2],[2,2]]) (patternEdgeCount [[],[],[2],[2,2]]) [] := certificate_1282_checked

theorem certificate_1283_checked : certificate_1283.Valid 15 7 14 certificate_1283_q certificate_1283_edges 7 3 [] := by decide +kernel
theorem certificate_1283_valid : certificate_1283.Valid 15 7 (patternOrder [[],[],[2],[2,3]]) (patternClique [[],[],[2],[2,3]]) (patternEdges [[],[],[2],[2,3]]) (patternAmount [[],[],[2],[2,3]]) (patternEdgeCount [[],[],[2],[2,3]]) [] := certificate_1283_checked

theorem certificate_1284_checked : certificate_1284.Valid 15 7 15 certificate_1284_q certificate_1284_edges 8 3 [] := by decide +kernel
theorem certificate_1284_valid : certificate_1284.Valid 15 7 (patternOrder [[],[],[2],[2,4]]) (patternClique [[],[],[2],[2,4]]) (patternEdges [[],[],[2],[2,4]]) (patternAmount [[],[],[2],[2,4]]) (patternEdgeCount [[],[],[2],[2,4]]) [] := certificate_1284_checked

theorem certificate_1285_checked : certificate_1285.Valid 15 7 15 certificate_1285_q certificate_1285_edges 8 3 [] := by decide +kernel
theorem certificate_1285_valid : certificate_1285.Valid 15 7 (patternOrder [[],[],[2],[3,3]]) (patternClique [[],[],[2],[3,3]]) (patternEdges [[],[],[2],[3,3]]) (patternAmount [[],[],[2],[3,3]]) (patternEdgeCount [[],[],[2],[3,3]]) [] := certificate_1285_checked

theorem certificate_1286_checked : certificate_1286.Valid 15 7 13 certificate_1286_q certificate_1286_edges 6 4 [] := by decide +kernel
theorem certificate_1286_valid : certificate_1286.Valid 15 7 (patternOrder [[],[],[2,1,1,2]]) (patternClique [[],[],[2,1,1,2]]) (patternEdges [[],[],[2,1,1,2]]) (patternAmount [[],[],[2,1,1,2]]) (patternEdgeCount [[],[],[2,1,1,2]]) [] := certificate_1286_checked

theorem certificate_1287_checked : certificate_1287.Valid 15 7 14 certificate_1287_q certificate_1287_edges 7 4 [] := by decide +kernel
theorem certificate_1287_valid : certificate_1287.Valid 15 7 (patternOrder [[],[],[2,1,1,3]]) (patternClique [[],[],[2,1,1,3]]) (patternEdges [[],[],[2,1,1,3]]) (patternAmount [[],[],[2,1,1,3]]) (patternEdgeCount [[],[],[2,1,1,3]]) [] := certificate_1287_checked

theorem certificate_1288_checked : certificate_1288.Valid 15 7 15 certificate_1288_q certificate_1288_edges 8 4 [] := by decide +kernel
theorem certificate_1288_valid : certificate_1288.Valid 15 7 (patternOrder [[],[],[2,1,1,4]]) (patternClique [[],[],[2,1,1,4]]) (patternEdges [[],[],[2,1,1,4]]) (patternAmount [[],[],[2,1,1,4]]) (patternEdgeCount [[],[],[2,1,1,4]]) [] := certificate_1288_checked

theorem certificate_1289_checked : certificate_1289.Valid 15 7 14 certificate_1289_q certificate_1289_edges 7 4 [] := by decide +kernel
theorem certificate_1289_valid : certificate_1289.Valid 15 7 (patternOrder [[],[],[2,1,2,2]]) (patternClique [[],[],[2,1,2,2]]) (patternEdges [[],[],[2,1,2,2]]) (patternAmount [[],[],[2,1,2,2]]) (patternEdgeCount [[],[],[2,1,2,2]]) [] := certificate_1289_checked

theorem certificate_1290_checked : certificate_1290.Valid 15 7 15 certificate_1290_q certificate_1290_edges 8 4 [] := by decide +kernel
theorem certificate_1290_valid : certificate_1290.Valid 15 7 (patternOrder [[],[],[2,1,2,3]]) (patternClique [[],[],[2,1,2,3]]) (patternEdges [[],[],[2,1,2,3]]) (patternAmount [[],[],[2,1,2,3]]) (patternEdgeCount [[],[],[2,1,2,3]]) [] := certificate_1290_checked

theorem certificate_1291_checked : certificate_1291.Valid 15 7 15 certificate_1291_q certificate_1291_edges 8 4 [] := by decide +kernel
theorem certificate_1291_valid : certificate_1291.Valid 15 7 (patternOrder [[],[],[2,1,3,2]]) (patternClique [[],[],[2,1,3,2]]) (patternEdges [[],[],[2,1,3,2]]) (patternAmount [[],[],[2,1,3,2]]) (patternEdgeCount [[],[],[2,1,3,2]]) [] := certificate_1291_checked

theorem certificate_1292_checked : certificate_1292.Valid 15 7 14 certificate_1292_q certificate_1292_edges 7 3 [] := by decide +kernel
theorem certificate_1292_valid : certificate_1292.Valid 15 7 (patternOrder [[],[],[2,2],[3]]) (patternClique [[],[],[2,2],[3]]) (patternEdges [[],[],[2,2],[3]]) (patternAmount [[],[],[2,2],[3]]) (patternEdgeCount [[],[],[2,2],[3]]) [] := certificate_1292_checked

theorem certificate_1293_checked : certificate_1293.Valid 15 7 15 certificate_1293_q certificate_1293_edges 8 3 [] := by decide +kernel
theorem certificate_1293_valid : certificate_1293.Valid 15 7 (patternOrder [[],[],[2,2],[4]]) (patternClique [[],[],[2,2],[4]]) (patternEdges [[],[],[2,2],[4]]) (patternAmount [[],[],[2,2],[4]]) (patternEdgeCount [[],[],[2,2],[4]]) [] := certificate_1293_checked

theorem certificate_1294_checked : certificate_1294.Valid 15 7 15 certificate_1294_q certificate_1294_edges 8 4 [] := by decide +kernel
theorem certificate_1294_valid : certificate_1294.Valid 15 7 (patternOrder [[],[],[2,2,1,3]]) (patternClique [[],[],[2,2,1,3]]) (patternEdges [[],[],[2,2,1,3]]) (patternAmount [[],[],[2,2,1,3]]) (patternEdgeCount [[],[],[2,2,1,3]]) [] := certificate_1294_checked

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

theorem patterns_15_7_8_verified_oai : ∀ D ∈ patterns_15_7_8, PatternVerified 15 7 D := by

  simp only [patterns_15_7_8, List.forall_mem_cons]

  exact ⟨⟨certificate_1279, certificate_1279_valid⟩, ⟨⟨certificate_1280, certificate_1280_valid⟩, ⟨⟨certificate_1281, certificate_1281_valid⟩, ⟨⟨certificate_1282, certificate_1282_valid⟩, ⟨⟨certificate_1283, certificate_1283_valid⟩, ⟨⟨certificate_1284, certificate_1284_valid⟩, ⟨⟨certificate_1285, certificate_1285_valid⟩, ⟨⟨certificate_1286, certificate_1286_valid⟩, ⟨⟨certificate_1287, certificate_1287_valid⟩, ⟨⟨certificate_1288, certificate_1288_valid⟩, ⟨⟨certificate_1289, certificate_1289_valid⟩, ⟨⟨certificate_1290, certificate_1290_valid⟩, ⟨⟨certificate_1291, certificate_1291_valid⟩, ⟨⟨certificate_1292, certificate_1292_valid⟩, ⟨⟨certificate_1293, certificate_1293_valid⟩, ⟨⟨certificate_1294, certificate_1294_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_8_verified_oai := @OAI.CycleClique.patterns_15_7_8_verified_oai
