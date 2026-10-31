-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_10_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:35:58.861927+00:00
-- url     : https://prove2.me/submissions/61c35e94-6e74-4ea1-a200-1fd5d844a3d1

import Mathlib
import Definitions.Def_OAIQ107D126
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates041
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1311_checked : certificate_1311.Valid 15 7 14 certificate_1311_q certificate_1311_edges 7 4 [] := by decide +kernel
theorem certificate_1311_valid : certificate_1311.Valid 15 7 (patternOrder [[],[1],[1,2,3]]) (patternClique [[],[1],[1,2,3]]) (patternEdges [[],[1],[1,2,3]]) (patternAmount [[],[1],[1,2,3]]) (patternEdgeCount [[],[1],[1,2,3]]) [] := certificate_1311_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates042
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1312_checked : certificate_1312.Valid 15 7 15 certificate_1312_q certificate_1312_edges 8 4 [] := by decide +kernel
theorem certificate_1312_valid : certificate_1312.Valid 15 7 (patternOrder [[],[1],[1,2,4]]) (patternClique [[],[1],[1,2,4]]) (patternEdges [[],[1],[1,2,4]]) (patternAmount [[],[1],[1,2,4]]) (patternEdgeCount [[],[1],[1,2,4]]) [] := certificate_1312_checked

theorem certificate_1313_checked : certificate_1313.Valid 15 7 13 certificate_1313_q certificate_1313_edges 6 4 [] := by decide +kernel
theorem certificate_1313_valid : certificate_1313.Valid 15 7 (patternOrder [[],[1],[1,3,1]]) (patternClique [[],[1],[1,3,1]]) (patternEdges [[],[1],[1,3,1]]) (patternAmount [[],[1],[1,3,1]]) (patternEdgeCount [[],[1],[1,3,1]]) [] := certificate_1313_checked

theorem certificate_1314_checked : certificate_1314.Valid 15 7 14 certificate_1314_q certificate_1314_edges 7 4 [] := by decide +kernel
theorem certificate_1314_valid : certificate_1314.Valid 15 7 (patternOrder [[],[1],[1,3,2]]) (patternClique [[],[1],[1,3,2]]) (patternEdges [[],[1],[1,3,2]]) (patternAmount [[],[1],[1,3,2]]) (patternEdgeCount [[],[1],[1,3,2]]) [] := certificate_1314_checked

theorem certificate_1315_checked : certificate_1315.Valid 15 7 15 certificate_1315_q certificate_1315_edges 8 4 [] := by decide +kernel
theorem certificate_1315_valid : certificate_1315.Valid 15 7 (patternOrder [[],[1],[1,3,3]]) (patternClique [[],[1],[1,3,3]]) (patternEdges [[],[1],[1,3,3]]) (patternAmount [[],[1],[1,3,3]]) (patternEdgeCount [[],[1],[1,3,3]]) [] := certificate_1315_checked

theorem certificate_1316_checked : certificate_1316.Valid 15 7 14 certificate_1316_q certificate_1316_edges 7 4 [] := by decide +kernel
theorem certificate_1316_valid : certificate_1316.Valid 15 7 (patternOrder [[],[1],[1,4,1]]) (patternClique [[],[1],[1,4,1]]) (patternEdges [[],[1],[1,4,1]]) (patternAmount [[],[1],[1,4,1]]) (patternEdgeCount [[],[1],[1,4,1]]) [] := certificate_1316_checked

theorem certificate_1317_checked : certificate_1317.Valid 15 7 15 certificate_1317_q certificate_1317_edges 8 4 [] := by decide +kernel
theorem certificate_1317_valid : certificate_1317.Valid 15 7 (patternOrder [[],[1],[1,4,2]]) (patternClique [[],[1],[1,4,2]]) (patternEdges [[],[1],[1,4,2]]) (patternAmount [[],[1],[1,4,2]]) (patternEdgeCount [[],[1],[1,4,2]]) [] := certificate_1317_checked

theorem certificate_1318_checked : certificate_1318.Valid 15 7 15 certificate_1318_q certificate_1318_edges 8 4 [] := by decide +kernel
theorem certificate_1318_valid : certificate_1318.Valid 15 7 (patternOrder [[],[1],[1,5,1]]) (patternClique [[],[1],[1,5,1]]) (patternEdges [[],[1],[1,5,1]]) (patternAmount [[],[1],[1,5,1]]) (patternEdgeCount [[],[1],[1,5,1]]) [] := certificate_1318_checked

theorem certificate_1319_checked : certificate_1319.Valid 15 7 12 certificate_1319_q certificate_1319_edges 5 3 [] := by decide +kernel
theorem certificate_1319_valid : certificate_1319.Valid 15 7 (patternOrder [[],[1],[2],[2]]) (patternClique [[],[1],[2],[2]]) (patternEdges [[],[1],[2],[2]]) (patternAmount [[],[1],[2],[2]]) (patternEdgeCount [[],[1],[2],[2]]) [] := certificate_1319_checked

theorem certificate_1320_checked : certificate_1320.Valid 15 7 13 certificate_1320_q certificate_1320_edges 6 3 [] := by decide +kernel
theorem certificate_1320_valid : certificate_1320.Valid 15 7 (patternOrder [[],[1],[2],[3]]) (patternClique [[],[1],[2],[3]]) (patternEdges [[],[1],[2],[3]]) (patternAmount [[],[1],[2],[3]]) (patternEdgeCount [[],[1],[2],[3]]) [] := certificate_1320_checked

theorem certificate_1321_checked : certificate_1321.Valid 15 7 14 certificate_1321_q certificate_1321_edges 7 3 [] := by decide +kernel
theorem certificate_1321_valid : certificate_1321.Valid 15 7 (patternOrder [[],[1],[2],[4]]) (patternClique [[],[1],[2],[4]]) (patternEdges [[],[1],[2],[4]]) (patternAmount [[],[1],[2],[4]]) (patternEdgeCount [[],[1],[2],[4]]) [] := certificate_1321_checked

theorem certificate_1322_checked : certificate_1322.Valid 15 7 15 certificate_1322_q certificate_1322_edges 8 3 [] := by decide +kernel
theorem certificate_1322_valid : certificate_1322.Valid 15 7 (patternOrder [[],[1],[2],[5]]) (patternClique [[],[1],[2],[5]]) (patternEdges [[],[1],[2],[5]]) (patternAmount [[],[1],[2],[5]]) (patternEdgeCount [[],[1],[2],[5]]) [] := certificate_1322_checked

theorem certificate_1323_checked : certificate_1323.Valid 15 7 13 certificate_1323_q certificate_1323_edges 6 4 [] := by decide +kernel
theorem certificate_1323_valid : certificate_1323.Valid 15 7 (patternOrder [[],[1],[2,1,2]]) (patternClique [[],[1],[2,1,2]]) (patternEdges [[],[1],[2,1,2]]) (patternAmount [[],[1],[2,1,2]]) (patternEdgeCount [[],[1],[2,1,2]]) [] := certificate_1323_checked

theorem certificate_1324_checked : certificate_1324.Valid 15 7 14 certificate_1324_q certificate_1324_edges 7 4 [] := by decide +kernel
theorem certificate_1324_valid : certificate_1324.Valid 15 7 (patternOrder [[],[1],[2,1,3]]) (patternClique [[],[1],[2,1,3]]) (patternEdges [[],[1],[2,1,3]]) (patternAmount [[],[1],[2,1,3]]) (patternEdgeCount [[],[1],[2,1,3]]) [] := certificate_1324_checked

theorem certificate_1325_checked : certificate_1325.Valid 15 7 15 certificate_1325_q certificate_1325_edges 8 4 [] := by decide +kernel
theorem certificate_1325_valid : certificate_1325.Valid 15 7 (patternOrder [[],[1],[2,1,4]]) (patternClique [[],[1],[2,1,4]]) (patternEdges [[],[1],[2,1,4]]) (patternAmount [[],[1],[2,1,4]]) (patternEdgeCount [[],[1],[2,1,4]]) [] := certificate_1325_checked

theorem certificate_1326_checked : certificate_1326.Valid 15 7 14 certificate_1326_q certificate_1326_edges 7 4 [] := by decide +kernel
theorem certificate_1326_valid : certificate_1326.Valid 15 7 (patternOrder [[],[1],[2,2,2]]) (patternClique [[],[1],[2,2,2]]) (patternEdges [[],[1],[2,2,2]]) (patternAmount [[],[1],[2,2,2]]) (patternEdgeCount [[],[1],[2,2,2]]) [] := certificate_1326_checked

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

theorem patterns_15_7_10_verified_oai : ∀ D ∈ patterns_15_7_10, PatternVerified 15 7 D := by

  simp only [patterns_15_7_10, List.forall_mem_cons]

  exact ⟨⟨certificate_1311, certificate_1311_valid⟩, ⟨⟨certificate_1312, certificate_1312_valid⟩, ⟨⟨certificate_1313, certificate_1313_valid⟩, ⟨⟨certificate_1314, certificate_1314_valid⟩, ⟨⟨certificate_1315, certificate_1315_valid⟩, ⟨⟨certificate_1316, certificate_1316_valid⟩, ⟨⟨certificate_1317, certificate_1317_valid⟩, ⟨⟨certificate_1318, certificate_1318_valid⟩, ⟨⟨certificate_1319, certificate_1319_valid⟩, ⟨⟨certificate_1320, certificate_1320_valid⟩, ⟨⟨certificate_1321, certificate_1321_valid⟩, ⟨⟨certificate_1322, certificate_1322_valid⟩, ⟨⟨certificate_1323, certificate_1323_valid⟩, ⟨⟨certificate_1324, certificate_1324_valid⟩, ⟨⟨certificate_1325, certificate_1325_valid⟩, ⟨⟨certificate_1326, certificate_1326_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_10_verified_oai := @OAI.CycleClique.patterns_15_7_10_verified_oai
