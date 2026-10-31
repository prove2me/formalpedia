-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_9_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:58:31.319006+00:00
-- url     : https://prove2.me/submissions/b01d1766-4032-407c-8482-2759ee2faa8d

import Mathlib
import Definitions.Def_OAIQ107D019
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

theorem certificate_1295_checked : certificate_1295.Valid 15 7 15 certificate_1295_q certificate_1295_edges 8 4 [] := by decide +kernel
theorem certificate_1295_valid : certificate_1295.Valid 15 7 (patternOrder [[],[],[2,2,2,2]]) (patternClique [[],[],[2,2,2,2]]) (patternEdges [[],[],[2,2,2,2]]) (patternAmount [[],[],[2,2,2,2]]) (patternEdgeCount [[],[],[2,2,2,2]]) [] := certificate_1295_checked

theorem certificate_1296_checked : certificate_1296.Valid 15 7 15 certificate_1296_q certificate_1296_edges 8 3 [] := by decide +kernel
theorem certificate_1296_valid : certificate_1296.Valid 15 7 (patternOrder [[],[],[2,3],[3]]) (patternClique [[],[],[2,3],[3]]) (patternEdges [[],[],[2,3],[3]]) (patternAmount [[],[],[2,3],[3]]) (patternEdgeCount [[],[],[2,3],[3]]) [] := certificate_1296_checked

theorem certificate_1297_checked : certificate_1297.Valid 15 7 15 certificate_1297_q certificate_1297_edges 8 4 [] := by decide +kernel
theorem certificate_1297_valid : certificate_1297.Valid 15 7 (patternOrder [[],[],[3,1,1,3]]) (patternClique [[],[],[3,1,1,3]]) (patternEdges [[],[],[3,1,1,3]]) (patternAmount [[],[],[3,1,1,3]]) (patternEdgeCount [[],[],[3,1,1,3]]) [] := certificate_1297_checked

theorem certificate_1298_checked : certificate_1298.Valid 15 7 10 certificate_1298_q certificate_1298_edges 3 3 [] := by decide +kernel
theorem certificate_1298_valid : certificate_1298.Valid 15 7 (patternOrder [[],[1],[1],[1]]) (patternClique [[],[1],[1],[1]]) (patternEdges [[],[1],[1],[1]]) (patternAmount [[],[1],[1],[1]]) (patternEdgeCount [[],[1],[1],[1]]) [] := certificate_1298_checked

theorem certificate_1299_checked : certificate_1299.Valid 15 7 11 certificate_1299_q certificate_1299_edges 4 3 [] := by decide +kernel
theorem certificate_1299_valid : certificate_1299.Valid 15 7 (patternOrder [[],[1],[1],[2]]) (patternClique [[],[1],[1],[2]]) (patternEdges [[],[1],[1],[2]]) (patternAmount [[],[1],[1],[2]]) (patternEdgeCount [[],[1],[1],[2]]) [] := certificate_1299_checked

theorem certificate_1300_checked : certificate_1300.Valid 15 7 12 certificate_1300_q certificate_1300_edges 5 3 [] := by decide +kernel
theorem certificate_1300_valid : certificate_1300.Valid 15 7 (patternOrder [[],[1],[1],[3]]) (patternClique [[],[1],[1],[3]]) (patternEdges [[],[1],[1],[3]]) (patternAmount [[],[1],[1],[3]]) (patternEdgeCount [[],[1],[1],[3]]) [] := certificate_1300_checked

theorem certificate_1301_checked : certificate_1301.Valid 15 7 13 certificate_1301_q certificate_1301_edges 6 3 [] := by decide +kernel
theorem certificate_1301_valid : certificate_1301.Valid 15 7 (patternOrder [[],[1],[1],[4]]) (patternClique [[],[1],[1],[4]]) (patternEdges [[],[1],[1],[4]]) (patternAmount [[],[1],[1],[4]]) (patternEdgeCount [[],[1],[1],[4]]) [] := certificate_1301_checked

theorem certificate_1302_checked : certificate_1302.Valid 15 7 14 certificate_1302_q certificate_1302_edges 7 3 [] := by decide +kernel
theorem certificate_1302_valid : certificate_1302.Valid 15 7 (patternOrder [[],[1],[1],[5]]) (patternClique [[],[1],[1],[5]]) (patternEdges [[],[1],[1],[5]]) (patternAmount [[],[1],[1],[5]]) (patternEdgeCount [[],[1],[1],[5]]) [] := certificate_1302_checked

theorem certificate_1303_checked : certificate_1303.Valid 15 7 15 certificate_1303_q certificate_1303_edges 8 3 [] := by decide +kernel
theorem certificate_1303_valid : certificate_1303.Valid 15 7 (patternOrder [[],[1],[1],[6]]) (patternClique [[],[1],[1],[6]]) (patternEdges [[],[1],[1],[6]]) (patternAmount [[],[1],[1],[6]]) (patternEdgeCount [[],[1],[1],[6]]) [] := certificate_1303_checked

theorem certificate_1304_checked : certificate_1304.Valid 15 7 11 certificate_1304_q certificate_1304_edges 4 4 [] := by decide +kernel
theorem certificate_1304_valid : certificate_1304.Valid 15 7 (patternOrder [[],[1],[1,1,1]]) (patternClique [[],[1],[1,1,1]]) (patternEdges [[],[1],[1,1,1]]) (patternAmount [[],[1],[1,1,1]]) (patternEdgeCount [[],[1],[1,1,1]]) [] := certificate_1304_checked

theorem certificate_1305_checked : certificate_1305.Valid 15 7 12 certificate_1305_q certificate_1305_edges 5 4 [] := by decide +kernel
theorem certificate_1305_valid : certificate_1305.Valid 15 7 (patternOrder [[],[1],[1,1,2]]) (patternClique [[],[1],[1,1,2]]) (patternEdges [[],[1],[1,1,2]]) (patternAmount [[],[1],[1,1,2]]) (patternEdgeCount [[],[1],[1,1,2]]) [] := certificate_1305_checked

theorem certificate_1306_checked : certificate_1306.Valid 15 7 13 certificate_1306_q certificate_1306_edges 6 4 [] := by decide +kernel
theorem certificate_1306_valid : certificate_1306.Valid 15 7 (patternOrder [[],[1],[1,1,3]]) (patternClique [[],[1],[1,1,3]]) (patternEdges [[],[1],[1,1,3]]) (patternAmount [[],[1],[1,1,3]]) (patternEdgeCount [[],[1],[1,1,3]]) [] := certificate_1306_checked

theorem certificate_1307_checked : certificate_1307.Valid 15 7 14 certificate_1307_q certificate_1307_edges 7 4 [] := by decide +kernel
theorem certificate_1307_valid : certificate_1307.Valid 15 7 (patternOrder [[],[1],[1,1,4]]) (patternClique [[],[1],[1,1,4]]) (patternEdges [[],[1],[1,1,4]]) (patternAmount [[],[1],[1,1,4]]) (patternEdgeCount [[],[1],[1,1,4]]) [] := certificate_1307_checked

theorem certificate_1308_checked : certificate_1308.Valid 15 7 15 certificate_1308_q certificate_1308_edges 8 4 [] := by decide +kernel
theorem certificate_1308_valid : certificate_1308.Valid 15 7 (patternOrder [[],[1],[1,1,5]]) (patternClique [[],[1],[1,1,5]]) (patternEdges [[],[1],[1,1,5]]) (patternAmount [[],[1],[1,1,5]]) (patternEdgeCount [[],[1],[1,1,5]]) [] := certificate_1308_checked

theorem certificate_1309_checked : certificate_1309.Valid 15 7 12 certificate_1309_q certificate_1309_edges 5 4 [] := by decide +kernel
theorem certificate_1309_valid : certificate_1309.Valid 15 7 (patternOrder [[],[1],[1,2,1]]) (patternClique [[],[1],[1,2,1]]) (patternEdges [[],[1],[1,2,1]]) (patternAmount [[],[1],[1,2,1]]) (patternEdgeCount [[],[1],[1,2,1]]) [] := certificate_1309_checked

theorem certificate_1310_checked : certificate_1310.Valid 15 7 13 certificate_1310_q certificate_1310_edges 6 4 [] := by decide +kernel
theorem certificate_1310_valid : certificate_1310.Valid 15 7 (patternOrder [[],[1],[1,2,2]]) (patternClique [[],[1],[1,2,2]]) (patternEdges [[],[1],[1,2,2]]) (patternAmount [[],[1],[1,2,2]]) (patternEdgeCount [[],[1],[1,2,2]]) [] := certificate_1310_checked

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

theorem patterns_15_7_9_verified_oai : ∀ D ∈ patterns_15_7_9, PatternVerified 15 7 D := by

  simp only [patterns_15_7_9, List.forall_mem_cons]

  exact ⟨⟨certificate_1295, certificate_1295_valid⟩, ⟨⟨certificate_1296, certificate_1296_valid⟩, ⟨⟨certificate_1297, certificate_1297_valid⟩, ⟨⟨certificate_1298, certificate_1298_valid⟩, ⟨⟨certificate_1299, certificate_1299_valid⟩, ⟨⟨certificate_1300, certificate_1300_valid⟩, ⟨⟨certificate_1301, certificate_1301_valid⟩, ⟨⟨certificate_1302, certificate_1302_valid⟩, ⟨⟨certificate_1303, certificate_1303_valid⟩, ⟨⟨certificate_1304, certificate_1304_valid⟩, ⟨⟨certificate_1305, certificate_1305_valid⟩, ⟨⟨certificate_1306, certificate_1306_valid⟩, ⟨⟨certificate_1307, certificate_1307_valid⟩, ⟨⟨certificate_1308, certificate_1308_valid⟩, ⟨⟨certificate_1309, certificate_1309_valid⟩, ⟨⟨certificate_1310, certificate_1310_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_9_verified_oai := @OAI.CycleClique.patterns_15_7_9_verified_oai
