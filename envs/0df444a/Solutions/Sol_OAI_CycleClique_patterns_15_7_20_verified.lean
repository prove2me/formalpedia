-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_20_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:48:36.820008+00:00
-- url     : https://prove2.me/submissions/d8f5b80a-b200-4c28-931e-751d6a93b8a8

import Mathlib
import Definitions.Def_OAIQ107D128
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates046
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1471_checked : certificate_1471.Valid 15 7 15 certificate_1471_q certificate_1471_edges 8 5 [] := by decide +kernel
theorem certificate_1471_valid : certificate_1471.Valid 15 7 (patternOrder [[1,1,1],[2,3]]) (patternClique [[1,1,1],[2,3]]) (patternEdges [[1,1,1],[2,3]]) (patternAmount [[1,1,1],[2,3]]) (patternEdgeCount [[1,1,1],[2,3]]) [] := certificate_1471_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates047
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1472_checked : certificate_1472.Valid 15 7 13 certificate_1472_q certificate_1472_edges 6 5 [] := by decide +kernel
theorem certificate_1472_valid : certificate_1472.Valid 15 7 (patternOrder [[1,1,1,1],[2]]) (patternClique [[1,1,1,1],[2]]) (patternEdges [[1,1,1,1],[2]]) (patternAmount [[1,1,1,1],[2]]) (patternEdgeCount [[1,1,1,1],[2]]) [] := certificate_1472_checked

theorem certificate_1473_checked : certificate_1473.Valid 15 7 14 certificate_1473_q certificate_1473_edges 7 5 [] := by decide +kernel
theorem certificate_1473_valid : certificate_1473.Valid 15 7 (patternOrder [[1,1,1,1],[3]]) (patternClique [[1,1,1,1],[3]]) (patternEdges [[1,1,1,1],[3]]) (patternAmount [[1,1,1,1],[3]]) (patternEdgeCount [[1,1,1,1],[3]]) [] := certificate_1473_checked

theorem certificate_1474_checked : certificate_1474.Valid 15 7 15 certificate_1474_q certificate_1474_edges 8 5 [] := by decide +kernel
theorem certificate_1474_valid : certificate_1474.Valid 15 7 (patternOrder [[1,1,1,1],[4]]) (patternClique [[1,1,1,1],[4]]) (patternEdges [[1,1,1,1],[4]]) (patternAmount [[1,1,1,1],[4]]) (patternEdgeCount [[1,1,1,1],[4]]) [] := certificate_1474_checked

theorem certificate_1475_checked : certificate_1475.Valid 15 7 13 certificate_1475_q certificate_1475_edges 6 6 [] := by decide +kernel
theorem certificate_1475_valid : certificate_1475.Valid 15 7 (patternOrder [[1,1,1,1,1,1]]) (patternClique [[1,1,1,1,1,1]]) (patternEdges [[1,1,1,1,1,1]]) (patternAmount [[1,1,1,1,1,1]]) (patternEdgeCount [[1,1,1,1,1,1]]) [] := certificate_1475_checked

theorem certificate_1476_checked : certificate_1476.Valid 15 7 14 certificate_1476_q certificate_1476_edges 7 6 [] := by decide +kernel
theorem certificate_1476_valid : certificate_1476.Valid 15 7 (patternOrder [[1,1,1,1,1,2]]) (patternClique [[1,1,1,1,1,2]]) (patternEdges [[1,1,1,1,1,2]]) (patternAmount [[1,1,1,1,1,2]]) (patternEdgeCount [[1,1,1,1,1,2]]) [] := certificate_1476_checked

theorem certificate_1477_checked : certificate_1477.Valid 15 7 15 certificate_1477_q certificate_1477_edges 8 6 [] := by decide +kernel
theorem certificate_1477_valid : certificate_1477.Valid 15 7 (patternOrder [[1,1,1,1,1,3]]) (patternClique [[1,1,1,1,1,3]]) (patternEdges [[1,1,1,1,1,3]]) (patternAmount [[1,1,1,1,1,3]]) (patternEdgeCount [[1,1,1,1,1,3]]) [] := certificate_1477_checked

theorem certificate_1478_checked : certificate_1478.Valid 15 7 14 certificate_1478_q certificate_1478_edges 7 6 [] := by decide +kernel
theorem certificate_1478_valid : certificate_1478.Valid 15 7 (patternOrder [[1,1,1,1,2,1]]) (patternClique [[1,1,1,1,2,1]]) (patternEdges [[1,1,1,1,2,1]]) (patternAmount [[1,1,1,1,2,1]]) (patternEdgeCount [[1,1,1,1,2,1]]) [] := certificate_1478_checked

theorem certificate_1479_checked : certificate_1479.Valid 15 7 15 certificate_1479_q certificate_1479_edges 8 6 [] := by decide +kernel
theorem certificate_1479_valid : certificate_1479.Valid 15 7 (patternOrder [[1,1,1,1,2,2]]) (patternClique [[1,1,1,1,2,2]]) (patternEdges [[1,1,1,1,2,2]]) (patternAmount [[1,1,1,1,2,2]]) (patternEdgeCount [[1,1,1,1,2,2]]) [] := certificate_1479_checked

theorem certificate_1480_checked : certificate_1480.Valid 15 7 15 certificate_1480_q certificate_1480_edges 8 6 [] := by decide +kernel
theorem certificate_1480_valid : certificate_1480.Valid 15 7 (patternOrder [[1,1,1,1,3,1]]) (patternClique [[1,1,1,1,3,1]]) (patternEdges [[1,1,1,1,3,1]]) (patternAmount [[1,1,1,1,3,1]]) (patternEdgeCount [[1,1,1,1,3,1]]) [] := certificate_1480_checked

theorem certificate_1481_checked : certificate_1481.Valid 15 7 14 certificate_1481_q certificate_1481_edges 7 5 [] := by decide +kernel
theorem certificate_1481_valid : certificate_1481.Valid 15 7 (patternOrder [[1,1,1,2],[2]]) (patternClique [[1,1,1,2],[2]]) (patternEdges [[1,1,1,2],[2]]) (patternAmount [[1,1,1,2],[2]]) (patternEdgeCount [[1,1,1,2],[2]]) [] := certificate_1481_checked

theorem certificate_1482_checked : certificate_1482.Valid 15 7 15 certificate_1482_q certificate_1482_edges 8 5 [] := by decide +kernel
theorem certificate_1482_valid : certificate_1482.Valid 15 7 (patternOrder [[1,1,1,2],[3]]) (patternClique [[1,1,1,2],[3]]) (patternEdges [[1,1,1,2],[3]]) (patternAmount [[1,1,1,2],[3]]) (patternEdgeCount [[1,1,1,2],[3]]) [] := certificate_1482_checked

theorem certificate_1483_checked : certificate_1483.Valid 15 7 14 certificate_1483_q certificate_1483_edges 7 6 [] := by decide +kernel
theorem certificate_1483_valid : certificate_1483.Valid 15 7 (patternOrder [[1,1,1,2,1,1]]) (patternClique [[1,1,1,2,1,1]]) (patternEdges [[1,1,1,2,1,1]]) (patternAmount [[1,1,1,2,1,1]]) (patternEdgeCount [[1,1,1,2,1,1]]) [] := certificate_1483_checked

theorem certificate_1484_checked : certificate_1484.Valid 15 7 15 certificate_1484_q certificate_1484_edges 8 6 [] := by decide +kernel
theorem certificate_1484_valid : certificate_1484.Valid 15 7 (patternOrder [[1,1,1,2,1,2]]) (patternClique [[1,1,1,2,1,2]]) (patternEdges [[1,1,1,2,1,2]]) (patternAmount [[1,1,1,2,1,2]]) (patternEdgeCount [[1,1,1,2,1,2]]) [] := certificate_1484_checked

theorem certificate_1485_checked : certificate_1485.Valid 15 7 15 certificate_1485_q certificate_1485_edges 8 6 [] := by decide +kernel
theorem certificate_1485_valid : certificate_1485.Valid 15 7 (patternOrder [[1,1,1,2,2,1]]) (patternClique [[1,1,1,2,2,1]]) (patternEdges [[1,1,1,2,2,1]]) (patternAmount [[1,1,1,2,2,1]]) (patternEdgeCount [[1,1,1,2,2,1]]) [] := certificate_1485_checked

theorem certificate_1486_checked : certificate_1486.Valid 15 7 15 certificate_1486_q certificate_1486_edges 8 5 [] := by decide +kernel
theorem certificate_1486_valid : certificate_1486.Valid 15 7 (patternOrder [[1,1,1,3],[2]]) (patternClique [[1,1,1,3],[2]]) (patternEdges [[1,1,1,3],[2]]) (patternAmount [[1,1,1,3],[2]]) (patternEdgeCount [[1,1,1,3],[2]]) [] := certificate_1486_checked

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

theorem patterns_15_7_20_verified_oai : ∀ D ∈ patterns_15_7_20, PatternVerified 15 7 D := by

  simp only [patterns_15_7_20, List.forall_mem_cons]

  exact ⟨⟨certificate_1471, certificate_1471_valid⟩, ⟨⟨certificate_1472, certificate_1472_valid⟩, ⟨⟨certificate_1473, certificate_1473_valid⟩, ⟨⟨certificate_1474, certificate_1474_valid⟩, ⟨⟨certificate_1475, certificate_1475_valid⟩, ⟨⟨certificate_1476, certificate_1476_valid⟩, ⟨⟨certificate_1477, certificate_1477_valid⟩, ⟨⟨certificate_1478, certificate_1478_valid⟩, ⟨⟨certificate_1479, certificate_1479_valid⟩, ⟨⟨certificate_1480, certificate_1480_valid⟩, ⟨⟨certificate_1481, certificate_1481_valid⟩, ⟨⟨certificate_1482, certificate_1482_valid⟩, ⟨⟨certificate_1483, certificate_1483_valid⟩, ⟨⟨certificate_1484, certificate_1484_valid⟩, ⟨⟨certificate_1485, certificate_1485_valid⟩, ⟨⟨certificate_1486, certificate_1486_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_20_verified_oai := @OAI.CycleClique.patterns_15_7_20_verified_oai
