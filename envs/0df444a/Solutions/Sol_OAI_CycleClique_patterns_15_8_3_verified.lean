-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_8_3_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:08:30.757695+00:00
-- url     : https://prove2.me/submissions/0087f675-6f2a-457a-b27f-0ce2c0b61056

import Mathlib
import Definitions.Def_OAIQ107D038
import Definitions.Def_OAIQ107D039
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates049
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1563_checked : certificate_1563.Valid 15 8 14 certificate_1563_q certificate_1563_edges 6 3 [] := by decide +kernel
theorem certificate_1563_valid : certificate_1563.Valid 15 8 (patternOrder [[],[],[],[],[2,2,2]]) (patternClique [[],[],[],[],[2,2,2]]) (patternEdges [[],[],[],[],[2,2,2]]) (patternAmount [[],[],[],[],[2,2,2]]) (patternEdgeCount [[],[],[],[],[2,2,2]]) [] := certificate_1563_checked

theorem certificate_1564_checked : certificate_1564.Valid 15 8 15 certificate_1564_q certificate_1564_edges 7 3 [] := by decide +kernel
theorem certificate_1564_valid : certificate_1564.Valid 15 8 (patternOrder [[],[],[],[],[2,2,3]]) (patternClique [[],[],[],[],[2,2,3]]) (patternEdges [[],[],[],[],[2,2,3]]) (patternAmount [[],[],[],[],[2,2,3]]) (patternEdgeCount [[],[],[],[],[2,2,3]]) [] := certificate_1564_checked

theorem certificate_1565_checked : certificate_1565.Valid 15 8 15 certificate_1565_q certificate_1565_edges 7 3 [] := by decide +kernel
theorem certificate_1565_valid : certificate_1565.Valid 15 8 (patternOrder [[],[],[],[],[2,3,2]]) (patternClique [[],[],[],[],[2,3,2]]) (patternEdges [[],[],[],[],[2,3,2]]) (patternAmount [[],[],[],[],[2,3,2]]) (patternEdgeCount [[],[],[],[],[2,3,2]]) [] := certificate_1565_checked

theorem certificate_1566_checked : certificate_1566.Valid 15 8 14 certificate_1566_q certificate_1566_edges 6 2 [] := by decide +kernel
theorem certificate_1566_valid : certificate_1566.Valid 15 8 (patternOrder [[],[],[],[],[3],[3]]) (patternClique [[],[],[],[],[3],[3]]) (patternEdges [[],[],[],[],[3],[3]]) (patternAmount [[],[],[],[],[3],[3]]) (patternEdgeCount [[],[],[],[],[3],[3]]) [] := certificate_1566_checked

theorem certificate_1567_checked : certificate_1567.Valid 15 8 15 certificate_1567_q certificate_1567_edges 7 2 [] := by decide +kernel
theorem certificate_1567_valid : certificate_1567.Valid 15 8 (patternOrder [[],[],[],[],[3],[4]]) (patternClique [[],[],[],[],[3],[4]]) (patternEdges [[],[],[],[],[3],[4]]) (patternAmount [[],[],[],[],[3],[4]]) (patternEdgeCount [[],[],[],[],[3],[4]]) [] := certificate_1567_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates050
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1568_checked : certificate_1568.Valid 15 8 15 certificate_1568_q certificate_1568_edges 7 3 [] := by decide +kernel
theorem certificate_1568_valid : certificate_1568.Valid 15 8 (patternOrder [[],[],[],[],[3,1,3]]) (patternClique [[],[],[],[],[3,1,3]]) (patternEdges [[],[],[],[],[3,1,3]]) (patternAmount [[],[],[],[],[3,1,3]]) (patternEdgeCount [[],[],[],[],[3,1,3]]) [] := certificate_1568_checked

theorem certificate_1569_checked : certificate_1569.Valid 15 8 11 certificate_1569_q certificate_1569_edges 3 3 [] := by decide +kernel
theorem certificate_1569_valid : certificate_1569.Valid 15 8 (patternOrder [[],[],[],[1],[1,1]]) (patternClique [[],[],[],[1],[1,1]]) (patternEdges [[],[],[],[1],[1,1]]) (patternAmount [[],[],[],[1],[1,1]]) (patternEdgeCount [[],[],[],[1],[1,1]]) [] := certificate_1569_checked

theorem certificate_1570_checked : certificate_1570.Valid 15 8 12 certificate_1570_q certificate_1570_edges 4 3 [] := by decide +kernel
theorem certificate_1570_valid : certificate_1570.Valid 15 8 (patternOrder [[],[],[],[1],[1,2]]) (patternClique [[],[],[],[1],[1,2]]) (patternEdges [[],[],[],[1],[1,2]]) (patternAmount [[],[],[],[1],[1,2]]) (patternEdgeCount [[],[],[],[1],[1,2]]) [] := certificate_1570_checked

theorem certificate_1571_checked : certificate_1571.Valid 15 8 13 certificate_1571_q certificate_1571_edges 5 3 [] := by decide +kernel
theorem certificate_1571_valid : certificate_1571.Valid 15 8 (patternOrder [[],[],[],[1],[1,3]]) (patternClique [[],[],[],[1],[1,3]]) (patternEdges [[],[],[],[1],[1,3]]) (patternAmount [[],[],[],[1],[1,3]]) (patternEdgeCount [[],[],[],[1],[1,3]]) [] := certificate_1571_checked

theorem certificate_1572_checked : certificate_1572.Valid 15 8 14 certificate_1572_q certificate_1572_edges 6 3 [] := by decide +kernel
theorem certificate_1572_valid : certificate_1572.Valid 15 8 (patternOrder [[],[],[],[1],[1,4]]) (patternClique [[],[],[],[1],[1,4]]) (patternEdges [[],[],[],[1],[1,4]]) (patternAmount [[],[],[],[1],[1,4]]) (patternEdgeCount [[],[],[],[1],[1,4]]) [] := certificate_1572_checked

theorem certificate_1573_checked : certificate_1573.Valid 15 8 15 certificate_1573_q certificate_1573_edges 7 3 [] := by decide +kernel
theorem certificate_1573_valid : certificate_1573.Valid 15 8 (patternOrder [[],[],[],[1],[1,5]]) (patternClique [[],[],[],[1],[1,5]]) (patternEdges [[],[],[],[1],[1,5]]) (patternAmount [[],[],[],[1],[1,5]]) (patternEdgeCount [[],[],[],[1],[1,5]]) [] := certificate_1573_checked

theorem certificate_1574_checked : certificate_1574.Valid 15 8 13 certificate_1574_q certificate_1574_edges 5 3 [] := by decide +kernel
theorem certificate_1574_valid : certificate_1574.Valid 15 8 (patternOrder [[],[],[],[1],[2,2]]) (patternClique [[],[],[],[1],[2,2]]) (patternEdges [[],[],[],[1],[2,2]]) (patternAmount [[],[],[],[1],[2,2]]) (patternEdgeCount [[],[],[],[1],[2,2]]) [] := certificate_1574_checked

theorem certificate_1575_checked : certificate_1575.Valid 15 8 14 certificate_1575_q certificate_1575_edges 6 3 [] := by decide +kernel
theorem certificate_1575_valid : certificate_1575.Valid 15 8 (patternOrder [[],[],[],[1],[2,3]]) (patternClique [[],[],[],[1],[2,3]]) (patternEdges [[],[],[],[1],[2,3]]) (patternAmount [[],[],[],[1],[2,3]]) (patternEdgeCount [[],[],[],[1],[2,3]]) [] := certificate_1575_checked

theorem certificate_1576_checked : certificate_1576.Valid 15 8 15 certificate_1576_q certificate_1576_edges 7 3 [] := by decide +kernel
theorem certificate_1576_valid : certificate_1576.Valid 15 8 (patternOrder [[],[],[],[1],[2,4]]) (patternClique [[],[],[],[1],[2,4]]) (patternEdges [[],[],[],[1],[2,4]]) (patternAmount [[],[],[],[1],[2,4]]) (patternEdgeCount [[],[],[],[1],[2,4]]) [] := certificate_1576_checked

theorem certificate_1577_checked : certificate_1577.Valid 15 8 15 certificate_1577_q certificate_1577_edges 7 3 [] := by decide +kernel
theorem certificate_1577_valid : certificate_1577.Valid 15 8 (patternOrder [[],[],[],[1],[3,3]]) (patternClique [[],[],[],[1],[3,3]]) (patternEdges [[],[],[],[1],[3,3]]) (patternAmount [[],[],[],[1],[3,3]]) (patternEdgeCount [[],[],[],[1],[3,3]]) [] := certificate_1577_checked

theorem certificate_1578_checked : certificate_1578.Valid 15 8 12 certificate_1578_q certificate_1578_edges 4 3 [] := by decide +kernel
theorem certificate_1578_valid : certificate_1578.Valid 15 8 (patternOrder [[],[],[],[1,1],[2]]) (patternClique [[],[],[],[1,1],[2]]) (patternEdges [[],[],[],[1,1],[2]]) (patternAmount [[],[],[],[1,1],[2]]) (patternEdgeCount [[],[],[],[1,1],[2]]) [] := certificate_1578_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns15x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_15_8_3_verified_oai : ∀ D ∈ patterns_15_8_3, PatternVerified 15 8 D := by

  simp only [patterns_15_8_3, List.forall_mem_cons]

  exact ⟨⟨certificate_1563, certificate_1563_valid⟩, ⟨⟨certificate_1564, certificate_1564_valid⟩, ⟨⟨certificate_1565, certificate_1565_valid⟩, ⟨⟨certificate_1566, certificate_1566_valid⟩, ⟨⟨certificate_1567, certificate_1567_valid⟩, ⟨⟨certificate_1568, certificate_1568_valid⟩, ⟨⟨certificate_1569, certificate_1569_valid⟩, ⟨⟨certificate_1570, certificate_1570_valid⟩, ⟨⟨certificate_1571, certificate_1571_valid⟩, ⟨⟨certificate_1572, certificate_1572_valid⟩, ⟨⟨certificate_1573, certificate_1573_valid⟩, ⟨⟨certificate_1574, certificate_1574_valid⟩, ⟨⟨certificate_1575, certificate_1575_valid⟩, ⟨⟨certificate_1576, certificate_1576_valid⟩, ⟨⟨certificate_1577, certificate_1577_valid⟩, ⟨⟨certificate_1578, certificate_1578_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_8_3_verified_oai := @OAI.CycleClique.patterns_15_8_3_verified_oai
