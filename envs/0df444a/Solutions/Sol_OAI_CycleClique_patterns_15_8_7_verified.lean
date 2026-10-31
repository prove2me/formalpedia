-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_8_7_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:18:48.260045+00:00
-- url     : https://prove2.me/submissions/30cf0f09-c0ae-42fe-8790-8dbc699985ff

import Mathlib
import Definitions.Def_OAIQ107D129
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates051
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1627_checked : certificate_1627.Valid 15 8 15 certificate_1627_q certificate_1627_edges 7 3 [] := by decide +kernel
theorem certificate_1627_valid : certificate_1627.Valid 15 8 (patternOrder [[],[],[1],[2],[4]]) (patternClique [[],[],[1],[2],[4]]) (patternEdges [[],[],[1],[2],[4]]) (patternAmount [[],[],[1],[2],[4]]) (patternEdgeCount [[],[],[1],[2],[4]]) [] := certificate_1627_checked

theorem certificate_1628_checked : certificate_1628.Valid 15 8 14 certificate_1628_q certificate_1628_edges 6 4 [] := by decide +kernel
theorem certificate_1628_valid : certificate_1628.Valid 15 8 (patternOrder [[],[],[1],[2,1,2]]) (patternClique [[],[],[1],[2,1,2]]) (patternEdges [[],[],[1],[2,1,2]]) (patternAmount [[],[],[1],[2,1,2]]) (patternEdgeCount [[],[],[1],[2,1,2]]) [] := certificate_1628_checked

theorem certificate_1629_checked : certificate_1629.Valid 15 8 15 certificate_1629_q certificate_1629_edges 7 4 [] := by decide +kernel
theorem certificate_1629_valid : certificate_1629.Valid 15 8 (patternOrder [[],[],[1],[2,1,3]]) (patternClique [[],[],[1],[2,1,3]]) (patternEdges [[],[],[1],[2,1,3]]) (patternAmount [[],[],[1],[2,1,3]]) (patternEdgeCount [[],[],[1],[2,1,3]]) [] := certificate_1629_checked

theorem certificate_1630_checked : certificate_1630.Valid 15 8 15 certificate_1630_q certificate_1630_edges 7 4 [] := by decide +kernel
theorem certificate_1630_valid : certificate_1630.Valid 15 8 (patternOrder [[],[],[1],[2,2,2]]) (patternClique [[],[],[1],[2,2,2]]) (patternEdges [[],[],[1],[2,2,2]]) (patternAmount [[],[],[1],[2,2,2]]) (patternEdgeCount [[],[],[1],[2,2,2]]) [] := certificate_1630_checked

theorem certificate_1631_checked : certificate_1631.Valid 15 8 15 certificate_1631_q certificate_1631_edges 7 3 [] := by decide +kernel
theorem certificate_1631_valid : certificate_1631.Valid 15 8 (patternOrder [[],[],[1],[3],[3]]) (patternClique [[],[],[1],[3],[3]]) (patternEdges [[],[],[1],[3],[3]]) (patternAmount [[],[],[1],[3],[3]]) (patternEdgeCount [[],[],[1],[3],[3]]) [] := certificate_1631_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates052
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1632_checked : certificate_1632.Valid 15 8 12 certificate_1632_q certificate_1632_edges 4 4 [] := by decide +kernel
theorem certificate_1632_valid : certificate_1632.Valid 15 8 (patternOrder [[],[],[1,1],[1,1]]) (patternClique [[],[],[1,1],[1,1]]) (patternEdges [[],[],[1,1],[1,1]]) (patternAmount [[],[],[1,1],[1,1]]) (patternEdgeCount [[],[],[1,1],[1,1]]) [] := certificate_1632_checked

theorem certificate_1633_checked : certificate_1633.Valid 15 8 13 certificate_1633_q certificate_1633_edges 5 4 [] := by decide +kernel
theorem certificate_1633_valid : certificate_1633.Valid 15 8 (patternOrder [[],[],[1,1],[1,2]]) (patternClique [[],[],[1,1],[1,2]]) (patternEdges [[],[],[1,1],[1,2]]) (patternAmount [[],[],[1,1],[1,2]]) (patternEdgeCount [[],[],[1,1],[1,2]]) [] := certificate_1633_checked

theorem certificate_1634_checked : certificate_1634.Valid 15 8 14 certificate_1634_q certificate_1634_edges 6 4 [] := by decide +kernel
theorem certificate_1634_valid : certificate_1634.Valid 15 8 (patternOrder [[],[],[1,1],[1,3]]) (patternClique [[],[],[1,1],[1,3]]) (patternEdges [[],[],[1,1],[1,3]]) (patternAmount [[],[],[1,1],[1,3]]) (patternEdgeCount [[],[],[1,1],[1,3]]) [] := certificate_1634_checked

theorem certificate_1635_checked : certificate_1635.Valid 15 8 15 certificate_1635_q certificate_1635_edges 7 4 [] := by decide +kernel
theorem certificate_1635_valid : certificate_1635.Valid 15 8 (patternOrder [[],[],[1,1],[1,4]]) (patternClique [[],[],[1,1],[1,4]]) (patternEdges [[],[],[1,1],[1,4]]) (patternAmount [[],[],[1,1],[1,4]]) (patternEdgeCount [[],[],[1,1],[1,4]]) [] := certificate_1635_checked

theorem certificate_1636_checked : certificate_1636.Valid 15 8 14 certificate_1636_q certificate_1636_edges 6 4 [] := by decide +kernel
theorem certificate_1636_valid : certificate_1636.Valid 15 8 (patternOrder [[],[],[1,1],[2,2]]) (patternClique [[],[],[1,1],[2,2]]) (patternEdges [[],[],[1,1],[2,2]]) (patternAmount [[],[],[1,1],[2,2]]) (patternEdgeCount [[],[],[1,1],[2,2]]) [] := certificate_1636_checked

theorem certificate_1637_checked : certificate_1637.Valid 15 8 15 certificate_1637_q certificate_1637_edges 7 4 [] := by decide +kernel
theorem certificate_1637_valid : certificate_1637.Valid 15 8 (patternOrder [[],[],[1,1],[2,3]]) (patternClique [[],[],[1,1],[2,3]]) (patternEdges [[],[],[1,1],[2,3]]) (patternAmount [[],[],[1,1],[2,3]]) (patternEdgeCount [[],[],[1,1],[2,3]]) [] := certificate_1637_checked

theorem certificate_1638_checked : certificate_1638.Valid 15 8 13 certificate_1638_q certificate_1638_edges 5 4 [] := by decide +kernel
theorem certificate_1638_valid : certificate_1638.Valid 15 8 (patternOrder [[],[],[1,1,1],[2]]) (patternClique [[],[],[1,1,1],[2]]) (patternEdges [[],[],[1,1,1],[2]]) (patternAmount [[],[],[1,1,1],[2]]) (patternEdgeCount [[],[],[1,1,1],[2]]) [] := certificate_1638_checked

theorem certificate_1639_checked : certificate_1639.Valid 15 8 14 certificate_1639_q certificate_1639_edges 6 4 [] := by decide +kernel
theorem certificate_1639_valid : certificate_1639.Valid 15 8 (patternOrder [[],[],[1,1,1],[3]]) (patternClique [[],[],[1,1,1],[3]]) (patternEdges [[],[],[1,1,1],[3]]) (patternAmount [[],[],[1,1,1],[3]]) (patternEdgeCount [[],[],[1,1,1],[3]]) [] := certificate_1639_checked

theorem certificate_1640_checked : certificate_1640.Valid 15 8 15 certificate_1640_q certificate_1640_edges 7 4 [] := by decide +kernel
theorem certificate_1640_valid : certificate_1640.Valid 15 8 (patternOrder [[],[],[1,1,1],[4]]) (patternClique [[],[],[1,1,1],[4]]) (patternEdges [[],[],[1,1,1],[4]]) (patternAmount [[],[],[1,1,1],[4]]) (patternEdgeCount [[],[],[1,1,1],[4]]) [] := certificate_1640_checked

theorem certificate_1641_checked : certificate_1641.Valid 15 8 13 certificate_1641_q certificate_1641_edges 5 5 [] := by decide +kernel
theorem certificate_1641_valid : certificate_1641.Valid 15 8 (patternOrder [[],[],[1,1,1,1,1]]) (patternClique [[],[],[1,1,1,1,1]]) (patternEdges [[],[],[1,1,1,1,1]]) (patternAmount [[],[],[1,1,1,1,1]]) (patternEdgeCount [[],[],[1,1,1,1,1]]) [] := certificate_1641_checked

theorem certificate_1642_checked : certificate_1642.Valid 15 8 14 certificate_1642_q certificate_1642_edges 6 5 [] := by decide +kernel
theorem certificate_1642_valid : certificate_1642.Valid 15 8 (patternOrder [[],[],[1,1,1,1,2]]) (patternClique [[],[],[1,1,1,1,2]]) (patternEdges [[],[],[1,1,1,1,2]]) (patternAmount [[],[],[1,1,1,1,2]]) (patternEdgeCount [[],[],[1,1,1,1,2]]) [] := certificate_1642_checked

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

theorem patterns_15_8_7_verified_oai : ∀ D ∈ patterns_15_8_7, PatternVerified 15 8 D := by

  simp only [patterns_15_8_7, List.forall_mem_cons]

  exact ⟨⟨certificate_1627, certificate_1627_valid⟩, ⟨⟨certificate_1628, certificate_1628_valid⟩, ⟨⟨certificate_1629, certificate_1629_valid⟩, ⟨⟨certificate_1630, certificate_1630_valid⟩, ⟨⟨certificate_1631, certificate_1631_valid⟩, ⟨⟨certificate_1632, certificate_1632_valid⟩, ⟨⟨certificate_1633, certificate_1633_valid⟩, ⟨⟨certificate_1634, certificate_1634_valid⟩, ⟨⟨certificate_1635, certificate_1635_valid⟩, ⟨⟨certificate_1636, certificate_1636_valid⟩, ⟨⟨certificate_1637, certificate_1637_valid⟩, ⟨⟨certificate_1638, certificate_1638_valid⟩, ⟨⟨certificate_1639, certificate_1639_valid⟩, ⟨⟨certificate_1640, certificate_1640_valid⟩, ⟨⟨certificate_1641, certificate_1641_valid⟩, ⟨⟨certificate_1642, certificate_1642_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_8_7_verified_oai := @OAI.CycleClique.patterns_15_8_7_verified_oai
