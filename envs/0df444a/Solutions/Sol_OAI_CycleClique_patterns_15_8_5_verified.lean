-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_8_5_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:18:01.947007+00:00
-- url     : https://prove2.me/submissions/7d7a4de8-a566-4bb1-a298-d4e9b0fa3fd1

import Mathlib
import Definitions.Def_OAIQ107D129
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates050
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1595_checked : certificate_1595.Valid 15 8 14 certificate_1595_q certificate_1595_edges 6 4 [] := by decide +kernel
theorem certificate_1595_valid : certificate_1595.Valid 15 8 (patternOrder [[],[],[],[1,2,1,2]]) (patternClique [[],[],[],[1,2,1,2]]) (patternEdges [[],[],[],[1,2,1,2]]) (patternAmount [[],[],[],[1,2,1,2]]) (patternEdgeCount [[],[],[],[1,2,1,2]]) [] := certificate_1595_checked

theorem certificate_1596_checked : certificate_1596.Valid 15 8 15 certificate_1596_q certificate_1596_edges 7 4 [] := by decide +kernel
theorem certificate_1596_valid : certificate_1596.Valid 15 8 (patternOrder [[],[],[],[1,2,1,3]]) (patternClique [[],[],[],[1,2,1,3]]) (patternEdges [[],[],[],[1,2,1,3]]) (patternAmount [[],[],[],[1,2,1,3]]) (patternEdgeCount [[],[],[],[1,2,1,3]]) [] := certificate_1596_checked

theorem certificate_1597_checked : certificate_1597.Valid 15 8 14 certificate_1597_q certificate_1597_edges 6 4 [] := by decide +kernel
theorem certificate_1597_valid : certificate_1597.Valid 15 8 (patternOrder [[],[],[],[1,2,2,1]]) (patternClique [[],[],[],[1,2,2,1]]) (patternEdges [[],[],[],[1,2,2,1]]) (patternAmount [[],[],[],[1,2,2,1]]) (patternEdgeCount [[],[],[],[1,2,2,1]]) [] := certificate_1597_checked

theorem certificate_1598_checked : certificate_1598.Valid 15 8 15 certificate_1598_q certificate_1598_edges 7 4 [] := by decide +kernel
theorem certificate_1598_valid : certificate_1598.Valid 15 8 (patternOrder [[],[],[],[1,2,2,2]]) (patternClique [[],[],[],[1,2,2,2]]) (patternEdges [[],[],[],[1,2,2,2]]) (patternAmount [[],[],[],[1,2,2,2]]) (patternEdgeCount [[],[],[],[1,2,2,2]]) [] := certificate_1598_checked

theorem certificate_1599_checked : certificate_1599.Valid 15 8 15 certificate_1599_q certificate_1599_edges 7 4 [] := by decide +kernel
theorem certificate_1599_valid : certificate_1599.Valid 15 8 (patternOrder [[],[],[],[1,2,3,1]]) (patternClique [[],[],[],[1,2,3,1]]) (patternEdges [[],[],[],[1,2,3,1]]) (patternAmount [[],[],[],[1,2,3,1]]) (patternEdgeCount [[],[],[],[1,2,3,1]]) [] := certificate_1599_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates051
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1600_checked : certificate_1600.Valid 15 8 14 certificate_1600_q certificate_1600_edges 6 3 [] := by decide +kernel
theorem certificate_1600_valid : certificate_1600.Valid 15 8 (patternOrder [[],[],[],[1,3],[2]]) (patternClique [[],[],[],[1,3],[2]]) (patternEdges [[],[],[],[1,3],[2]]) (patternAmount [[],[],[],[1,3],[2]]) (patternEdgeCount [[],[],[],[1,3],[2]]) [] := certificate_1600_checked

theorem certificate_1601_checked : certificate_1601.Valid 15 8 15 certificate_1601_q certificate_1601_edges 7 3 [] := by decide +kernel
theorem certificate_1601_valid : certificate_1601.Valid 15 8 (patternOrder [[],[],[],[1,3],[3]]) (patternClique [[],[],[],[1,3],[3]]) (patternEdges [[],[],[],[1,3],[3]]) (patternAmount [[],[],[],[1,3],[3]]) (patternEdgeCount [[],[],[],[1,3],[3]]) [] := certificate_1601_checked

theorem certificate_1602_checked : certificate_1602.Valid 15 8 15 certificate_1602_q certificate_1602_edges 7 4 [] := by decide +kernel
theorem certificate_1602_valid : certificate_1602.Valid 15 8 (patternOrder [[],[],[],[1,3,1,2]]) (patternClique [[],[],[],[1,3,1,2]]) (patternEdges [[],[],[],[1,3,1,2]]) (patternAmount [[],[],[],[1,3,1,2]]) (patternEdgeCount [[],[],[],[1,3,1,2]]) [] := certificate_1602_checked

theorem certificate_1603_checked : certificate_1603.Valid 15 8 15 certificate_1603_q certificate_1603_edges 7 3 [] := by decide +kernel
theorem certificate_1603_valid : certificate_1603.Valid 15 8 (patternOrder [[],[],[],[1,4],[2]]) (patternClique [[],[],[],[1,4],[2]]) (patternEdges [[],[],[],[1,4],[2]]) (patternAmount [[],[],[],[1,4],[2]]) (patternEdgeCount [[],[],[],[1,4],[2]]) [] := certificate_1603_checked

theorem certificate_1604_checked : certificate_1604.Valid 15 8 14 certificate_1604_q certificate_1604_edges 6 3 [] := by decide +kernel
theorem certificate_1604_valid : certificate_1604.Valid 15 8 (patternOrder [[],[],[],[2],[2,2]]) (patternClique [[],[],[],[2],[2,2]]) (patternEdges [[],[],[],[2],[2,2]]) (patternAmount [[],[],[],[2],[2,2]]) (patternEdgeCount [[],[],[],[2],[2,2]]) [] := certificate_1604_checked

theorem certificate_1605_checked : certificate_1605.Valid 15 8 15 certificate_1605_q certificate_1605_edges 7 3 [] := by decide +kernel
theorem certificate_1605_valid : certificate_1605.Valid 15 8 (patternOrder [[],[],[],[2],[2,3]]) (patternClique [[],[],[],[2],[2,3]]) (patternEdges [[],[],[],[2],[2,3]]) (patternAmount [[],[],[],[2],[2,3]]) (patternEdgeCount [[],[],[],[2],[2,3]]) [] := certificate_1605_checked

theorem certificate_1606_checked : certificate_1606.Valid 15 8 14 certificate_1606_q certificate_1606_edges 6 4 [] := by decide +kernel
theorem certificate_1606_valid : certificate_1606.Valid 15 8 (patternOrder [[],[],[],[2,1,1,2]]) (patternClique [[],[],[],[2,1,1,2]]) (patternEdges [[],[],[],[2,1,1,2]]) (patternAmount [[],[],[],[2,1,1,2]]) (patternEdgeCount [[],[],[],[2,1,1,2]]) [] := certificate_1606_checked

theorem certificate_1607_checked : certificate_1607.Valid 15 8 15 certificate_1607_q certificate_1607_edges 7 4 [] := by decide +kernel
theorem certificate_1607_valid : certificate_1607.Valid 15 8 (patternOrder [[],[],[],[2,1,1,3]]) (patternClique [[],[],[],[2,1,1,3]]) (patternEdges [[],[],[],[2,1,1,3]]) (patternAmount [[],[],[],[2,1,1,3]]) (patternEdgeCount [[],[],[],[2,1,1,3]]) [] := certificate_1607_checked

theorem certificate_1608_checked : certificate_1608.Valid 15 8 15 certificate_1608_q certificate_1608_edges 7 4 [] := by decide +kernel
theorem certificate_1608_valid : certificate_1608.Valid 15 8 (patternOrder [[],[],[],[2,1,2,2]]) (patternClique [[],[],[],[2,1,2,2]]) (patternEdges [[],[],[],[2,1,2,2]]) (patternAmount [[],[],[],[2,1,2,2]]) (patternEdgeCount [[],[],[],[2,1,2,2]]) [] := certificate_1608_checked

theorem certificate_1609_checked : certificate_1609.Valid 15 8 15 certificate_1609_q certificate_1609_edges 7 3 [] := by decide +kernel
theorem certificate_1609_valid : certificate_1609.Valid 15 8 (patternOrder [[],[],[],[2,2],[3]]) (patternClique [[],[],[],[2,2],[3]]) (patternEdges [[],[],[],[2,2],[3]]) (patternAmount [[],[],[],[2,2],[3]]) (patternEdgeCount [[],[],[],[2,2],[3]]) [] := certificate_1609_checked

theorem certificate_1610_checked : certificate_1610.Valid 15 8 11 certificate_1610_q certificate_1610_edges 3 3 [] := by decide +kernel
theorem certificate_1610_valid : certificate_1610.Valid 15 8 (patternOrder [[],[],[1],[1],[1]]) (patternClique [[],[],[1],[1],[1]]) (patternEdges [[],[],[1],[1],[1]]) (patternAmount [[],[],[1],[1],[1]]) (patternEdgeCount [[],[],[1],[1],[1]]) [] := certificate_1610_checked

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

theorem patterns_15_8_5_verified_oai : ∀ D ∈ patterns_15_8_5, PatternVerified 15 8 D := by

  simp only [patterns_15_8_5, List.forall_mem_cons]

  exact ⟨⟨certificate_1595, certificate_1595_valid⟩, ⟨⟨certificate_1596, certificate_1596_valid⟩, ⟨⟨certificate_1597, certificate_1597_valid⟩, ⟨⟨certificate_1598, certificate_1598_valid⟩, ⟨⟨certificate_1599, certificate_1599_valid⟩, ⟨⟨certificate_1600, certificate_1600_valid⟩, ⟨⟨certificate_1601, certificate_1601_valid⟩, ⟨⟨certificate_1602, certificate_1602_valid⟩, ⟨⟨certificate_1603, certificate_1603_valid⟩, ⟨⟨certificate_1604, certificate_1604_valid⟩, ⟨⟨certificate_1605, certificate_1605_valid⟩, ⟨⟨certificate_1606, certificate_1606_valid⟩, ⟨⟨certificate_1607, certificate_1607_valid⟩, ⟨⟨certificate_1608, certificate_1608_valid⟩, ⟨⟨certificate_1609, certificate_1609_valid⟩, ⟨⟨certificate_1610, certificate_1610_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_8_5_verified_oai := @OAI.CycleClique.patterns_15_8_5_verified_oai
