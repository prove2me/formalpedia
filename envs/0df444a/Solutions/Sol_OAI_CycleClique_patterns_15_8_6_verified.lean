-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_8_6_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:12:11.095863+00:00
-- url     : https://prove2.me/submissions/6e4bf14a-ff68-44b1-bb51-980b92b73c01

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

theorem certificate_1611_checked : certificate_1611.Valid 15 8 12 certificate_1611_q certificate_1611_edges 4 3 [] := by decide +kernel
theorem certificate_1611_valid : certificate_1611.Valid 15 8 (patternOrder [[],[],[1],[1],[2]]) (patternClique [[],[],[1],[1],[2]]) (patternEdges [[],[],[1],[1],[2]]) (patternAmount [[],[],[1],[1],[2]]) (patternEdgeCount [[],[],[1],[1],[2]]) [] := certificate_1611_checked

theorem certificate_1612_checked : certificate_1612.Valid 15 8 13 certificate_1612_q certificate_1612_edges 5 3 [] := by decide +kernel
theorem certificate_1612_valid : certificate_1612.Valid 15 8 (patternOrder [[],[],[1],[1],[3]]) (patternClique [[],[],[1],[1],[3]]) (patternEdges [[],[],[1],[1],[3]]) (patternAmount [[],[],[1],[1],[3]]) (patternEdgeCount [[],[],[1],[1],[3]]) [] := certificate_1612_checked

theorem certificate_1613_checked : certificate_1613.Valid 15 8 14 certificate_1613_q certificate_1613_edges 6 3 [] := by decide +kernel
theorem certificate_1613_valid : certificate_1613.Valid 15 8 (patternOrder [[],[],[1],[1],[4]]) (patternClique [[],[],[1],[1],[4]]) (patternEdges [[],[],[1],[1],[4]]) (patternAmount [[],[],[1],[1],[4]]) (patternEdgeCount [[],[],[1],[1],[4]]) [] := certificate_1613_checked

theorem certificate_1614_checked : certificate_1614.Valid 15 8 15 certificate_1614_q certificate_1614_edges 7 3 [] := by decide +kernel
theorem certificate_1614_valid : certificate_1614.Valid 15 8 (patternOrder [[],[],[1],[1],[5]]) (patternClique [[],[],[1],[1],[5]]) (patternEdges [[],[],[1],[1],[5]]) (patternAmount [[],[],[1],[1],[5]]) (patternEdgeCount [[],[],[1],[1],[5]]) [] := certificate_1614_checked

theorem certificate_1615_checked : certificate_1615.Valid 15 8 12 certificate_1615_q certificate_1615_edges 4 4 [] := by decide +kernel
theorem certificate_1615_valid : certificate_1615.Valid 15 8 (patternOrder [[],[],[1],[1,1,1]]) (patternClique [[],[],[1],[1,1,1]]) (patternEdges [[],[],[1],[1,1,1]]) (patternAmount [[],[],[1],[1,1,1]]) (patternEdgeCount [[],[],[1],[1,1,1]]) [] := certificate_1615_checked

theorem certificate_1616_checked : certificate_1616.Valid 15 8 13 certificate_1616_q certificate_1616_edges 5 4 [] := by decide +kernel
theorem certificate_1616_valid : certificate_1616.Valid 15 8 (patternOrder [[],[],[1],[1,1,2]]) (patternClique [[],[],[1],[1,1,2]]) (patternEdges [[],[],[1],[1,1,2]]) (patternAmount [[],[],[1],[1,1,2]]) (patternEdgeCount [[],[],[1],[1,1,2]]) [] := certificate_1616_checked

theorem certificate_1617_checked : certificate_1617.Valid 15 8 14 certificate_1617_q certificate_1617_edges 6 4 [] := by decide +kernel
theorem certificate_1617_valid : certificate_1617.Valid 15 8 (patternOrder [[],[],[1],[1,1,3]]) (patternClique [[],[],[1],[1,1,3]]) (patternEdges [[],[],[1],[1,1,3]]) (patternAmount [[],[],[1],[1,1,3]]) (patternEdgeCount [[],[],[1],[1,1,3]]) [] := certificate_1617_checked

theorem certificate_1618_checked : certificate_1618.Valid 15 8 15 certificate_1618_q certificate_1618_edges 7 4 [] := by decide +kernel
theorem certificate_1618_valid : certificate_1618.Valid 15 8 (patternOrder [[],[],[1],[1,1,4]]) (patternClique [[],[],[1],[1,1,4]]) (patternEdges [[],[],[1],[1,1,4]]) (patternAmount [[],[],[1],[1,1,4]]) (patternEdgeCount [[],[],[1],[1,1,4]]) [] := certificate_1618_checked

theorem certificate_1619_checked : certificate_1619.Valid 15 8 13 certificate_1619_q certificate_1619_edges 5 4 [] := by decide +kernel
theorem certificate_1619_valid : certificate_1619.Valid 15 8 (patternOrder [[],[],[1],[1,2,1]]) (patternClique [[],[],[1],[1,2,1]]) (patternEdges [[],[],[1],[1,2,1]]) (patternAmount [[],[],[1],[1,2,1]]) (patternEdgeCount [[],[],[1],[1,2,1]]) [] := certificate_1619_checked

theorem certificate_1620_checked : certificate_1620.Valid 15 8 14 certificate_1620_q certificate_1620_edges 6 4 [] := by decide +kernel
theorem certificate_1620_valid : certificate_1620.Valid 15 8 (patternOrder [[],[],[1],[1,2,2]]) (patternClique [[],[],[1],[1,2,2]]) (patternEdges [[],[],[1],[1,2,2]]) (patternAmount [[],[],[1],[1,2,2]]) (patternEdgeCount [[],[],[1],[1,2,2]]) [] := certificate_1620_checked

theorem certificate_1621_checked : certificate_1621.Valid 15 8 15 certificate_1621_q certificate_1621_edges 7 4 [] := by decide +kernel
theorem certificate_1621_valid : certificate_1621.Valid 15 8 (patternOrder [[],[],[1],[1,2,3]]) (patternClique [[],[],[1],[1,2,3]]) (patternEdges [[],[],[1],[1,2,3]]) (patternAmount [[],[],[1],[1,2,3]]) (patternEdgeCount [[],[],[1],[1,2,3]]) [] := certificate_1621_checked

theorem certificate_1622_checked : certificate_1622.Valid 15 8 14 certificate_1622_q certificate_1622_edges 6 4 [] := by decide +kernel
theorem certificate_1622_valid : certificate_1622.Valid 15 8 (patternOrder [[],[],[1],[1,3,1]]) (patternClique [[],[],[1],[1,3,1]]) (patternEdges [[],[],[1],[1,3,1]]) (patternAmount [[],[],[1],[1,3,1]]) (patternEdgeCount [[],[],[1],[1,3,1]]) [] := certificate_1622_checked

theorem certificate_1623_checked : certificate_1623.Valid 15 8 15 certificate_1623_q certificate_1623_edges 7 4 [] := by decide +kernel
theorem certificate_1623_valid : certificate_1623.Valid 15 8 (patternOrder [[],[],[1],[1,3,2]]) (patternClique [[],[],[1],[1,3,2]]) (patternEdges [[],[],[1],[1,3,2]]) (patternAmount [[],[],[1],[1,3,2]]) (patternEdgeCount [[],[],[1],[1,3,2]]) [] := certificate_1623_checked

theorem certificate_1624_checked : certificate_1624.Valid 15 8 15 certificate_1624_q certificate_1624_edges 7 4 [] := by decide +kernel
theorem certificate_1624_valid : certificate_1624.Valid 15 8 (patternOrder [[],[],[1],[1,4,1]]) (patternClique [[],[],[1],[1,4,1]]) (patternEdges [[],[],[1],[1,4,1]]) (patternAmount [[],[],[1],[1,4,1]]) (patternEdgeCount [[],[],[1],[1,4,1]]) [] := certificate_1624_checked

theorem certificate_1625_checked : certificate_1625.Valid 15 8 13 certificate_1625_q certificate_1625_edges 5 3 [] := by decide +kernel
theorem certificate_1625_valid : certificate_1625.Valid 15 8 (patternOrder [[],[],[1],[2],[2]]) (patternClique [[],[],[1],[2],[2]]) (patternEdges [[],[],[1],[2],[2]]) (patternAmount [[],[],[1],[2],[2]]) (patternEdgeCount [[],[],[1],[2],[2]]) [] := certificate_1625_checked

theorem certificate_1626_checked : certificate_1626.Valid 15 8 14 certificate_1626_q certificate_1626_edges 6 3 [] := by decide +kernel
theorem certificate_1626_valid : certificate_1626.Valid 15 8 (patternOrder [[],[],[1],[2],[3]]) (patternClique [[],[],[1],[2],[3]]) (patternEdges [[],[],[1],[2],[3]]) (patternAmount [[],[],[1],[2],[3]]) (patternEdgeCount [[],[],[1],[2],[3]]) [] := certificate_1626_checked

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

theorem patterns_15_8_6_verified_oai : ∀ D ∈ patterns_15_8_6, PatternVerified 15 8 D := by

  simp only [patterns_15_8_6, List.forall_mem_cons]

  exact ⟨⟨certificate_1611, certificate_1611_valid⟩, ⟨⟨certificate_1612, certificate_1612_valid⟩, ⟨⟨certificate_1613, certificate_1613_valid⟩, ⟨⟨certificate_1614, certificate_1614_valid⟩, ⟨⟨certificate_1615, certificate_1615_valid⟩, ⟨⟨certificate_1616, certificate_1616_valid⟩, ⟨⟨certificate_1617, certificate_1617_valid⟩, ⟨⟨certificate_1618, certificate_1618_valid⟩, ⟨⟨certificate_1619, certificate_1619_valid⟩, ⟨⟨certificate_1620, certificate_1620_valid⟩, ⟨⟨certificate_1621, certificate_1621_valid⟩, ⟨⟨certificate_1622, certificate_1622_valid⟩, ⟨⟨certificate_1623, certificate_1623_valid⟩, ⟨⟨certificate_1624, certificate_1624_valid⟩, ⟨⟨certificate_1625, certificate_1625_valid⟩, ⟨⟨certificate_1626, certificate_1626_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_8_6_verified_oai := @OAI.CycleClique.patterns_15_8_6_verified_oai
