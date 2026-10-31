-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_8_4_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:20:32.76848+00:00
-- url     : https://prove2.me/submissions/3aac8933-573e-461d-8ed5-62753c80a7c7

import Mathlib
import Definitions.Def_OAIQ107D040
import Definitions.Def_OAIQ107D133
import Definitions.Def_OAIQ107D134

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates050
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1579_checked : certificate_1579.Valid 15 8 13 certificate_1579_q certificate_1579_edges 5 3 [] := by decide +kernel
theorem certificate_1579_valid : certificate_1579.Valid 15 8 (patternOrder [[],[],[],[1,1],[3]]) (patternClique [[],[],[],[1,1],[3]]) (patternEdges [[],[],[],[1,1],[3]]) (patternAmount [[],[],[],[1,1],[3]]) (patternEdgeCount [[],[],[],[1,1],[3]]) [] := certificate_1579_checked

theorem certificate_1580_checked : certificate_1580.Valid 15 8 14 certificate_1580_q certificate_1580_edges 6 3 [] := by decide +kernel
theorem certificate_1580_valid : certificate_1580.Valid 15 8 (patternOrder [[],[],[],[1,1],[4]]) (patternClique [[],[],[],[1,1],[4]]) (patternEdges [[],[],[],[1,1],[4]]) (patternAmount [[],[],[],[1,1],[4]]) (patternEdgeCount [[],[],[],[1,1],[4]]) [] := certificate_1580_checked

theorem certificate_1581_checked : certificate_1581.Valid 15 8 15 certificate_1581_q certificate_1581_edges 7 3 [] := by decide +kernel
theorem certificate_1581_valid : certificate_1581.Valid 15 8 (patternOrder [[],[],[],[1,1],[5]]) (patternClique [[],[],[],[1,1],[5]]) (patternEdges [[],[],[],[1,1],[5]]) (patternAmount [[],[],[],[1,1],[5]]) (patternEdgeCount [[],[],[],[1,1],[5]]) [] := certificate_1581_checked

theorem certificate_1582_checked : certificate_1582.Valid 15 8 12 certificate_1582_q certificate_1582_edges 4 4 [] := by decide +kernel
theorem certificate_1582_valid : certificate_1582.Valid 15 8 (patternOrder [[],[],[],[1,1,1,1]]) (patternClique [[],[],[],[1,1,1,1]]) (patternEdges [[],[],[],[1,1,1,1]]) (patternAmount [[],[],[],[1,1,1,1]]) (patternEdgeCount [[],[],[],[1,1,1,1]]) [] := certificate_1582_checked

theorem certificate_1583_checked : certificate_1583.Valid 15 8 13 certificate_1583_q certificate_1583_edges 5 4 [] := by decide +kernel
theorem certificate_1583_valid : certificate_1583.Valid 15 8 (patternOrder [[],[],[],[1,1,1,2]]) (patternClique [[],[],[],[1,1,1,2]]) (patternEdges [[],[],[],[1,1,1,2]]) (patternAmount [[],[],[],[1,1,1,2]]) (patternEdgeCount [[],[],[],[1,1,1,2]]) [] := certificate_1583_checked

theorem certificate_1584_checked : certificate_1584.Valid 15 8 14 certificate_1584_q certificate_1584_edges 6 4 [] := by decide +kernel
theorem certificate_1584_valid : certificate_1584.Valid 15 8 (patternOrder [[],[],[],[1,1,1,3]]) (patternClique [[],[],[],[1,1,1,3]]) (patternEdges [[],[],[],[1,1,1,3]]) (patternAmount [[],[],[],[1,1,1,3]]) (patternEdgeCount [[],[],[],[1,1,1,3]]) [] := certificate_1584_checked

theorem certificate_1585_checked : certificate_1585.Valid 15 8 15 certificate_1585_q certificate_1585_edges 7 4 [] := by decide +kernel
theorem certificate_1585_valid : certificate_1585.Valid 15 8 (patternOrder [[],[],[],[1,1,1,4]]) (patternClique [[],[],[],[1,1,1,4]]) (patternEdges [[],[],[],[1,1,1,4]]) (patternAmount [[],[],[],[1,1,1,4]]) (patternEdgeCount [[],[],[],[1,1,1,4]]) [] := certificate_1585_checked

theorem certificate_1586_checked : certificate_1586.Valid 15 8 13 certificate_1586_q certificate_1586_edges 5 4 [] := by decide +kernel
theorem certificate_1586_valid : certificate_1586.Valid 15 8 (patternOrder [[],[],[],[1,1,2,1]]) (patternClique [[],[],[],[1,1,2,1]]) (patternEdges [[],[],[],[1,1,2,1]]) (patternAmount [[],[],[],[1,1,2,1]]) (patternEdgeCount [[],[],[],[1,1,2,1]]) [] := certificate_1586_checked

theorem certificate_1587_checked : certificate_1587.Valid 15 8 14 certificate_1587_q certificate_1587_edges 6 4 [] := by decide +kernel
theorem certificate_1587_valid : certificate_1587.Valid 15 8 (patternOrder [[],[],[],[1,1,2,2]]) (patternClique [[],[],[],[1,1,2,2]]) (patternEdges [[],[],[],[1,1,2,2]]) (patternAmount [[],[],[],[1,1,2,2]]) (patternEdgeCount [[],[],[],[1,1,2,2]]) [] := certificate_1587_checked

theorem certificate_1588_checked : certificate_1588.Valid 15 8 15 certificate_1588_q certificate_1588_edges 7 4 [] := by decide +kernel
theorem certificate_1588_valid : certificate_1588.Valid 15 8 (patternOrder [[],[],[],[1,1,2,3]]) (patternClique [[],[],[],[1,1,2,3]]) (patternEdges [[],[],[],[1,1,2,3]]) (patternAmount [[],[],[],[1,1,2,3]]) (patternEdgeCount [[],[],[],[1,1,2,3]]) [] := certificate_1588_checked

theorem certificate_1589_checked : certificate_1589.Valid 15 8 14 certificate_1589_q certificate_1589_edges 6 4 [] := by decide +kernel
theorem certificate_1589_valid : certificate_1589.Valid 15 8 (patternOrder [[],[],[],[1,1,3,1]]) (patternClique [[],[],[],[1,1,3,1]]) (patternEdges [[],[],[],[1,1,3,1]]) (patternAmount [[],[],[],[1,1,3,1]]) (patternEdgeCount [[],[],[],[1,1,3,1]]) [] := certificate_1589_checked

theorem certificate_1590_checked : certificate_1590.Valid 15 8 15 certificate_1590_q certificate_1590_edges 7 4 [] := by decide +kernel
theorem certificate_1590_valid : certificate_1590.Valid 15 8 (patternOrder [[],[],[],[1,1,3,2]]) (patternClique [[],[],[],[1,1,3,2]]) (patternEdges [[],[],[],[1,1,3,2]]) (patternAmount [[],[],[],[1,1,3,2]]) (patternEdgeCount [[],[],[],[1,1,3,2]]) [] := certificate_1590_checked

theorem certificate_1591_checked : certificate_1591.Valid 15 8 15 certificate_1591_q certificate_1591_edges 7 4 [] := by decide +kernel
theorem certificate_1591_valid : certificate_1591.Valid 15 8 (patternOrder [[],[],[],[1,1,4,1]]) (patternClique [[],[],[],[1,1,4,1]]) (patternEdges [[],[],[],[1,1,4,1]]) (patternAmount [[],[],[],[1,1,4,1]]) (patternEdgeCount [[],[],[],[1,1,4,1]]) [] := certificate_1591_checked

theorem certificate_1592_checked : certificate_1592.Valid 15 8 13 certificate_1592_q certificate_1592_edges 5 3 [] := by decide +kernel
theorem certificate_1592_valid : certificate_1592.Valid 15 8 (patternOrder [[],[],[],[1,2],[2]]) (patternClique [[],[],[],[1,2],[2]]) (patternEdges [[],[],[],[1,2],[2]]) (patternAmount [[],[],[],[1,2],[2]]) (patternEdgeCount [[],[],[],[1,2],[2]]) [] := certificate_1592_checked

theorem certificate_1593_checked : certificate_1593.Valid 15 8 14 certificate_1593_q certificate_1593_edges 6 3 [] := by decide +kernel
theorem certificate_1593_valid : certificate_1593.Valid 15 8 (patternOrder [[],[],[],[1,2],[3]]) (patternClique [[],[],[],[1,2],[3]]) (patternEdges [[],[],[],[1,2],[3]]) (patternAmount [[],[],[],[1,2],[3]]) (patternEdgeCount [[],[],[],[1,2],[3]]) [] := certificate_1593_checked

theorem certificate_1594_checked : certificate_1594.Valid 15 8 15 certificate_1594_q certificate_1594_edges 7 3 [] := by decide +kernel
theorem certificate_1594_valid : certificate_1594.Valid 15 8 (patternOrder [[],[],[],[1,2],[4]]) (patternClique [[],[],[],[1,2],[4]]) (patternEdges [[],[],[],[1,2],[4]]) (patternAmount [[],[],[],[1,2],[4]]) (patternEdgeCount [[],[],[],[1,2],[4]]) [] := certificate_1594_checked

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

theorem patterns_15_8_4_verified_oai : ∀ D ∈ patterns_15_8_4, PatternVerified 15 8 D := by

  simp only [patterns_15_8_4, List.forall_mem_cons]

  exact ⟨⟨certificate_1579, certificate_1579_valid⟩, ⟨⟨certificate_1580, certificate_1580_valid⟩, ⟨⟨certificate_1581, certificate_1581_valid⟩, ⟨⟨certificate_1582, certificate_1582_valid⟩, ⟨⟨certificate_1583, certificate_1583_valid⟩, ⟨⟨certificate_1584, certificate_1584_valid⟩, ⟨⟨certificate_1585, certificate_1585_valid⟩, ⟨⟨certificate_1586, certificate_1586_valid⟩, ⟨⟨certificate_1587, certificate_1587_valid⟩, ⟨⟨certificate_1588, certificate_1588_valid⟩, ⟨⟨certificate_1589, certificate_1589_valid⟩, ⟨⟨certificate_1590, certificate_1590_valid⟩, ⟨⟨certificate_1591, certificate_1591_valid⟩, ⟨⟨certificate_1592, certificate_1592_valid⟩, ⟨⟨certificate_1593, certificate_1593_valid⟩, ⟨⟨certificate_1594, certificate_1594_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_8_4_verified_oai := @OAI.CycleClique.patterns_15_8_4_verified_oai
