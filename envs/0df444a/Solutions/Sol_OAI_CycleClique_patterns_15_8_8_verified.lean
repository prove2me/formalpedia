-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_8_8_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:18:25.501172+00:00
-- url     : https://prove2.me/submissions/6fd0848f-7acd-4f76-92ac-fce10ddb0118

import Mathlib
import Definitions.Def_OAIQ107D129
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates052
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1643_checked : certificate_1643.Valid 15 8 15 certificate_1643_q certificate_1643_edges 7 5 [] := by decide +kernel
theorem certificate_1643_valid : certificate_1643.Valid 15 8 (patternOrder [[],[],[1,1,1,1,3]]) (patternClique [[],[],[1,1,1,1,3]]) (patternEdges [[],[],[1,1,1,1,3]]) (patternAmount [[],[],[1,1,1,1,3]]) (patternEdgeCount [[],[],[1,1,1,1,3]]) [] := certificate_1643_checked

theorem certificate_1644_checked : certificate_1644.Valid 15 8 14 certificate_1644_q certificate_1644_edges 6 5 [] := by decide +kernel
theorem certificate_1644_valid : certificate_1644.Valid 15 8 (patternOrder [[],[],[1,1,1,2,1]]) (patternClique [[],[],[1,1,1,2,1]]) (patternEdges [[],[],[1,1,1,2,1]]) (patternAmount [[],[],[1,1,1,2,1]]) (patternEdgeCount [[],[],[1,1,1,2,1]]) [] := certificate_1644_checked

theorem certificate_1645_checked : certificate_1645.Valid 15 8 15 certificate_1645_q certificate_1645_edges 7 5 [] := by decide +kernel
theorem certificate_1645_valid : certificate_1645.Valid 15 8 (patternOrder [[],[],[1,1,1,2,2]]) (patternClique [[],[],[1,1,1,2,2]]) (patternEdges [[],[],[1,1,1,2,2]]) (patternAmount [[],[],[1,1,1,2,2]]) (patternEdgeCount [[],[],[1,1,1,2,2]]) [] := certificate_1645_checked

theorem certificate_1646_checked : certificate_1646.Valid 15 8 15 certificate_1646_q certificate_1646_edges 7 5 [] := by decide +kernel
theorem certificate_1646_valid : certificate_1646.Valid 15 8 (patternOrder [[],[],[1,1,1,3,1]]) (patternClique [[],[],[1,1,1,3,1]]) (patternEdges [[],[],[1,1,1,3,1]]) (patternAmount [[],[],[1,1,1,3,1]]) (patternEdgeCount [[],[],[1,1,1,3,1]]) [] := certificate_1646_checked

theorem certificate_1647_checked : certificate_1647.Valid 15 8 14 certificate_1647_q certificate_1647_edges 6 4 [] := by decide +kernel
theorem certificate_1647_valid : certificate_1647.Valid 15 8 (patternOrder [[],[],[1,1,2],[2]]) (patternClique [[],[],[1,1,2],[2]]) (patternEdges [[],[],[1,1,2],[2]]) (patternAmount [[],[],[1,1,2],[2]]) (patternEdgeCount [[],[],[1,1,2],[2]]) [] := certificate_1647_checked

theorem certificate_1648_checked : certificate_1648.Valid 15 8 15 certificate_1648_q certificate_1648_edges 7 4 [] := by decide +kernel
theorem certificate_1648_valid : certificate_1648.Valid 15 8 (patternOrder [[],[],[1,1,2],[3]]) (patternClique [[],[],[1,1,2],[3]]) (patternEdges [[],[],[1,1,2],[3]]) (patternAmount [[],[],[1,1,2],[3]]) (patternEdgeCount [[],[],[1,1,2],[3]]) [] := certificate_1648_checked

theorem certificate_1649_checked : certificate_1649.Valid 15 8 14 certificate_1649_q certificate_1649_edges 6 5 [] := by decide +kernel
theorem certificate_1649_valid : certificate_1649.Valid 15 8 (patternOrder [[],[],[1,1,2,1,1]]) (patternClique [[],[],[1,1,2,1,1]]) (patternEdges [[],[],[1,1,2,1,1]]) (patternAmount [[],[],[1,1,2,1,1]]) (patternEdgeCount [[],[],[1,1,2,1,1]]) [] := certificate_1649_checked

theorem certificate_1650_checked : certificate_1650.Valid 15 8 15 certificate_1650_q certificate_1650_edges 7 5 [] := by decide +kernel
theorem certificate_1650_valid : certificate_1650.Valid 15 8 (patternOrder [[],[],[1,1,2,1,2]]) (patternClique [[],[],[1,1,2,1,2]]) (patternEdges [[],[],[1,1,2,1,2]]) (patternAmount [[],[],[1,1,2,1,2]]) (patternEdgeCount [[],[],[1,1,2,1,2]]) [] := certificate_1650_checked

theorem certificate_1651_checked : certificate_1651.Valid 15 8 15 certificate_1651_q certificate_1651_edges 7 5 [] := by decide +kernel
theorem certificate_1651_valid : certificate_1651.Valid 15 8 (patternOrder [[],[],[1,1,2,2,1]]) (patternClique [[],[],[1,1,2,2,1]]) (patternEdges [[],[],[1,1,2,2,1]]) (patternAmount [[],[],[1,1,2,2,1]]) (patternEdgeCount [[],[],[1,1,2,2,1]]) [] := certificate_1651_checked

theorem certificate_1652_checked : certificate_1652.Valid 15 8 15 certificate_1652_q certificate_1652_edges 7 4 [] := by decide +kernel
theorem certificate_1652_valid : certificate_1652.Valid 15 8 (patternOrder [[],[],[1,1,3],[2]]) (patternClique [[],[],[1,1,3],[2]]) (patternEdges [[],[],[1,1,3],[2]]) (patternAmount [[],[],[1,1,3],[2]]) (patternEdgeCount [[],[],[1,1,3],[2]]) [] := certificate_1652_checked

theorem certificate_1653_checked : certificate_1653.Valid 15 8 15 certificate_1653_q certificate_1653_edges 7 5 [] := by decide +kernel
theorem certificate_1653_valid : certificate_1653.Valid 15 8 (patternOrder [[],[],[1,1,3,1,1]]) (patternClique [[],[],[1,1,3,1,1]]) (patternEdges [[],[],[1,1,3,1,1]]) (patternAmount [[],[],[1,1,3,1,1]]) (patternEdgeCount [[],[],[1,1,3,1,1]]) [] := certificate_1653_checked

theorem certificate_1654_checked : certificate_1654.Valid 15 8 14 certificate_1654_q certificate_1654_edges 6 4 [] := by decide +kernel
theorem certificate_1654_valid : certificate_1654.Valid 15 8 (patternOrder [[],[],[1,2],[1,2]]) (patternClique [[],[],[1,2],[1,2]]) (patternEdges [[],[],[1,2],[1,2]]) (patternAmount [[],[],[1,2],[1,2]]) (patternEdgeCount [[],[],[1,2],[1,2]]) [] := certificate_1654_checked

theorem certificate_1655_checked : certificate_1655.Valid 15 8 15 certificate_1655_q certificate_1655_edges 7 4 [] := by decide +kernel
theorem certificate_1655_valid : certificate_1655.Valid 15 8 (patternOrder [[],[],[1,2],[1,3]]) (patternClique [[],[],[1,2],[1,3]]) (patternEdges [[],[],[1,2],[1,3]]) (patternAmount [[],[],[1,2],[1,3]]) (patternEdgeCount [[],[],[1,2],[1,3]]) [] := certificate_1655_checked

theorem certificate_1656_checked : certificate_1656.Valid 15 8 15 certificate_1656_q certificate_1656_edges 7 4 [] := by decide +kernel
theorem certificate_1656_valid : certificate_1656.Valid 15 8 (patternOrder [[],[],[1,2],[2,2]]) (patternClique [[],[],[1,2],[2,2]]) (patternEdges [[],[],[1,2],[2,2]]) (patternAmount [[],[],[1,2],[2,2]]) (patternEdgeCount [[],[],[1,2],[2,2]]) [] := certificate_1656_checked

theorem certificate_1657_checked : certificate_1657.Valid 15 8 14 certificate_1657_q certificate_1657_edges 6 4 [] := by decide +kernel
theorem certificate_1657_valid : certificate_1657.Valid 15 8 (patternOrder [[],[],[1,2,1],[2]]) (patternClique [[],[],[1,2,1],[2]]) (patternEdges [[],[],[1,2,1],[2]]) (patternAmount [[],[],[1,2,1],[2]]) (patternEdgeCount [[],[],[1,2,1],[2]]) [] := certificate_1657_checked

theorem certificate_1658_checked : certificate_1658.Valid 15 8 15 certificate_1658_q certificate_1658_edges 7 4 [] := by decide +kernel
theorem certificate_1658_valid : certificate_1658.Valid 15 8 (patternOrder [[],[],[1,2,1],[3]]) (patternClique [[],[],[1,2,1],[3]]) (patternEdges [[],[],[1,2,1],[3]]) (patternAmount [[],[],[1,2,1],[3]]) (patternEdgeCount [[],[],[1,2,1],[3]]) [] := certificate_1658_checked

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

theorem patterns_15_8_8_verified_oai : ∀ D ∈ patterns_15_8_8, PatternVerified 15 8 D := by

  simp only [patterns_15_8_8, List.forall_mem_cons]

  exact ⟨⟨certificate_1643, certificate_1643_valid⟩, ⟨⟨certificate_1644, certificate_1644_valid⟩, ⟨⟨certificate_1645, certificate_1645_valid⟩, ⟨⟨certificate_1646, certificate_1646_valid⟩, ⟨⟨certificate_1647, certificate_1647_valid⟩, ⟨⟨certificate_1648, certificate_1648_valid⟩, ⟨⟨certificate_1649, certificate_1649_valid⟩, ⟨⟨certificate_1650, certificate_1650_valid⟩, ⟨⟨certificate_1651, certificate_1651_valid⟩, ⟨⟨certificate_1652, certificate_1652_valid⟩, ⟨⟨certificate_1653, certificate_1653_valid⟩, ⟨⟨certificate_1654, certificate_1654_valid⟩, ⟨⟨certificate_1655, certificate_1655_valid⟩, ⟨⟨certificate_1656, certificate_1656_valid⟩, ⟨⟨certificate_1657, certificate_1657_valid⟩, ⟨⟨certificate_1658, certificate_1658_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_8_8_verified_oai := @OAI.CycleClique.patterns_15_8_8_verified_oai
