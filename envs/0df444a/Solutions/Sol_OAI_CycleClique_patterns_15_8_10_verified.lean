-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_8_10_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:15:28.741009+00:00
-- url     : https://prove2.me/submissions/2841fe7f-130b-45a8-bba0-71981ef06252

import Mathlib
import Definitions.Def_OAIQ107D129
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates053
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1675_checked : certificate_1675.Valid 15 8 15 certificate_1675_q certificate_1675_edges 7 4 [] := by decide +kernel
theorem certificate_1675_valid : certificate_1675.Valid 15 8 (patternOrder [[],[1],[1,1],[4]]) (patternClique [[],[1],[1,1],[4]]) (patternEdges [[],[1],[1,1],[4]]) (patternAmount [[],[1],[1,1],[4]]) (patternEdgeCount [[],[1],[1,1],[4]]) [] := certificate_1675_checked

theorem certificate_1676_checked : certificate_1676.Valid 15 8 13 certificate_1676_q certificate_1676_edges 5 5 [] := by decide +kernel
theorem certificate_1676_valid : certificate_1676.Valid 15 8 (patternOrder [[],[1],[1,1,1,1]]) (patternClique [[],[1],[1,1,1,1]]) (patternEdges [[],[1],[1,1,1,1]]) (patternAmount [[],[1],[1,1,1,1]]) (patternEdgeCount [[],[1],[1,1,1,1]]) [] := certificate_1676_checked

theorem certificate_1677_checked : certificate_1677.Valid 15 8 14 certificate_1677_q certificate_1677_edges 6 5 [] := by decide +kernel
theorem certificate_1677_valid : certificate_1677.Valid 15 8 (patternOrder [[],[1],[1,1,1,2]]) (patternClique [[],[1],[1,1,1,2]]) (patternEdges [[],[1],[1,1,1,2]]) (patternAmount [[],[1],[1,1,1,2]]) (patternEdgeCount [[],[1],[1,1,1,2]]) [] := certificate_1677_checked

theorem certificate_1678_checked : certificate_1678.Valid 15 8 15 certificate_1678_q certificate_1678_edges 7 5 [] := by decide +kernel
theorem certificate_1678_valid : certificate_1678.Valid 15 8 (patternOrder [[],[1],[1,1,1,3]]) (patternClique [[],[1],[1,1,1,3]]) (patternEdges [[],[1],[1,1,1,3]]) (patternAmount [[],[1],[1,1,1,3]]) (patternEdgeCount [[],[1],[1,1,1,3]]) [] := certificate_1678_checked

theorem certificate_1679_checked : certificate_1679.Valid 15 8 14 certificate_1679_q certificate_1679_edges 6 5 [] := by decide +kernel
theorem certificate_1679_valid : certificate_1679.Valid 15 8 (patternOrder [[],[1],[1,1,2,1]]) (patternClique [[],[1],[1,1,2,1]]) (patternEdges [[],[1],[1,1,2,1]]) (patternAmount [[],[1],[1,1,2,1]]) (patternEdgeCount [[],[1],[1,1,2,1]]) [] := certificate_1679_checked

theorem certificate_1680_checked : certificate_1680.Valid 15 8 15 certificate_1680_q certificate_1680_edges 7 5 [] := by decide +kernel
theorem certificate_1680_valid : certificate_1680.Valid 15 8 (patternOrder [[],[1],[1,1,2,2]]) (patternClique [[],[1],[1,1,2,2]]) (patternEdges [[],[1],[1,1,2,2]]) (patternAmount [[],[1],[1,1,2,2]]) (patternEdgeCount [[],[1],[1,1,2,2]]) [] := certificate_1680_checked

theorem certificate_1681_checked : certificate_1681.Valid 15 8 15 certificate_1681_q certificate_1681_edges 7 5 [] := by decide +kernel
theorem certificate_1681_valid : certificate_1681.Valid 15 8 (patternOrder [[],[1],[1,1,3,1]]) (patternClique [[],[1],[1,1,3,1]]) (patternEdges [[],[1],[1,1,3,1]]) (patternAmount [[],[1],[1,1,3,1]]) (patternEdgeCount [[],[1],[1,1,3,1]]) [] := certificate_1681_checked

theorem certificate_1682_checked : certificate_1682.Valid 15 8 14 certificate_1682_q certificate_1682_edges 6 4 [] := by decide +kernel
theorem certificate_1682_valid : certificate_1682.Valid 15 8 (patternOrder [[],[1],[1,2],[2]]) (patternClique [[],[1],[1,2],[2]]) (patternEdges [[],[1],[1,2],[2]]) (patternAmount [[],[1],[1,2],[2]]) (patternEdgeCount [[],[1],[1,2],[2]]) [] := certificate_1682_checked

theorem certificate_1683_checked : certificate_1683.Valid 15 8 15 certificate_1683_q certificate_1683_edges 7 4 [] := by decide +kernel
theorem certificate_1683_valid : certificate_1683.Valid 15 8 (patternOrder [[],[1],[1,2],[3]]) (patternClique [[],[1],[1,2],[3]]) (patternEdges [[],[1],[1,2],[3]]) (patternAmount [[],[1],[1,2],[3]]) (patternEdgeCount [[],[1],[1,2],[3]]) [] := certificate_1683_checked

theorem certificate_1684_checked : certificate_1684.Valid 15 8 15 certificate_1684_q certificate_1684_edges 7 5 [] := by decide +kernel
theorem certificate_1684_valid : certificate_1684.Valid 15 8 (patternOrder [[],[1],[1,2,1,2]]) (patternClique [[],[1],[1,2,1,2]]) (patternEdges [[],[1],[1,2,1,2]]) (patternAmount [[],[1],[1,2,1,2]]) (patternEdgeCount [[],[1],[1,2,1,2]]) [] := certificate_1684_checked

theorem certificate_1685_checked : certificate_1685.Valid 15 8 15 certificate_1685_q certificate_1685_edges 7 5 [] := by decide +kernel
theorem certificate_1685_valid : certificate_1685.Valid 15 8 (patternOrder [[],[1],[1,2,2,1]]) (patternClique [[],[1],[1,2,2,1]]) (patternEdges [[],[1],[1,2,2,1]]) (patternAmount [[],[1],[1,2,2,1]]) (patternEdgeCount [[],[1],[1,2,2,1]]) [] := certificate_1685_checked

theorem certificate_1686_checked : certificate_1686.Valid 15 8 15 certificate_1686_q certificate_1686_edges 7 4 [] := by decide +kernel
theorem certificate_1686_valid : certificate_1686.Valid 15 8 (patternOrder [[],[1],[1,3],[2]]) (patternClique [[],[1],[1,3],[2]]) (patternEdges [[],[1],[1,3],[2]]) (patternAmount [[],[1],[1,3],[2]]) (patternEdgeCount [[],[1],[1,3],[2]]) [] := certificate_1686_checked

theorem certificate_1687_checked : certificate_1687.Valid 15 8 15 certificate_1687_q certificate_1687_edges 7 4 [] := by decide +kernel
theorem certificate_1687_valid : certificate_1687.Valid 15 8 (patternOrder [[],[1],[2],[2,2]]) (patternClique [[],[1],[2],[2,2]]) (patternEdges [[],[1],[2],[2,2]]) (patternAmount [[],[1],[2],[2,2]]) (patternEdgeCount [[],[1],[2],[2,2]]) [] := certificate_1687_checked

theorem certificate_1688_checked : certificate_1688.Valid 15 8 15 certificate_1688_q certificate_1688_edges 7 5 [] := by decide +kernel
theorem certificate_1688_valid : certificate_1688.Valid 15 8 (patternOrder [[],[1],[2,1,1,2]]) (patternClique [[],[1],[2,1,1,2]]) (patternEdges [[],[1],[2,1,1,2]]) (patternAmount [[],[1],[2,1,1,2]]) (patternEdgeCount [[],[1],[2,1,1,2]]) [] := certificate_1688_checked

theorem certificate_1689_checked : certificate_1689.Valid 15 8 13 certificate_1689_q certificate_1689_edges 5 5 [] := by decide +kernel
theorem certificate_1689_valid : certificate_1689.Valid 15 8 (patternOrder [[],[1,1],[1,1,1]]) (patternClique [[],[1,1],[1,1,1]]) (patternEdges [[],[1,1],[1,1,1]]) (patternAmount [[],[1,1],[1,1,1]]) (patternEdgeCount [[],[1,1],[1,1,1]]) [] := certificate_1689_checked

theorem certificate_1690_checked : certificate_1690.Valid 15 8 14 certificate_1690_q certificate_1690_edges 6 5 [] := by decide +kernel
theorem certificate_1690_valid : certificate_1690.Valid 15 8 (patternOrder [[],[1,1],[1,1,2]]) (patternClique [[],[1,1],[1,1,2]]) (patternEdges [[],[1,1],[1,1,2]]) (patternAmount [[],[1,1],[1,1,2]]) (patternEdgeCount [[],[1,1],[1,1,2]]) [] := certificate_1690_checked

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

theorem patterns_15_8_10_verified_oai : ∀ D ∈ patterns_15_8_10, PatternVerified 15 8 D := by

  simp only [patterns_15_8_10, List.forall_mem_cons]

  exact ⟨⟨certificate_1675, certificate_1675_valid⟩, ⟨⟨certificate_1676, certificate_1676_valid⟩, ⟨⟨certificate_1677, certificate_1677_valid⟩, ⟨⟨certificate_1678, certificate_1678_valid⟩, ⟨⟨certificate_1679, certificate_1679_valid⟩, ⟨⟨certificate_1680, certificate_1680_valid⟩, ⟨⟨certificate_1681, certificate_1681_valid⟩, ⟨⟨certificate_1682, certificate_1682_valid⟩, ⟨⟨certificate_1683, certificate_1683_valid⟩, ⟨⟨certificate_1684, certificate_1684_valid⟩, ⟨⟨certificate_1685, certificate_1685_valid⟩, ⟨⟨certificate_1686, certificate_1686_valid⟩, ⟨⟨certificate_1687, certificate_1687_valid⟩, ⟨⟨certificate_1688, certificate_1688_valid⟩, ⟨⟨certificate_1689, certificate_1689_valid⟩, ⟨⟨certificate_1690, certificate_1690_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_8_10_verified_oai := @OAI.CycleClique.patterns_15_8_10_verified_oai
