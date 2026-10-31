-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_8_9_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:27:37.913997+00:00
-- url     : https://prove2.me/submissions/287a00ae-cf2e-4bf6-bc57-e52e94908392

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

theorem certificate_1659_checked : certificate_1659.Valid 15 8 15 certificate_1659_q certificate_1659_edges 7 5 [] := by decide +kernel
theorem certificate_1659_valid : certificate_1659.Valid 15 8 (patternOrder [[],[],[1,2,1,1,2]]) (patternClique [[],[],[1,2,1,1,2]]) (patternEdges [[],[],[1,2,1,1,2]]) (patternAmount [[],[],[1,2,1,1,2]]) (patternEdgeCount [[],[],[1,2,1,1,2]]) [] := certificate_1659_checked

theorem certificate_1660_checked : certificate_1660.Valid 15 8 15 certificate_1660_q certificate_1660_edges 7 5 [] := by decide +kernel
theorem certificate_1660_valid : certificate_1660.Valid 15 8 (patternOrder [[],[],[1,2,1,2,1]]) (patternClique [[],[],[1,2,1,2,1]]) (patternEdges [[],[],[1,2,1,2,1]]) (patternAmount [[],[],[1,2,1,2,1]]) (patternEdgeCount [[],[],[1,2,1,2,1]]) [] := certificate_1660_checked

theorem certificate_1661_checked : certificate_1661.Valid 15 8 15 certificate_1661_q certificate_1661_edges 7 4 [] := by decide +kernel
theorem certificate_1661_valid : certificate_1661.Valid 15 8 (patternOrder [[],[],[1,2,2],[2]]) (patternClique [[],[],[1,2,2],[2]]) (patternEdges [[],[],[1,2,2],[2]]) (patternAmount [[],[],[1,2,2],[2]]) (patternEdgeCount [[],[],[1,2,2],[2]]) [] := certificate_1661_checked

theorem certificate_1662_checked : certificate_1662.Valid 15 8 15 certificate_1662_q certificate_1662_edges 7 4 [] := by decide +kernel
theorem certificate_1662_valid : certificate_1662.Valid 15 8 (patternOrder [[],[],[1,3,1],[2]]) (patternClique [[],[],[1,3,1],[2]]) (patternEdges [[],[],[1,3,1],[2]]) (patternAmount [[],[],[1,3,1],[2]]) (patternEdgeCount [[],[],[1,3,1],[2]]) [] := certificate_1662_checked

theorem certificate_1663_checked : certificate_1663.Valid 15 8 14 certificate_1663_q certificate_1663_edges 6 3 [] := by decide +kernel
theorem certificate_1663_valid : certificate_1663.Valid 15 8 (patternOrder [[],[],[2],[2],[2]]) (patternClique [[],[],[2],[2],[2]]) (patternEdges [[],[],[2],[2],[2]]) (patternAmount [[],[],[2],[2],[2]]) (patternEdgeCount [[],[],[2],[2],[2]]) [] := certificate_1663_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates053
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1664_checked : certificate_1664.Valid 15 8 15 certificate_1664_q certificate_1664_edges 7 3 [] := by decide +kernel
theorem certificate_1664_valid : certificate_1664.Valid 15 8 (patternOrder [[],[],[2],[2],[3]]) (patternClique [[],[],[2],[2],[3]]) (patternEdges [[],[],[2],[2],[3]]) (patternAmount [[],[],[2],[2],[3]]) (patternEdgeCount [[],[],[2],[2],[3]]) [] := certificate_1664_checked

theorem certificate_1665_checked : certificate_1665.Valid 15 8 15 certificate_1665_q certificate_1665_edges 7 4 [] := by decide +kernel
theorem certificate_1665_valid : certificate_1665.Valid 15 8 (patternOrder [[],[],[2],[2,1,2]]) (patternClique [[],[],[2],[2,1,2]]) (patternEdges [[],[],[2],[2,1,2]]) (patternAmount [[],[],[2],[2,1,2]]) (patternEdgeCount [[],[],[2],[2,1,2]]) [] := certificate_1665_checked

theorem certificate_1666_checked : certificate_1666.Valid 15 8 15 certificate_1666_q certificate_1666_edges 7 5 [] := by decide +kernel
theorem certificate_1666_valid : certificate_1666.Valid 15 8 (patternOrder [[],[],[2,1,1,1,2]]) (patternClique [[],[],[2,1,1,1,2]]) (patternEdges [[],[],[2,1,1,1,2]]) (patternAmount [[],[],[2,1,1,1,2]]) (patternEdgeCount [[],[],[2,1,1,1,2]]) [] := certificate_1666_checked

theorem certificate_1667_checked : certificate_1667.Valid 15 8 12 certificate_1667_q certificate_1667_edges 4 4 [] := by decide +kernel
theorem certificate_1667_valid : certificate_1667.Valid 15 8 (patternOrder [[],[1],[1],[1,1]]) (patternClique [[],[1],[1],[1,1]]) (patternEdges [[],[1],[1],[1,1]]) (patternAmount [[],[1],[1],[1,1]]) (patternEdgeCount [[],[1],[1],[1,1]]) [] := certificate_1667_checked

theorem certificate_1668_checked : certificate_1668.Valid 15 8 13 certificate_1668_q certificate_1668_edges 5 4 [] := by decide +kernel
theorem certificate_1668_valid : certificate_1668.Valid 15 8 (patternOrder [[],[1],[1],[1,2]]) (patternClique [[],[1],[1],[1,2]]) (patternEdges [[],[1],[1],[1,2]]) (patternAmount [[],[1],[1],[1,2]]) (patternEdgeCount [[],[1],[1],[1,2]]) [] := certificate_1668_checked

theorem certificate_1669_checked : certificate_1669.Valid 15 8 14 certificate_1669_q certificate_1669_edges 6 4 [] := by decide +kernel
theorem certificate_1669_valid : certificate_1669.Valid 15 8 (patternOrder [[],[1],[1],[1,3]]) (patternClique [[],[1],[1],[1,3]]) (patternEdges [[],[1],[1],[1,3]]) (patternAmount [[],[1],[1],[1,3]]) (patternEdgeCount [[],[1],[1],[1,3]]) [] := certificate_1669_checked

theorem certificate_1670_checked : certificate_1670.Valid 15 8 15 certificate_1670_q certificate_1670_edges 7 4 [] := by decide +kernel
theorem certificate_1670_valid : certificate_1670.Valid 15 8 (patternOrder [[],[1],[1],[1,4]]) (patternClique [[],[1],[1],[1,4]]) (patternEdges [[],[1],[1],[1,4]]) (patternAmount [[],[1],[1],[1,4]]) (patternEdgeCount [[],[1],[1],[1,4]]) [] := certificate_1670_checked

theorem certificate_1671_checked : certificate_1671.Valid 15 8 14 certificate_1671_q certificate_1671_edges 6 4 [] := by decide +kernel
theorem certificate_1671_valid : certificate_1671.Valid 15 8 (patternOrder [[],[1],[1],[2,2]]) (patternClique [[],[1],[1],[2,2]]) (patternEdges [[],[1],[1],[2,2]]) (patternAmount [[],[1],[1],[2,2]]) (patternEdgeCount [[],[1],[1],[2,2]]) [] := certificate_1671_checked

theorem certificate_1672_checked : certificate_1672.Valid 15 8 15 certificate_1672_q certificate_1672_edges 7 4 [] := by decide +kernel
theorem certificate_1672_valid : certificate_1672.Valid 15 8 (patternOrder [[],[1],[1],[2,3]]) (patternClique [[],[1],[1],[2,3]]) (patternEdges [[],[1],[1],[2,3]]) (patternAmount [[],[1],[1],[2,3]]) (patternEdgeCount [[],[1],[1],[2,3]]) [] := certificate_1672_checked

theorem certificate_1673_checked : certificate_1673.Valid 15 8 13 certificate_1673_q certificate_1673_edges 5 4 [] := by decide +kernel
theorem certificate_1673_valid : certificate_1673.Valid 15 8 (patternOrder [[],[1],[1,1],[2]]) (patternClique [[],[1],[1,1],[2]]) (patternEdges [[],[1],[1,1],[2]]) (patternAmount [[],[1],[1,1],[2]]) (patternEdgeCount [[],[1],[1,1],[2]]) [] := certificate_1673_checked

theorem certificate_1674_checked : certificate_1674.Valid 15 8 14 certificate_1674_q certificate_1674_edges 6 4 [] := by decide +kernel
theorem certificate_1674_valid : certificate_1674.Valid 15 8 (patternOrder [[],[1],[1,1],[3]]) (patternClique [[],[1],[1,1],[3]]) (patternEdges [[],[1],[1,1],[3]]) (patternAmount [[],[1],[1,1],[3]]) (patternEdgeCount [[],[1],[1,1],[3]]) [] := certificate_1674_checked

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

theorem patterns_15_8_9_verified_oai : ∀ D ∈ patterns_15_8_9, PatternVerified 15 8 D := by

  simp only [patterns_15_8_9, List.forall_mem_cons]

  exact ⟨⟨certificate_1659, certificate_1659_valid⟩, ⟨⟨certificate_1660, certificate_1660_valid⟩, ⟨⟨certificate_1661, certificate_1661_valid⟩, ⟨⟨certificate_1662, certificate_1662_valid⟩, ⟨⟨certificate_1663, certificate_1663_valid⟩, ⟨⟨certificate_1664, certificate_1664_valid⟩, ⟨⟨certificate_1665, certificate_1665_valid⟩, ⟨⟨certificate_1666, certificate_1666_valid⟩, ⟨⟨certificate_1667, certificate_1667_valid⟩, ⟨⟨certificate_1668, certificate_1668_valid⟩, ⟨⟨certificate_1669, certificate_1669_valid⟩, ⟨⟨certificate_1670, certificate_1670_valid⟩, ⟨⟨certificate_1671, certificate_1671_valid⟩, ⟨⟨certificate_1672, certificate_1672_valid⟩, ⟨⟨certificate_1673, certificate_1673_valid⟩, ⟨⟨certificate_1674, certificate_1674_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_8_9_verified_oai := @OAI.CycleClique.patterns_15_8_9_verified_oai
