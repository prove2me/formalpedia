-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_8_2_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:08:07.943982+00:00
-- url     : https://prove2.me/submissions/53c8feec-7df8-4a8e-becf-098aa4447d87

import Mathlib
import Definitions.Def_OAIQ107D038
import Definitions.Def_OAIQ107D129
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

theorem certificate_1547_checked : certificate_1547.Valid 15 8 13 certificate_1547_q certificate_1547_edges 5 3 [] := by decide +kernel
theorem certificate_1547_valid : certificate_1547.Valid 15 8 (patternOrder [[],[],[],[],[1,2,2]]) (patternClique [[],[],[],[],[1,2,2]]) (patternEdges [[],[],[],[],[1,2,2]]) (patternAmount [[],[],[],[],[1,2,2]]) (patternEdgeCount [[],[],[],[],[1,2,2]]) [] := certificate_1547_checked

theorem certificate_1548_checked : certificate_1548.Valid 15 8 14 certificate_1548_q certificate_1548_edges 6 3 [] := by decide +kernel
theorem certificate_1548_valid : certificate_1548.Valid 15 8 (patternOrder [[],[],[],[],[1,2,3]]) (patternClique [[],[],[],[],[1,2,3]]) (patternEdges [[],[],[],[],[1,2,3]]) (patternAmount [[],[],[],[],[1,2,3]]) (patternEdgeCount [[],[],[],[],[1,2,3]]) [] := certificate_1548_checked

theorem certificate_1549_checked : certificate_1549.Valid 15 8 15 certificate_1549_q certificate_1549_edges 7 3 [] := by decide +kernel
theorem certificate_1549_valid : certificate_1549.Valid 15 8 (patternOrder [[],[],[],[],[1,2,4]]) (patternClique [[],[],[],[],[1,2,4]]) (patternEdges [[],[],[],[],[1,2,4]]) (patternAmount [[],[],[],[],[1,2,4]]) (patternEdgeCount [[],[],[],[],[1,2,4]]) [] := certificate_1549_checked

theorem certificate_1550_checked : certificate_1550.Valid 15 8 13 certificate_1550_q certificate_1550_edges 5 3 [] := by decide +kernel
theorem certificate_1550_valid : certificate_1550.Valid 15 8 (patternOrder [[],[],[],[],[1,3,1]]) (patternClique [[],[],[],[],[1,3,1]]) (patternEdges [[],[],[],[],[1,3,1]]) (patternAmount [[],[],[],[],[1,3,1]]) (patternEdgeCount [[],[],[],[],[1,3,1]]) [] := certificate_1550_checked

theorem certificate_1551_checked : certificate_1551.Valid 15 8 14 certificate_1551_q certificate_1551_edges 6 3 [] := by decide +kernel
theorem certificate_1551_valid : certificate_1551.Valid 15 8 (patternOrder [[],[],[],[],[1,3,2]]) (patternClique [[],[],[],[],[1,3,2]]) (patternEdges [[],[],[],[],[1,3,2]]) (patternAmount [[],[],[],[],[1,3,2]]) (patternEdgeCount [[],[],[],[],[1,3,2]]) [] := certificate_1551_checked

theorem certificate_1552_checked : certificate_1552.Valid 15 8 15 certificate_1552_q certificate_1552_edges 7 3 [] := by decide +kernel
theorem certificate_1552_valid : certificate_1552.Valid 15 8 (patternOrder [[],[],[],[],[1,3,3]]) (patternClique [[],[],[],[],[1,3,3]]) (patternEdges [[],[],[],[],[1,3,3]]) (patternAmount [[],[],[],[],[1,3,3]]) (patternEdgeCount [[],[],[],[],[1,3,3]]) [] := certificate_1552_checked

theorem certificate_1553_checked : certificate_1553.Valid 15 8 14 certificate_1553_q certificate_1553_edges 6 3 [] := by decide +kernel
theorem certificate_1553_valid : certificate_1553.Valid 15 8 (patternOrder [[],[],[],[],[1,4,1]]) (patternClique [[],[],[],[],[1,4,1]]) (patternEdges [[],[],[],[],[1,4,1]]) (patternAmount [[],[],[],[],[1,4,1]]) (patternEdgeCount [[],[],[],[],[1,4,1]]) [] := certificate_1553_checked

theorem certificate_1554_checked : certificate_1554.Valid 15 8 15 certificate_1554_q certificate_1554_edges 7 3 [] := by decide +kernel
theorem certificate_1554_valid : certificate_1554.Valid 15 8 (patternOrder [[],[],[],[],[1,4,2]]) (patternClique [[],[],[],[],[1,4,2]]) (patternEdges [[],[],[],[],[1,4,2]]) (patternAmount [[],[],[],[],[1,4,2]]) (patternEdgeCount [[],[],[],[],[1,4,2]]) [] := certificate_1554_checked

theorem certificate_1555_checked : certificate_1555.Valid 15 8 15 certificate_1555_q certificate_1555_edges 7 3 [] := by decide +kernel
theorem certificate_1555_valid : certificate_1555.Valid 15 8 (patternOrder [[],[],[],[],[1,5,1]]) (patternClique [[],[],[],[],[1,5,1]]) (patternEdges [[],[],[],[],[1,5,1]]) (patternAmount [[],[],[],[],[1,5,1]]) (patternEdgeCount [[],[],[],[],[1,5,1]]) [] := certificate_1555_checked

theorem certificate_1556_checked : certificate_1556.Valid 15 8 12 certificate_1556_q certificate_1556_edges 4 2 [] := by decide +kernel
theorem certificate_1556_valid : certificate_1556.Valid 15 8 (patternOrder [[],[],[],[],[2],[2]]) (patternClique [[],[],[],[],[2],[2]]) (patternEdges [[],[],[],[],[2],[2]]) (patternAmount [[],[],[],[],[2],[2]]) (patternEdgeCount [[],[],[],[],[2],[2]]) [] := certificate_1556_checked

theorem certificate_1557_checked : certificate_1557.Valid 15 8 13 certificate_1557_q certificate_1557_edges 5 2 [] := by decide +kernel
theorem certificate_1557_valid : certificate_1557.Valid 15 8 (patternOrder [[],[],[],[],[2],[3]]) (patternClique [[],[],[],[],[2],[3]]) (patternEdges [[],[],[],[],[2],[3]]) (patternAmount [[],[],[],[],[2],[3]]) (patternEdgeCount [[],[],[],[],[2],[3]]) [] := certificate_1557_checked

theorem certificate_1558_checked : certificate_1558.Valid 15 8 14 certificate_1558_q certificate_1558_edges 6 2 [] := by decide +kernel
theorem certificate_1558_valid : certificate_1558.Valid 15 8 (patternOrder [[],[],[],[],[2],[4]]) (patternClique [[],[],[],[],[2],[4]]) (patternEdges [[],[],[],[],[2],[4]]) (patternAmount [[],[],[],[],[2],[4]]) (patternEdgeCount [[],[],[],[],[2],[4]]) [] := certificate_1558_checked

theorem certificate_1559_checked : certificate_1559.Valid 15 8 15 certificate_1559_q certificate_1559_edges 7 2 [] := by decide +kernel
theorem certificate_1559_valid : certificate_1559.Valid 15 8 (patternOrder [[],[],[],[],[2],[5]]) (patternClique [[],[],[],[],[2],[5]]) (patternEdges [[],[],[],[],[2],[5]]) (patternAmount [[],[],[],[],[2],[5]]) (patternEdgeCount [[],[],[],[],[2],[5]]) [] := certificate_1559_checked

theorem certificate_1560_checked : certificate_1560.Valid 15 8 13 certificate_1560_q certificate_1560_edges 5 3 [] := by decide +kernel
theorem certificate_1560_valid : certificate_1560.Valid 15 8 (patternOrder [[],[],[],[],[2,1,2]]) (patternClique [[],[],[],[],[2,1,2]]) (patternEdges [[],[],[],[],[2,1,2]]) (patternAmount [[],[],[],[],[2,1,2]]) (patternEdgeCount [[],[],[],[],[2,1,2]]) [] := certificate_1560_checked

theorem certificate_1561_checked : certificate_1561.Valid 15 8 14 certificate_1561_q certificate_1561_edges 6 3 [] := by decide +kernel
theorem certificate_1561_valid : certificate_1561.Valid 15 8 (patternOrder [[],[],[],[],[2,1,3]]) (patternClique [[],[],[],[],[2,1,3]]) (patternEdges [[],[],[],[],[2,1,3]]) (patternAmount [[],[],[],[],[2,1,3]]) (patternEdgeCount [[],[],[],[],[2,1,3]]) [] := certificate_1561_checked

theorem certificate_1562_checked : certificate_1562.Valid 15 8 15 certificate_1562_q certificate_1562_edges 7 3 [] := by decide +kernel
theorem certificate_1562_valid : certificate_1562.Valid 15 8 (patternOrder [[],[],[],[],[2,1,4]]) (patternClique [[],[],[],[],[2,1,4]]) (patternEdges [[],[],[],[],[2,1,4]]) (patternAmount [[],[],[],[],[2,1,4]]) (patternEdgeCount [[],[],[],[],[2,1,4]]) [] := certificate_1562_checked

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

theorem patterns_15_8_2_verified_oai : ∀ D ∈ patterns_15_8_2, PatternVerified 15 8 D := by

  simp only [patterns_15_8_2, List.forall_mem_cons]

  exact ⟨⟨certificate_1547, certificate_1547_valid⟩, ⟨⟨certificate_1548, certificate_1548_valid⟩, ⟨⟨certificate_1549, certificate_1549_valid⟩, ⟨⟨certificate_1550, certificate_1550_valid⟩, ⟨⟨certificate_1551, certificate_1551_valid⟩, ⟨⟨certificate_1552, certificate_1552_valid⟩, ⟨⟨certificate_1553, certificate_1553_valid⟩, ⟨⟨certificate_1554, certificate_1554_valid⟩, ⟨⟨certificate_1555, certificate_1555_valid⟩, ⟨⟨certificate_1556, certificate_1556_valid⟩, ⟨⟨certificate_1557, certificate_1557_valid⟩, ⟨⟨certificate_1558, certificate_1558_valid⟩, ⟨⟨certificate_1559, certificate_1559_valid⟩, ⟨⟨certificate_1560, certificate_1560_valid⟩, ⟨⟨certificate_1561, certificate_1561_valid⟩, ⟨⟨certificate_1562, certificate_1562_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_8_2_verified_oai := @OAI.CycleClique.patterns_15_8_2_verified_oai
