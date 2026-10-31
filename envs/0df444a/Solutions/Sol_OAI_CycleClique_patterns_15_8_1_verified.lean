-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_8_1_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:01:10.789538+00:00
-- url     : https://prove2.me/submissions/55dc12c5-94ec-4b52-afe2-ddee1ec41884

import Mathlib
import Definitions.Def_OAIQ107D036
import Definitions.Def_OAIQ107D037
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates048
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1531_checked : certificate_1531.Valid 15 8 14 certificate_1531_q certificate_1531_edges 6 2 [] := by decide +kernel
theorem certificate_1531_valid : certificate_1531.Valid 15 8 (patternOrder [[],[],[],[],[],[2,4]]) (patternClique [[],[],[],[],[],[2,4]]) (patternEdges [[],[],[],[],[],[2,4]]) (patternAmount [[],[],[],[],[],[2,4]]) (patternEdgeCount [[],[],[],[],[],[2,4]]) [] := certificate_1531_checked

theorem certificate_1532_checked : certificate_1532.Valid 15 8 15 certificate_1532_q certificate_1532_edges 7 2 [] := by decide +kernel
theorem certificate_1532_valid : certificate_1532.Valid 15 8 (patternOrder [[],[],[],[],[],[2,5]]) (patternClique [[],[],[],[],[],[2,5]]) (patternEdges [[],[],[],[],[],[2,5]]) (patternAmount [[],[],[],[],[],[2,5]]) (patternEdgeCount [[],[],[],[],[],[2,5]]) [] := certificate_1532_checked

theorem certificate_1533_checked : certificate_1533.Valid 15 8 14 certificate_1533_q certificate_1533_edges 6 2 [] := by decide +kernel
theorem certificate_1533_valid : certificate_1533.Valid 15 8 (patternOrder [[],[],[],[],[],[3,3]]) (patternClique [[],[],[],[],[],[3,3]]) (patternEdges [[],[],[],[],[],[3,3]]) (patternAmount [[],[],[],[],[],[3,3]]) (patternEdgeCount [[],[],[],[],[],[3,3]]) [] := certificate_1533_checked

theorem certificate_1534_checked : certificate_1534.Valid 15 8 15 certificate_1534_q certificate_1534_edges 7 2 [] := by decide +kernel
theorem certificate_1534_valid : certificate_1534.Valid 15 8 (patternOrder [[],[],[],[],[],[3,4]]) (patternClique [[],[],[],[],[],[3,4]]) (patternEdges [[],[],[],[],[],[3,4]]) (patternAmount [[],[],[],[],[],[3,4]]) (patternEdgeCount [[],[],[],[],[],[3,4]]) [] := certificate_1534_checked

theorem certificate_1535_checked : certificate_1535.Valid 15 8 10 certificate_1535_q certificate_1535_edges 2 2 [] := by decide +kernel
theorem certificate_1535_valid : certificate_1535.Valid 15 8 (patternOrder [[],[],[],[],[1],[1]]) (patternClique [[],[],[],[],[1],[1]]) (patternEdges [[],[],[],[],[1],[1]]) (patternAmount [[],[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[],[1],[1]]) [] := certificate_1535_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates049
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1536_checked : certificate_1536.Valid 15 8 11 certificate_1536_q certificate_1536_edges 3 2 [] := by decide +kernel
theorem certificate_1536_valid : certificate_1536.Valid 15 8 (patternOrder [[],[],[],[],[1],[2]]) (patternClique [[],[],[],[],[1],[2]]) (patternEdges [[],[],[],[],[1],[2]]) (patternAmount [[],[],[],[],[1],[2]]) (patternEdgeCount [[],[],[],[],[1],[2]]) [] := certificate_1536_checked

theorem certificate_1537_checked : certificate_1537.Valid 15 8 12 certificate_1537_q certificate_1537_edges 4 2 [] := by decide +kernel
theorem certificate_1537_valid : certificate_1537.Valid 15 8 (patternOrder [[],[],[],[],[1],[3]]) (patternClique [[],[],[],[],[1],[3]]) (patternEdges [[],[],[],[],[1],[3]]) (patternAmount [[],[],[],[],[1],[3]]) (patternEdgeCount [[],[],[],[],[1],[3]]) [] := certificate_1537_checked

theorem certificate_1538_checked : certificate_1538.Valid 15 8 13 certificate_1538_q certificate_1538_edges 5 2 [] := by decide +kernel
theorem certificate_1538_valid : certificate_1538.Valid 15 8 (patternOrder [[],[],[],[],[1],[4]]) (patternClique [[],[],[],[],[1],[4]]) (patternEdges [[],[],[],[],[1],[4]]) (patternAmount [[],[],[],[],[1],[4]]) (patternEdgeCount [[],[],[],[],[1],[4]]) [] := certificate_1538_checked

theorem certificate_1539_checked : certificate_1539.Valid 15 8 14 certificate_1539_q certificate_1539_edges 6 2 [] := by decide +kernel
theorem certificate_1539_valid : certificate_1539.Valid 15 8 (patternOrder [[],[],[],[],[1],[5]]) (patternClique [[],[],[],[],[1],[5]]) (patternEdges [[],[],[],[],[1],[5]]) (patternAmount [[],[],[],[],[1],[5]]) (patternEdgeCount [[],[],[],[],[1],[5]]) [] := certificate_1539_checked

theorem certificate_1540_checked : certificate_1540.Valid 15 8 15 certificate_1540_q certificate_1540_edges 7 2 [] := by decide +kernel
theorem certificate_1540_valid : certificate_1540.Valid 15 8 (patternOrder [[],[],[],[],[1],[6]]) (patternClique [[],[],[],[],[1],[6]]) (patternEdges [[],[],[],[],[1],[6]]) (patternAmount [[],[],[],[],[1],[6]]) (patternEdgeCount [[],[],[],[],[1],[6]]) [] := certificate_1540_checked

theorem certificate_1541_checked : certificate_1541.Valid 15 8 11 certificate_1541_q certificate_1541_edges 3 3 [] := by decide +kernel
theorem certificate_1541_valid : certificate_1541.Valid 15 8 (patternOrder [[],[],[],[],[1,1,1]]) (patternClique [[],[],[],[],[1,1,1]]) (patternEdges [[],[],[],[],[1,1,1]]) (patternAmount [[],[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[],[1,1,1]]) [] := certificate_1541_checked

theorem certificate_1542_checked : certificate_1542.Valid 15 8 12 certificate_1542_q certificate_1542_edges 4 3 [] := by decide +kernel
theorem certificate_1542_valid : certificate_1542.Valid 15 8 (patternOrder [[],[],[],[],[1,1,2]]) (patternClique [[],[],[],[],[1,1,2]]) (patternEdges [[],[],[],[],[1,1,2]]) (patternAmount [[],[],[],[],[1,1,2]]) (patternEdgeCount [[],[],[],[],[1,1,2]]) [] := certificate_1542_checked

theorem certificate_1543_checked : certificate_1543.Valid 15 8 13 certificate_1543_q certificate_1543_edges 5 3 [] := by decide +kernel
theorem certificate_1543_valid : certificate_1543.Valid 15 8 (patternOrder [[],[],[],[],[1,1,3]]) (patternClique [[],[],[],[],[1,1,3]]) (patternEdges [[],[],[],[],[1,1,3]]) (patternAmount [[],[],[],[],[1,1,3]]) (patternEdgeCount [[],[],[],[],[1,1,3]]) [] := certificate_1543_checked

theorem certificate_1544_checked : certificate_1544.Valid 15 8 14 certificate_1544_q certificate_1544_edges 6 3 [] := by decide +kernel
theorem certificate_1544_valid : certificate_1544.Valid 15 8 (patternOrder [[],[],[],[],[1,1,4]]) (patternClique [[],[],[],[],[1,1,4]]) (patternEdges [[],[],[],[],[1,1,4]]) (patternAmount [[],[],[],[],[1,1,4]]) (patternEdgeCount [[],[],[],[],[1,1,4]]) [] := certificate_1544_checked

theorem certificate_1545_checked : certificate_1545.Valid 15 8 15 certificate_1545_q certificate_1545_edges 7 3 [] := by decide +kernel
theorem certificate_1545_valid : certificate_1545.Valid 15 8 (patternOrder [[],[],[],[],[1,1,5]]) (patternClique [[],[],[],[],[1,1,5]]) (patternEdges [[],[],[],[],[1,1,5]]) (patternAmount [[],[],[],[],[1,1,5]]) (patternEdgeCount [[],[],[],[],[1,1,5]]) [] := certificate_1545_checked

theorem certificate_1546_checked : certificate_1546.Valid 15 8 12 certificate_1546_q certificate_1546_edges 4 3 [] := by decide +kernel
theorem certificate_1546_valid : certificate_1546.Valid 15 8 (patternOrder [[],[],[],[],[1,2,1]]) (patternClique [[],[],[],[],[1,2,1]]) (patternEdges [[],[],[],[],[1,2,1]]) (patternAmount [[],[],[],[],[1,2,1]]) (patternEdgeCount [[],[],[],[],[1,2,1]]) [] := certificate_1546_checked

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

theorem patterns_15_8_1_verified_oai : ∀ D ∈ patterns_15_8_1, PatternVerified 15 8 D := by

  simp only [patterns_15_8_1, List.forall_mem_cons]

  exact ⟨⟨certificate_1531, certificate_1531_valid⟩, ⟨⟨certificate_1532, certificate_1532_valid⟩, ⟨⟨certificate_1533, certificate_1533_valid⟩, ⟨⟨certificate_1534, certificate_1534_valid⟩, ⟨⟨certificate_1535, certificate_1535_valid⟩, ⟨⟨certificate_1536, certificate_1536_valid⟩, ⟨⟨certificate_1537, certificate_1537_valid⟩, ⟨⟨certificate_1538, certificate_1538_valid⟩, ⟨⟨certificate_1539, certificate_1539_valid⟩, ⟨⟨certificate_1540, certificate_1540_valid⟩, ⟨⟨certificate_1541, certificate_1541_valid⟩, ⟨⟨certificate_1542, certificate_1542_valid⟩, ⟨⟨certificate_1543, certificate_1543_valid⟩, ⟨⟨certificate_1544, certificate_1544_valid⟩, ⟨⟨certificate_1545, certificate_1545_valid⟩, ⟨⟨certificate_1546, certificate_1546_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_8_1_verified_oai := @OAI.CycleClique.patterns_15_8_1_verified_oai
