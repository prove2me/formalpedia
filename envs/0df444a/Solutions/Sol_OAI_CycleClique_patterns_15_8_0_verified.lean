-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_8_0_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:04:27.571884+00:00
-- url     : https://prove2.me/submissions/8aa388cf-b525-4fb6-a402-275365539b76

import Mathlib
import Definitions.Def_OAIQ107D128
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

theorem certificate_1515_checked : certificate_1515.Valid 15 8 8 certificate_1515_q certificate_1515_edges 0 0 [] := by decide +kernel
theorem certificate_1515_valid : certificate_1515.Valid 15 8 (patternOrder [[],[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[],[]]) [] := certificate_1515_checked

theorem certificate_1516_checked : certificate_1516.Valid 15 8 9 certificate_1516_q certificate_1516_edges 1 1 [] := by decide +kernel
theorem certificate_1516_valid : certificate_1516.Valid 15 8 (patternOrder [[],[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[],[1]]) [] := certificate_1516_checked

theorem certificate_1517_checked : certificate_1517.Valid 15 8 10 certificate_1517_q certificate_1517_edges 2 1 [] := by decide +kernel
theorem certificate_1517_valid : certificate_1517.Valid 15 8 (patternOrder [[],[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[],[2]]) [] := certificate_1517_checked

theorem certificate_1518_checked : certificate_1518.Valid 15 8 11 certificate_1518_q certificate_1518_edges 3 1 [] := by decide +kernel
theorem certificate_1518_valid : certificate_1518.Valid 15 8 (patternOrder [[],[],[],[],[],[],[3]]) (patternClique [[],[],[],[],[],[],[3]]) (patternEdges [[],[],[],[],[],[],[3]]) (patternAmount [[],[],[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[],[],[3]]) [] := certificate_1518_checked

theorem certificate_1519_checked : certificate_1519.Valid 15 8 12 certificate_1519_q certificate_1519_edges 4 1 [] := by decide +kernel
theorem certificate_1519_valid : certificate_1519.Valid 15 8 (patternOrder [[],[],[],[],[],[],[4]]) (patternClique [[],[],[],[],[],[],[4]]) (patternEdges [[],[],[],[],[],[],[4]]) (patternAmount [[],[],[],[],[],[],[4]]) (patternEdgeCount [[],[],[],[],[],[],[4]]) [] := certificate_1519_checked

theorem certificate_1520_checked : certificate_1520.Valid 15 8 13 certificate_1520_q certificate_1520_edges 5 1 [] := by decide +kernel
theorem certificate_1520_valid : certificate_1520.Valid 15 8 (patternOrder [[],[],[],[],[],[],[5]]) (patternClique [[],[],[],[],[],[],[5]]) (patternEdges [[],[],[],[],[],[],[5]]) (patternAmount [[],[],[],[],[],[],[5]]) (patternEdgeCount [[],[],[],[],[],[],[5]]) [] := certificate_1520_checked

theorem certificate_1521_checked : certificate_1521.Valid 15 8 14 certificate_1521_q certificate_1521_edges 6 1 [] := by decide +kernel
theorem certificate_1521_valid : certificate_1521.Valid 15 8 (patternOrder [[],[],[],[],[],[],[6]]) (patternClique [[],[],[],[],[],[],[6]]) (patternEdges [[],[],[],[],[],[],[6]]) (patternAmount [[],[],[],[],[],[],[6]]) (patternEdgeCount [[],[],[],[],[],[],[6]]) [] := certificate_1521_checked

theorem certificate_1522_checked : certificate_1522.Valid 15 8 15 certificate_1522_q certificate_1522_edges 7 1 [] := by decide +kernel
theorem certificate_1522_valid : certificate_1522.Valid 15 8 (patternOrder [[],[],[],[],[],[],[7]]) (patternClique [[],[],[],[],[],[],[7]]) (patternEdges [[],[],[],[],[],[],[7]]) (patternAmount [[],[],[],[],[],[],[7]]) (patternEdgeCount [[],[],[],[],[],[],[7]]) [] := certificate_1522_checked

theorem certificate_1523_checked : certificate_1523.Valid 15 8 10 certificate_1523_q certificate_1523_edges 2 2 [] := by decide +kernel
theorem certificate_1523_valid : certificate_1523.Valid 15 8 (patternOrder [[],[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[],[1,1]]) [] := certificate_1523_checked

theorem certificate_1524_checked : certificate_1524.Valid 15 8 11 certificate_1524_q certificate_1524_edges 3 2 [] := by decide +kernel
theorem certificate_1524_valid : certificate_1524.Valid 15 8 (patternOrder [[],[],[],[],[],[1,2]]) (patternClique [[],[],[],[],[],[1,2]]) (patternEdges [[],[],[],[],[],[1,2]]) (patternAmount [[],[],[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[],[],[1,2]]) [] := certificate_1524_checked

theorem certificate_1525_checked : certificate_1525.Valid 15 8 12 certificate_1525_q certificate_1525_edges 4 2 [] := by decide +kernel
theorem certificate_1525_valid : certificate_1525.Valid 15 8 (patternOrder [[],[],[],[],[],[1,3]]) (patternClique [[],[],[],[],[],[1,3]]) (patternEdges [[],[],[],[],[],[1,3]]) (patternAmount [[],[],[],[],[],[1,3]]) (patternEdgeCount [[],[],[],[],[],[1,3]]) [] := certificate_1525_checked

theorem certificate_1526_checked : certificate_1526.Valid 15 8 13 certificate_1526_q certificate_1526_edges 5 2 [] := by decide +kernel
theorem certificate_1526_valid : certificate_1526.Valid 15 8 (patternOrder [[],[],[],[],[],[1,4]]) (patternClique [[],[],[],[],[],[1,4]]) (patternEdges [[],[],[],[],[],[1,4]]) (patternAmount [[],[],[],[],[],[1,4]]) (patternEdgeCount [[],[],[],[],[],[1,4]]) [] := certificate_1526_checked

theorem certificate_1527_checked : certificate_1527.Valid 15 8 14 certificate_1527_q certificate_1527_edges 6 2 [] := by decide +kernel
theorem certificate_1527_valid : certificate_1527.Valid 15 8 (patternOrder [[],[],[],[],[],[1,5]]) (patternClique [[],[],[],[],[],[1,5]]) (patternEdges [[],[],[],[],[],[1,5]]) (patternAmount [[],[],[],[],[],[1,5]]) (patternEdgeCount [[],[],[],[],[],[1,5]]) [] := certificate_1527_checked

theorem certificate_1528_checked : certificate_1528.Valid 15 8 15 certificate_1528_q certificate_1528_edges 7 2 [] := by decide +kernel
theorem certificate_1528_valid : certificate_1528.Valid 15 8 (patternOrder [[],[],[],[],[],[1,6]]) (patternClique [[],[],[],[],[],[1,6]]) (patternEdges [[],[],[],[],[],[1,6]]) (patternAmount [[],[],[],[],[],[1,6]]) (patternEdgeCount [[],[],[],[],[],[1,6]]) [] := certificate_1528_checked

theorem certificate_1529_checked : certificate_1529.Valid 15 8 12 certificate_1529_q certificate_1529_edges 4 2 [] := by decide +kernel
theorem certificate_1529_valid : certificate_1529.Valid 15 8 (patternOrder [[],[],[],[],[],[2,2]]) (patternClique [[],[],[],[],[],[2,2]]) (patternEdges [[],[],[],[],[],[2,2]]) (patternAmount [[],[],[],[],[],[2,2]]) (patternEdgeCount [[],[],[],[],[],[2,2]]) [] := certificate_1529_checked

theorem certificate_1530_checked : certificate_1530.Valid 15 8 13 certificate_1530_q certificate_1530_edges 5 2 [] := by decide +kernel
theorem certificate_1530_valid : certificate_1530.Valid 15 8 (patternOrder [[],[],[],[],[],[2,3]]) (patternClique [[],[],[],[],[],[2,3]]) (patternEdges [[],[],[],[],[],[2,3]]) (patternAmount [[],[],[],[],[],[2,3]]) (patternEdgeCount [[],[],[],[],[],[2,3]]) [] := certificate_1530_checked

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

theorem patterns_15_8_0_verified_oai : ∀ D ∈ patterns_15_8_0, PatternVerified 15 8 D := by

  simp only [patterns_15_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_1515, certificate_1515_valid⟩, ⟨⟨certificate_1516, certificate_1516_valid⟩, ⟨⟨certificate_1517, certificate_1517_valid⟩, ⟨⟨certificate_1518, certificate_1518_valid⟩, ⟨⟨certificate_1519, certificate_1519_valid⟩, ⟨⟨certificate_1520, certificate_1520_valid⟩, ⟨⟨certificate_1521, certificate_1521_valid⟩, ⟨⟨certificate_1522, certificate_1522_valid⟩, ⟨⟨certificate_1523, certificate_1523_valid⟩, ⟨⟨certificate_1524, certificate_1524_valid⟩, ⟨⟨certificate_1525, certificate_1525_valid⟩, ⟨⟨certificate_1526, certificate_1526_valid⟩, ⟨⟨certificate_1527, certificate_1527_valid⟩, ⟨⟨certificate_1528, certificate_1528_valid⟩, ⟨⟨certificate_1529, certificate_1529_valid⟩, ⟨⟨certificate_1530, certificate_1530_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_8_0_verified_oai := @OAI.CycleClique.patterns_15_8_0_verified_oai
