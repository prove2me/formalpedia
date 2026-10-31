-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_21_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:51:32.563782+00:00
-- url     : https://prove2.me/submissions/8c9c7209-9f24-4e0d-be2b-17099b76deec

import Mathlib
import Definitions.Def_OAIQ107D128
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates047
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1487_checked : certificate_1487.Valid 15 7 15 certificate_1487_q certificate_1487_edges 8 6 [] := by decide +kernel
theorem certificate_1487_valid : certificate_1487.Valid 15 7 (patternOrder [[1,1,1,3,1,1]]) (patternClique [[1,1,1,3,1,1]]) (patternEdges [[1,1,1,3,1,1]]) (patternAmount [[1,1,1,3,1,1]]) (patternEdgeCount [[1,1,1,3,1,1]]) [] := certificate_1487_checked

theorem certificate_1488_checked : certificate_1488.Valid 15 7 14 certificate_1488_q certificate_1488_edges 7 5 [] := by decide +kernel
theorem certificate_1488_valid : certificate_1488.Valid 15 7 (patternOrder [[1,1,2],[1,2]]) (patternClique [[1,1,2],[1,2]]) (patternEdges [[1,1,2],[1,2]]) (patternAmount [[1,1,2],[1,2]]) (patternEdgeCount [[1,1,2],[1,2]]) [] := certificate_1488_checked

theorem certificate_1489_checked : certificate_1489.Valid 15 7 15 certificate_1489_q certificate_1489_edges 8 5 [] := by decide +kernel
theorem certificate_1489_valid : certificate_1489.Valid 15 7 (patternOrder [[1,1,2],[1,3]]) (patternClique [[1,1,2],[1,3]]) (patternEdges [[1,1,2],[1,3]]) (patternAmount [[1,1,2],[1,3]]) (patternEdgeCount [[1,1,2],[1,3]]) [] := certificate_1489_checked

theorem certificate_1490_checked : certificate_1490.Valid 15 7 15 certificate_1490_q certificate_1490_edges 8 5 [] := by decide +kernel
theorem certificate_1490_valid : certificate_1490.Valid 15 7 (patternOrder [[1,1,2],[2,2]]) (patternClique [[1,1,2],[2,2]]) (patternEdges [[1,1,2],[2,2]]) (patternAmount [[1,1,2],[2,2]]) (patternEdgeCount [[1,1,2],[2,2]]) [] := certificate_1490_checked

theorem certificate_1491_checked : certificate_1491.Valid 15 7 14 certificate_1491_q certificate_1491_edges 7 5 [] := by decide +kernel
theorem certificate_1491_valid : certificate_1491.Valid 15 7 (patternOrder [[1,1,2,1],[2]]) (patternClique [[1,1,2,1],[2]]) (patternEdges [[1,1,2,1],[2]]) (patternAmount [[1,1,2,1],[2]]) (patternEdgeCount [[1,1,2,1],[2]]) [] := certificate_1491_checked

theorem certificate_1492_checked : certificate_1492.Valid 15 7 15 certificate_1492_q certificate_1492_edges 8 5 [] := by decide +kernel
theorem certificate_1492_valid : certificate_1492.Valid 15 7 (patternOrder [[1,1,2,1],[3]]) (patternClique [[1,1,2,1],[3]]) (patternEdges [[1,1,2,1],[3]]) (patternAmount [[1,1,2,1],[3]]) (patternEdgeCount [[1,1,2,1],[3]]) [] := certificate_1492_checked

theorem certificate_1493_checked : certificate_1493.Valid 15 7 15 certificate_1493_q certificate_1493_edges 8 6 [] := by decide +kernel
theorem certificate_1493_valid : certificate_1493.Valid 15 7 (patternOrder [[1,1,2,1,1,2]]) (patternClique [[1,1,2,1,1,2]]) (patternEdges [[1,1,2,1,1,2]]) (patternAmount [[1,1,2,1,1,2]]) (patternEdgeCount [[1,1,2,1,1,2]]) [] := certificate_1493_checked

theorem certificate_1494_checked : certificate_1494.Valid 15 7 15 certificate_1494_q certificate_1494_edges 8 6 [] := by decide +kernel
theorem certificate_1494_valid : certificate_1494.Valid 15 7 (patternOrder [[1,1,2,1,2,1]]) (patternClique [[1,1,2,1,2,1]]) (patternEdges [[1,1,2,1,2,1]]) (patternAmount [[1,1,2,1,2,1]]) (patternEdgeCount [[1,1,2,1,2,1]]) [] := certificate_1494_checked

theorem certificate_1495_checked : certificate_1495.Valid 15 7 15 certificate_1495_q certificate_1495_edges 8 5 [] := by decide +kernel
theorem certificate_1495_valid : certificate_1495.Valid 15 7 (patternOrder [[1,1,2,2],[2]]) (patternClique [[1,1,2,2],[2]]) (patternEdges [[1,1,2,2],[2]]) (patternAmount [[1,1,2,2],[2]]) (patternEdgeCount [[1,1,2,2],[2]]) [] := certificate_1495_checked

theorem certificate_1496_checked : certificate_1496.Valid 15 7 15 certificate_1496_q certificate_1496_edges 8 6 [] := by decide +kernel
theorem certificate_1496_valid : certificate_1496.Valid 15 7 (patternOrder [[1,1,2,2,1,1]]) (patternClique [[1,1,2,2,1,1]]) (patternEdges [[1,1,2,2,1,1]]) (patternAmount [[1,1,2,2,1,1]]) (patternEdgeCount [[1,1,2,2,1,1]]) [] := certificate_1496_checked

theorem certificate_1497_checked : certificate_1497.Valid 15 7 15 certificate_1497_q certificate_1497_edges 8 5 [] := by decide +kernel
theorem certificate_1497_valid : certificate_1497.Valid 15 7 (patternOrder [[1,1,3],[1,2]]) (patternClique [[1,1,3],[1,2]]) (patternEdges [[1,1,3],[1,2]]) (patternAmount [[1,1,3],[1,2]]) (patternEdgeCount [[1,1,3],[1,2]]) [] := certificate_1497_checked

theorem certificate_1498_checked : certificate_1498.Valid 15 7 15 certificate_1498_q certificate_1498_edges 8 5 [] := by decide +kernel
theorem certificate_1498_valid : certificate_1498.Valid 15 7 (patternOrder [[1,1,3,1],[2]]) (patternClique [[1,1,3,1],[2]]) (patternEdges [[1,1,3,1],[2]]) (patternAmount [[1,1,3,1],[2]]) (patternEdgeCount [[1,1,3,1],[2]]) [] := certificate_1498_checked

theorem certificate_1499_checked : certificate_1499.Valid 15 7 14 certificate_1499_q certificate_1499_edges 7 5 [] := by decide +kernel
theorem certificate_1499_valid : certificate_1499.Valid 15 7 (patternOrder [[1,2],[1,2,1]]) (patternClique [[1,2],[1,2,1]]) (patternEdges [[1,2],[1,2,1]]) (patternAmount [[1,2],[1,2,1]]) (patternEdgeCount [[1,2],[1,2,1]]) [] := certificate_1499_checked

theorem certificate_1500_checked : certificate_1500.Valid 15 7 15 certificate_1500_q certificate_1500_edges 8 5 [] := by decide +kernel
theorem certificate_1500_valid : certificate_1500.Valid 15 7 (patternOrder [[1,2],[1,2,2]]) (patternClique [[1,2],[1,2,2]]) (patternEdges [[1,2],[1,2,2]]) (patternAmount [[1,2],[1,2,2]]) (patternEdgeCount [[1,2],[1,2,2]]) [] := certificate_1500_checked

theorem certificate_1501_checked : certificate_1501.Valid 15 7 15 certificate_1501_q certificate_1501_edges 8 5 [] := by decide +kernel
theorem certificate_1501_valid : certificate_1501.Valid 15 7 (patternOrder [[1,2],[1,3,1]]) (patternClique [[1,2],[1,3,1]]) (patternEdges [[1,2],[1,3,1]]) (patternAmount [[1,2],[1,3,1]]) (patternEdgeCount [[1,2],[1,3,1]]) [] := certificate_1501_checked

theorem certificate_1502_checked : certificate_1502.Valid 15 7 14 certificate_1502_q certificate_1502_edges 7 4 [] := by decide +kernel
theorem certificate_1502_valid : certificate_1502.Valid 15 7 (patternOrder [[1,2],[2],[2]]) (patternClique [[1,2],[2],[2]]) (patternEdges [[1,2],[2],[2]]) (patternAmount [[1,2],[2],[2]]) (patternEdgeCount [[1,2],[2],[2]]) [] := certificate_1502_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns15x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_15_7_21_verified_oai : ∀ D ∈ patterns_15_7_21, PatternVerified 15 7 D := by

  simp only [patterns_15_7_21, List.forall_mem_cons]

  exact ⟨⟨certificate_1487, certificate_1487_valid⟩, ⟨⟨certificate_1488, certificate_1488_valid⟩, ⟨⟨certificate_1489, certificate_1489_valid⟩, ⟨⟨certificate_1490, certificate_1490_valid⟩, ⟨⟨certificate_1491, certificate_1491_valid⟩, ⟨⟨certificate_1492, certificate_1492_valid⟩, ⟨⟨certificate_1493, certificate_1493_valid⟩, ⟨⟨certificate_1494, certificate_1494_valid⟩, ⟨⟨certificate_1495, certificate_1495_valid⟩, ⟨⟨certificate_1496, certificate_1496_valid⟩, ⟨⟨certificate_1497, certificate_1497_valid⟩, ⟨⟨certificate_1498, certificate_1498_valid⟩, ⟨⟨certificate_1499, certificate_1499_valid⟩, ⟨⟨certificate_1500, certificate_1500_valid⟩, ⟨⟨certificate_1501, certificate_1501_valid⟩, ⟨⟨certificate_1502, certificate_1502_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_21_verified_oai := @OAI.CycleClique.patterns_15_7_21_verified_oai
