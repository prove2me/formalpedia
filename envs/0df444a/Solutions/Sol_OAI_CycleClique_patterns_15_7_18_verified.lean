-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_18_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:44:30.958413+00:00
-- url     : https://prove2.me/submissions/70622411-8cae-4f4e-a4a1-af5a42d5927b

import Mathlib
import Definitions.Def_OAIQ107D128
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates045
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1439_checked : certificate_1439.Valid 15 7 15 certificate_1439_q certificate_1439_edges 8 5 [] := by decide +kernel
theorem certificate_1439_valid : certificate_1439.Valid 15 7 (patternOrder [[1],[1,2,3,1]]) (patternClique [[1],[1,2,3,1]]) (patternEdges [[1],[1,2,3,1]]) (patternAmount [[1],[1,2,3,1]]) (patternEdgeCount [[1],[1,2,3,1]]) [] := certificate_1439_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates046
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1440_checked : certificate_1440.Valid 15 7 14 certificate_1440_q certificate_1440_edges 7 4 [] := by decide +kernel
theorem certificate_1440_valid : certificate_1440.Valid 15 7 (patternOrder [[1],[1,3],[2]]) (patternClique [[1],[1,3],[2]]) (patternEdges [[1],[1,3],[2]]) (patternAmount [[1],[1,3],[2]]) (patternEdgeCount [[1],[1,3],[2]]) [] := certificate_1440_checked

theorem certificate_1441_checked : certificate_1441.Valid 15 7 15 certificate_1441_q certificate_1441_edges 8 4 [] := by decide +kernel
theorem certificate_1441_valid : certificate_1441.Valid 15 7 (patternOrder [[1],[1,3],[3]]) (patternClique [[1],[1,3],[3]]) (patternEdges [[1],[1,3],[3]]) (patternAmount [[1],[1,3],[3]]) (patternEdgeCount [[1],[1,3],[3]]) [] := certificate_1441_checked

theorem certificate_1442_checked : certificate_1442.Valid 15 7 15 certificate_1442_q certificate_1442_edges 8 5 [] := by decide +kernel
theorem certificate_1442_valid : certificate_1442.Valid 15 7 (patternOrder [[1],[1,3,1,2]]) (patternClique [[1],[1,3,1,2]]) (patternEdges [[1],[1,3,1,2]]) (patternAmount [[1],[1,3,1,2]]) (patternEdgeCount [[1],[1,3,1,2]]) [] := certificate_1442_checked

theorem certificate_1443_checked : certificate_1443.Valid 15 7 15 certificate_1443_q certificate_1443_edges 8 4 [] := by decide +kernel
theorem certificate_1443_valid : certificate_1443.Valid 15 7 (patternOrder [[1],[1,4],[2]]) (patternClique [[1],[1,4],[2]]) (patternEdges [[1],[1,4],[2]]) (patternAmount [[1],[1,4],[2]]) (patternEdgeCount [[1],[1,4],[2]]) [] := certificate_1443_checked

theorem certificate_1444_checked : certificate_1444.Valid 15 7 14 certificate_1444_q certificate_1444_edges 7 4 [] := by decide +kernel
theorem certificate_1444_valid : certificate_1444.Valid 15 7 (patternOrder [[1],[2],[2,2]]) (patternClique [[1],[2],[2,2]]) (patternEdges [[1],[2],[2,2]]) (patternAmount [[1],[2],[2,2]]) (patternEdgeCount [[1],[2],[2,2]]) [] := certificate_1444_checked

theorem certificate_1445_checked : certificate_1445.Valid 15 7 15 certificate_1445_q certificate_1445_edges 8 4 [] := by decide +kernel
theorem certificate_1445_valid : certificate_1445.Valid 15 7 (patternOrder [[1],[2],[2,3]]) (patternClique [[1],[2],[2,3]]) (patternEdges [[1],[2],[2,3]]) (patternAmount [[1],[2],[2,3]]) (patternEdgeCount [[1],[2],[2,3]]) [] := certificate_1445_checked

theorem certificate_1446_checked : certificate_1446.Valid 15 7 14 certificate_1446_q certificate_1446_edges 7 5 [] := by decide +kernel
theorem certificate_1446_valid : certificate_1446.Valid 15 7 (patternOrder [[1],[2,1,1,2]]) (patternClique [[1],[2,1,1,2]]) (patternEdges [[1],[2,1,1,2]]) (patternAmount [[1],[2,1,1,2]]) (patternEdgeCount [[1],[2,1,1,2]]) [] := certificate_1446_checked

theorem certificate_1447_checked : certificate_1447.Valid 15 7 15 certificate_1447_q certificate_1447_edges 8 5 [] := by decide +kernel
theorem certificate_1447_valid : certificate_1447.Valid 15 7 (patternOrder [[1],[2,1,1,3]]) (patternClique [[1],[2,1,1,3]]) (patternEdges [[1],[2,1,1,3]]) (patternAmount [[1],[2,1,1,3]]) (patternEdgeCount [[1],[2,1,1,3]]) [] := certificate_1447_checked

theorem certificate_1448_checked : certificate_1448.Valid 15 7 15 certificate_1448_q certificate_1448_edges 8 5 [] := by decide +kernel
theorem certificate_1448_valid : certificate_1448.Valid 15 7 (patternOrder [[1],[2,1,2,2]]) (patternClique [[1],[2,1,2,2]]) (patternEdges [[1],[2,1,2,2]]) (patternAmount [[1],[2,1,2,2]]) (patternEdgeCount [[1],[2,1,2,2]]) [] := certificate_1448_checked

theorem certificate_1449_checked : certificate_1449.Valid 15 7 15 certificate_1449_q certificate_1449_edges 8 4 [] := by decide +kernel
theorem certificate_1449_valid : certificate_1449.Valid 15 7 (patternOrder [[1],[2,2],[3]]) (patternClique [[1],[2,2],[3]]) (patternEdges [[1],[2,2],[3]]) (patternAmount [[1],[2,2],[3]]) (patternEdgeCount [[1],[2,2],[3]]) [] := certificate_1449_checked

theorem certificate_1450_checked : certificate_1450.Valid 15 7 12 certificate_1450_q certificate_1450_edges 5 5 [] := by decide +kernel
theorem certificate_1450_valid : certificate_1450.Valid 15 7 (patternOrder [[1,1],[1,1,1]]) (patternClique [[1,1],[1,1,1]]) (patternEdges [[1,1],[1,1,1]]) (patternAmount [[1,1],[1,1,1]]) (patternEdgeCount [[1,1],[1,1,1]]) [] := certificate_1450_checked

theorem certificate_1451_checked : certificate_1451.Valid 15 7 13 certificate_1451_q certificate_1451_edges 6 5 [] := by decide +kernel
theorem certificate_1451_valid : certificate_1451.Valid 15 7 (patternOrder [[1,1],[1,1,2]]) (patternClique [[1,1],[1,1,2]]) (patternEdges [[1,1],[1,1,2]]) (patternAmount [[1,1],[1,1,2]]) (patternEdgeCount [[1,1],[1,1,2]]) [] := certificate_1451_checked

theorem certificate_1452_checked : certificate_1452.Valid 15 7 14 certificate_1452_q certificate_1452_edges 7 5 [] := by decide +kernel
theorem certificate_1452_valid : certificate_1452.Valid 15 7 (patternOrder [[1,1],[1,1,3]]) (patternClique [[1,1],[1,1,3]]) (patternEdges [[1,1],[1,1,3]]) (patternAmount [[1,1],[1,1,3]]) (patternEdgeCount [[1,1],[1,1,3]]) [] := certificate_1452_checked

theorem certificate_1453_checked : certificate_1453.Valid 15 7 15 certificate_1453_q certificate_1453_edges 8 5 [] := by decide +kernel
theorem certificate_1453_valid : certificate_1453.Valid 15 7 (patternOrder [[1,1],[1,1,4]]) (patternClique [[1,1],[1,1,4]]) (patternEdges [[1,1],[1,1,4]]) (patternAmount [[1,1],[1,1,4]]) (patternEdgeCount [[1,1],[1,1,4]]) [] := certificate_1453_checked

theorem certificate_1454_checked : certificate_1454.Valid 15 7 13 certificate_1454_q certificate_1454_edges 6 5 [] := by decide +kernel
theorem certificate_1454_valid : certificate_1454.Valid 15 7 (patternOrder [[1,1],[1,2,1]]) (patternClique [[1,1],[1,2,1]]) (patternEdges [[1,1],[1,2,1]]) (patternAmount [[1,1],[1,2,1]]) (patternEdgeCount [[1,1],[1,2,1]]) [] := certificate_1454_checked

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

theorem patterns_15_7_18_verified_oai : ∀ D ∈ patterns_15_7_18, PatternVerified 15 7 D := by

  simp only [patterns_15_7_18, List.forall_mem_cons]

  exact ⟨⟨certificate_1439, certificate_1439_valid⟩, ⟨⟨certificate_1440, certificate_1440_valid⟩, ⟨⟨certificate_1441, certificate_1441_valid⟩, ⟨⟨certificate_1442, certificate_1442_valid⟩, ⟨⟨certificate_1443, certificate_1443_valid⟩, ⟨⟨certificate_1444, certificate_1444_valid⟩, ⟨⟨certificate_1445, certificate_1445_valid⟩, ⟨⟨certificate_1446, certificate_1446_valid⟩, ⟨⟨certificate_1447, certificate_1447_valid⟩, ⟨⟨certificate_1448, certificate_1448_valid⟩, ⟨⟨certificate_1449, certificate_1449_valid⟩, ⟨⟨certificate_1450, certificate_1450_valid⟩, ⟨⟨certificate_1451, certificate_1451_valid⟩, ⟨⟨certificate_1452, certificate_1452_valid⟩, ⟨⟨certificate_1453, certificate_1453_valid⟩, ⟨⟨certificate_1454, certificate_1454_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_18_verified_oai := @OAI.CycleClique.patterns_15_7_18_verified_oai
