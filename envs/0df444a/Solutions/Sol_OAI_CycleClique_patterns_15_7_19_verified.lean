-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_19_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:47:06.172453+00:00
-- url     : https://prove2.me/submissions/6611ac3f-b023-4ed0-9689-9003881f6424

import Mathlib
import Definitions.Def_OAIQ107D128
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates046
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1455_checked : certificate_1455.Valid 15 7 14 certificate_1455_q certificate_1455_edges 7 5 [] := by decide +kernel
theorem certificate_1455_valid : certificate_1455.Valid 15 7 (patternOrder [[1,1],[1,2,2]]) (patternClique [[1,1],[1,2,2]]) (patternEdges [[1,1],[1,2,2]]) (patternAmount [[1,1],[1,2,2]]) (patternEdgeCount [[1,1],[1,2,2]]) [] := certificate_1455_checked

theorem certificate_1456_checked : certificate_1456.Valid 15 7 15 certificate_1456_q certificate_1456_edges 8 5 [] := by decide +kernel
theorem certificate_1456_valid : certificate_1456.Valid 15 7 (patternOrder [[1,1],[1,2,3]]) (patternClique [[1,1],[1,2,3]]) (patternEdges [[1,1],[1,2,3]]) (patternAmount [[1,1],[1,2,3]]) (patternEdgeCount [[1,1],[1,2,3]]) [] := certificate_1456_checked

theorem certificate_1457_checked : certificate_1457.Valid 15 7 14 certificate_1457_q certificate_1457_edges 7 5 [] := by decide +kernel
theorem certificate_1457_valid : certificate_1457.Valid 15 7 (patternOrder [[1,1],[1,3,1]]) (patternClique [[1,1],[1,3,1]]) (patternEdges [[1,1],[1,3,1]]) (patternAmount [[1,1],[1,3,1]]) (patternEdgeCount [[1,1],[1,3,1]]) [] := certificate_1457_checked

theorem certificate_1458_checked : certificate_1458.Valid 15 7 15 certificate_1458_q certificate_1458_edges 8 5 [] := by decide +kernel
theorem certificate_1458_valid : certificate_1458.Valid 15 7 (patternOrder [[1,1],[1,3,2]]) (patternClique [[1,1],[1,3,2]]) (patternEdges [[1,1],[1,3,2]]) (patternAmount [[1,1],[1,3,2]]) (patternEdgeCount [[1,1],[1,3,2]]) [] := certificate_1458_checked

theorem certificate_1459_checked : certificate_1459.Valid 15 7 15 certificate_1459_q certificate_1459_edges 8 5 [] := by decide +kernel
theorem certificate_1459_valid : certificate_1459.Valid 15 7 (patternOrder [[1,1],[1,4,1]]) (patternClique [[1,1],[1,4,1]]) (patternEdges [[1,1],[1,4,1]]) (patternAmount [[1,1],[1,4,1]]) (patternEdgeCount [[1,1],[1,4,1]]) [] := certificate_1459_checked

theorem certificate_1460_checked : certificate_1460.Valid 15 7 13 certificate_1460_q certificate_1460_edges 6 4 [] := by decide +kernel
theorem certificate_1460_valid : certificate_1460.Valid 15 7 (patternOrder [[1,1],[2],[2]]) (patternClique [[1,1],[2],[2]]) (patternEdges [[1,1],[2],[2]]) (patternAmount [[1,1],[2],[2]]) (patternEdgeCount [[1,1],[2],[2]]) [] := certificate_1460_checked

theorem certificate_1461_checked : certificate_1461.Valid 15 7 14 certificate_1461_q certificate_1461_edges 7 4 [] := by decide +kernel
theorem certificate_1461_valid : certificate_1461.Valid 15 7 (patternOrder [[1,1],[2],[3]]) (patternClique [[1,1],[2],[3]]) (patternEdges [[1,1],[2],[3]]) (patternAmount [[1,1],[2],[3]]) (patternEdgeCount [[1,1],[2],[3]]) [] := certificate_1461_checked

theorem certificate_1462_checked : certificate_1462.Valid 15 7 15 certificate_1462_q certificate_1462_edges 8 4 [] := by decide +kernel
theorem certificate_1462_valid : certificate_1462.Valid 15 7 (patternOrder [[1,1],[2],[4]]) (patternClique [[1,1],[2],[4]]) (patternEdges [[1,1],[2],[4]]) (patternAmount [[1,1],[2],[4]]) (patternEdgeCount [[1,1],[2],[4]]) [] := certificate_1462_checked

theorem certificate_1463_checked : certificate_1463.Valid 15 7 14 certificate_1463_q certificate_1463_edges 7 5 [] := by decide +kernel
theorem certificate_1463_valid : certificate_1463.Valid 15 7 (patternOrder [[1,1],[2,1,2]]) (patternClique [[1,1],[2,1,2]]) (patternEdges [[1,1],[2,1,2]]) (patternAmount [[1,1],[2,1,2]]) (patternEdgeCount [[1,1],[2,1,2]]) [] := certificate_1463_checked

theorem certificate_1464_checked : certificate_1464.Valid 15 7 15 certificate_1464_q certificate_1464_edges 8 5 [] := by decide +kernel
theorem certificate_1464_valid : certificate_1464.Valid 15 7 (patternOrder [[1,1],[2,1,3]]) (patternClique [[1,1],[2,1,3]]) (patternEdges [[1,1],[2,1,3]]) (patternAmount [[1,1],[2,1,3]]) (patternEdgeCount [[1,1],[2,1,3]]) [] := certificate_1464_checked

theorem certificate_1465_checked : certificate_1465.Valid 15 7 15 certificate_1465_q certificate_1465_edges 8 5 [] := by decide +kernel
theorem certificate_1465_valid : certificate_1465.Valid 15 7 (patternOrder [[1,1],[2,2,2]]) (patternClique [[1,1],[2,2,2]]) (patternEdges [[1,1],[2,2,2]]) (patternAmount [[1,1],[2,2,2]]) (patternEdgeCount [[1,1],[2,2,2]]) [] := certificate_1465_checked

theorem certificate_1466_checked : certificate_1466.Valid 15 7 15 certificate_1466_q certificate_1466_edges 8 4 [] := by decide +kernel
theorem certificate_1466_valid : certificate_1466.Valid 15 7 (patternOrder [[1,1],[3],[3]]) (patternClique [[1,1],[3],[3]]) (patternEdges [[1,1],[3],[3]]) (patternAmount [[1,1],[3],[3]]) (patternEdgeCount [[1,1],[3],[3]]) [] := certificate_1466_checked

theorem certificate_1467_checked : certificate_1467.Valid 15 7 13 certificate_1467_q certificate_1467_edges 6 5 [] := by decide +kernel
theorem certificate_1467_valid : certificate_1467.Valid 15 7 (patternOrder [[1,1,1],[1,2]]) (patternClique [[1,1,1],[1,2]]) (patternEdges [[1,1,1],[1,2]]) (patternAmount [[1,1,1],[1,2]]) (patternEdgeCount [[1,1,1],[1,2]]) [] := certificate_1467_checked

theorem certificate_1468_checked : certificate_1468.Valid 15 7 14 certificate_1468_q certificate_1468_edges 7 5 [] := by decide +kernel
theorem certificate_1468_valid : certificate_1468.Valid 15 7 (patternOrder [[1,1,1],[1,3]]) (patternClique [[1,1,1],[1,3]]) (patternEdges [[1,1,1],[1,3]]) (patternAmount [[1,1,1],[1,3]]) (patternEdgeCount [[1,1,1],[1,3]]) [] := certificate_1468_checked

theorem certificate_1469_checked : certificate_1469.Valid 15 7 15 certificate_1469_q certificate_1469_edges 8 5 [] := by decide +kernel
theorem certificate_1469_valid : certificate_1469.Valid 15 7 (patternOrder [[1,1,1],[1,4]]) (patternClique [[1,1,1],[1,4]]) (patternEdges [[1,1,1],[1,4]]) (patternAmount [[1,1,1],[1,4]]) (patternEdgeCount [[1,1,1],[1,4]]) [] := certificate_1469_checked

theorem certificate_1470_checked : certificate_1470.Valid 15 7 14 certificate_1470_q certificate_1470_edges 7 5 [] := by decide +kernel
theorem certificate_1470_valid : certificate_1470.Valid 15 7 (patternOrder [[1,1,1],[2,2]]) (patternClique [[1,1,1],[2,2]]) (patternEdges [[1,1,1],[2,2]]) (patternAmount [[1,1,1],[2,2]]) (patternEdgeCount [[1,1,1],[2,2]]) [] := certificate_1470_checked

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

theorem patterns_15_7_19_verified_oai : ∀ D ∈ patterns_15_7_19, PatternVerified 15 7 D := by

  simp only [patterns_15_7_19, List.forall_mem_cons]

  exact ⟨⟨certificate_1455, certificate_1455_valid⟩, ⟨⟨certificate_1456, certificate_1456_valid⟩, ⟨⟨certificate_1457, certificate_1457_valid⟩, ⟨⟨certificate_1458, certificate_1458_valid⟩, ⟨⟨certificate_1459, certificate_1459_valid⟩, ⟨⟨certificate_1460, certificate_1460_valid⟩, ⟨⟨certificate_1461, certificate_1461_valid⟩, ⟨⟨certificate_1462, certificate_1462_valid⟩, ⟨⟨certificate_1463, certificate_1463_valid⟩, ⟨⟨certificate_1464, certificate_1464_valid⟩, ⟨⟨certificate_1465, certificate_1465_valid⟩, ⟨⟨certificate_1466, certificate_1466_valid⟩, ⟨⟨certificate_1467, certificate_1467_valid⟩, ⟨⟨certificate_1468, certificate_1468_valid⟩, ⟨⟨certificate_1469, certificate_1469_valid⟩, ⟨⟨certificate_1470, certificate_1470_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_19_verified_oai := @OAI.CycleClique.patterns_15_7_19_verified_oai
