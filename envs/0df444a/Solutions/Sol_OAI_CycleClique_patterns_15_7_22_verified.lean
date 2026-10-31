-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_22_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:52:38.78262+00:00
-- url     : https://prove2.me/submissions/d5fa356b-2f32-4aab-b03f-0cbb2ac72702

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

theorem certificate_1503_checked : certificate_1503.Valid 15 7 15 certificate_1503_q certificate_1503_edges 8 4 [] := by decide +kernel
theorem certificate_1503_valid : certificate_1503.Valid 15 7 (patternOrder [[1,2],[2],[3]]) (patternClique [[1,2],[2],[3]]) (patternEdges [[1,2],[2],[3]]) (patternAmount [[1,2],[2],[3]]) (patternEdgeCount [[1,2],[2],[3]]) [] := certificate_1503_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates048
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1504_checked : certificate_1504.Valid 15 7 15 certificate_1504_q certificate_1504_edges 8 5 [] := by decide +kernel
theorem certificate_1504_valid : certificate_1504.Valid 15 7 (patternOrder [[1,2],[2,1,2]]) (patternClique [[1,2],[2,1,2]]) (patternEdges [[1,2],[2,1,2]]) (patternAmount [[1,2],[2,1,2]]) (patternEdgeCount [[1,2],[2,1,2]]) [] := certificate_1504_checked

theorem certificate_1505_checked : certificate_1505.Valid 15 7 15 certificate_1505_q certificate_1505_edges 8 5 [] := by decide +kernel
theorem certificate_1505_valid : certificate_1505.Valid 15 7 (patternOrder [[1,2,1],[1,3]]) (patternClique [[1,2,1],[1,3]]) (patternEdges [[1,2,1],[1,3]]) (patternAmount [[1,2,1],[1,3]]) (patternEdgeCount [[1,2,1],[1,3]]) [] := certificate_1505_checked

theorem certificate_1506_checked : certificate_1506.Valid 15 7 15 certificate_1506_q certificate_1506_edges 8 5 [] := by decide +kernel
theorem certificate_1506_valid : certificate_1506.Valid 15 7 (patternOrder [[1,2,1],[2,2]]) (patternClique [[1,2,1],[2,2]]) (patternEdges [[1,2,1],[2,2]]) (patternAmount [[1,2,1],[2,2]]) (patternEdgeCount [[1,2,1],[2,2]]) [] := certificate_1506_checked

theorem certificate_1507_checked : certificate_1507.Valid 15 7 15 certificate_1507_q certificate_1507_edges 8 6 [] := by decide +kernel
theorem certificate_1507_valid : certificate_1507.Valid 15 7 (patternOrder [[1,2,1,1,1,2]]) (patternClique [[1,2,1,1,1,2]]) (patternEdges [[1,2,1,1,1,2]]) (patternAmount [[1,2,1,1,1,2]]) (patternEdgeCount [[1,2,1,1,1,2]]) [] := certificate_1507_checked

theorem certificate_1508_checked : certificate_1508.Valid 15 7 15 certificate_1508_q certificate_1508_edges 8 6 [] := by decide +kernel
theorem certificate_1508_valid : certificate_1508.Valid 15 7 (patternOrder [[1,2,1,1,2,1]]) (patternClique [[1,2,1,1,2,1]]) (patternEdges [[1,2,1,1,2,1]]) (patternAmount [[1,2,1,1,2,1]]) (patternEdgeCount [[1,2,1,1,2,1]]) [] := certificate_1508_checked

theorem certificate_1509_checked : certificate_1509.Valid 15 7 15 certificate_1509_q certificate_1509_edges 8 5 [] := by decide +kernel
theorem certificate_1509_valid : certificate_1509.Valid 15 7 (patternOrder [[1,2,1,2],[2]]) (patternClique [[1,2,1,2],[2]]) (patternEdges [[1,2,1,2],[2]]) (patternAmount [[1,2,1,2],[2]]) (patternEdgeCount [[1,2,1,2],[2]]) [] := certificate_1509_checked

theorem certificate_1510_checked : certificate_1510.Valid 15 7 15 certificate_1510_q certificate_1510_edges 8 5 [] := by decide +kernel
theorem certificate_1510_valid : certificate_1510.Valid 15 7 (patternOrder [[1,2,2,1],[2]]) (patternClique [[1,2,2,1],[2]]) (patternEdges [[1,2,2,1],[2]]) (patternAmount [[1,2,2,1],[2]]) (patternEdgeCount [[1,2,2,1],[2]]) [] := certificate_1510_checked

theorem certificate_1511_checked : certificate_1511.Valid 15 7 15 certificate_1511_q certificate_1511_edges 8 4 [] := by decide +kernel
theorem certificate_1511_valid : certificate_1511.Valid 15 7 (patternOrder [[1,3],[2],[2]]) (patternClique [[1,3],[2],[2]]) (patternEdges [[1,3],[2],[2]]) (patternAmount [[1,3],[2],[2]]) (patternEdgeCount [[1,3],[2],[2]]) [] := certificate_1511_checked

theorem certificate_1512_checked : certificate_1512.Valid 15 7 15 certificate_1512_q certificate_1512_edges 8 4 [] := by decide +kernel
theorem certificate_1512_valid : certificate_1512.Valid 15 7 (patternOrder [[2],[2],[2,2]]) (patternClique [[2],[2],[2,2]]) (patternEdges [[2],[2],[2,2]]) (patternAmount [[2],[2],[2,2]]) (patternEdgeCount [[2],[2],[2,2]]) [] := certificate_1512_checked

theorem certificate_1513_checked : certificate_1513.Valid 15 7 15 certificate_1513_q certificate_1513_edges 8 5 [] := by decide +kernel
theorem certificate_1513_valid : certificate_1513.Valid 15 7 (patternOrder [[2],[2,1,1,2]]) (patternClique [[2],[2,1,1,2]]) (patternEdges [[2],[2,1,1,2]]) (patternAmount [[2],[2,1,1,2]]) (patternEdgeCount [[2],[2,1,1,2]]) [] := certificate_1513_checked

theorem certificate_1514_checked : certificate_1514.Valid 15 7 15 certificate_1514_q certificate_1514_edges 8 6 [] := by decide +kernel
theorem certificate_1514_valid : certificate_1514.Valid 15 7 (patternOrder [[2,1,1,1,1,2]]) (patternClique [[2,1,1,1,1,2]]) (patternEdges [[2,1,1,1,1,2]]) (patternAmount [[2,1,1,1,1,2]]) (patternEdgeCount [[2,1,1,1,1,2]]) [] := certificate_1514_checked

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

theorem patterns_15_7_22_verified_oai : ∀ D ∈ patterns_15_7_22, PatternVerified 15 7 D := by

  simp only [patterns_15_7_22, List.forall_mem_cons]

  exact ⟨⟨certificate_1503, certificate_1503_valid⟩, ⟨⟨certificate_1504, certificate_1504_valid⟩, ⟨⟨certificate_1505, certificate_1505_valid⟩, ⟨⟨certificate_1506, certificate_1506_valid⟩, ⟨⟨certificate_1507, certificate_1507_valid⟩, ⟨⟨certificate_1508, certificate_1508_valid⟩, ⟨⟨certificate_1509, certificate_1509_valid⟩, ⟨⟨certificate_1510, certificate_1510_valid⟩, ⟨⟨certificate_1511, certificate_1511_valid⟩, ⟨⟨certificate_1512, certificate_1512_valid⟩, ⟨⟨certificate_1513, certificate_1513_valid⟩, ⟨⟨certificate_1514, certificate_1514_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_22_verified_oai := @OAI.CycleClique.patterns_15_7_22_verified_oai
