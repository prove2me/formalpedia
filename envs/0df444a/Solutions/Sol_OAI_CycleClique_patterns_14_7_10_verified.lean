-- Prove2me | solution 1 for OAI.CycleClique.patterns_14_7_10_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:21:46.950896+00:00
-- url     : https://prove2.me/submissions/d1d92ae8-ceab-480f-b1a4-ba8979829949

import Mathlib
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates032
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_996_checked : certificate_996.Valid 14 7 14 certificate_996_q certificate_996_edges 7 4 [] := by decide +kernel
theorem certificate_996_valid : certificate_996.Valid 14 7 (patternOrder [[1],[1,1],[4]]) (patternClique [[1],[1,1],[4]]) (patternEdges [[1],[1,1],[4]]) (patternAmount [[1],[1,1],[4]]) (patternEdgeCount [[1],[1,1],[4]]) [] := certificate_996_checked

theorem certificate_997_checked : certificate_997.Valid 14 7 12 certificate_997_q certificate_997_edges 5 5 [] := by decide +kernel
theorem certificate_997_valid : certificate_997.Valid 14 7 (patternOrder [[1],[1,1,1,1]]) (patternClique [[1],[1,1,1,1]]) (patternEdges [[1],[1,1,1,1]]) (patternAmount [[1],[1,1,1,1]]) (patternEdgeCount [[1],[1,1,1,1]]) [] := certificate_997_checked

theorem certificate_998_checked : certificate_998.Valid 14 7 13 certificate_998_q certificate_998_edges 6 5 [] := by decide +kernel
theorem certificate_998_valid : certificate_998.Valid 14 7 (patternOrder [[1],[1,1,1,2]]) (patternClique [[1],[1,1,1,2]]) (patternEdges [[1],[1,1,1,2]]) (patternAmount [[1],[1,1,1,2]]) (patternEdgeCount [[1],[1,1,1,2]]) [] := certificate_998_checked

theorem certificate_999_checked : certificate_999.Valid 14 7 14 certificate_999_q certificate_999_edges 7 5 [] := by decide +kernel
theorem certificate_999_valid : certificate_999.Valid 14 7 (patternOrder [[1],[1,1,1,3]]) (patternClique [[1],[1,1,1,3]]) (patternEdges [[1],[1,1,1,3]]) (patternAmount [[1],[1,1,1,3]]) (patternEdgeCount [[1],[1,1,1,3]]) [] := certificate_999_checked

theorem certificate_1000_checked : certificate_1000.Valid 14 7 13 certificate_1000_q certificate_1000_edges 6 5 [] := by decide +kernel
theorem certificate_1000_valid : certificate_1000.Valid 14 7 (patternOrder [[1],[1,1,2,1]]) (patternClique [[1],[1,1,2,1]]) (patternEdges [[1],[1,1,2,1]]) (patternAmount [[1],[1,1,2,1]]) (patternEdgeCount [[1],[1,1,2,1]]) [] := certificate_1000_checked

theorem certificate_1001_checked : certificate_1001.Valid 14 7 14 certificate_1001_q certificate_1001_edges 7 5 [] := by decide +kernel
theorem certificate_1001_valid : certificate_1001.Valid 14 7 (patternOrder [[1],[1,1,2,2]]) (patternClique [[1],[1,1,2,2]]) (patternEdges [[1],[1,1,2,2]]) (patternAmount [[1],[1,1,2,2]]) (patternEdgeCount [[1],[1,1,2,2]]) [] := certificate_1001_checked

theorem certificate_1002_checked : certificate_1002.Valid 14 7 14 certificate_1002_q certificate_1002_edges 7 5 [] := by decide +kernel
theorem certificate_1002_valid : certificate_1002.Valid 14 7 (patternOrder [[1],[1,1,3,1]]) (patternClique [[1],[1,1,3,1]]) (patternEdges [[1],[1,1,3,1]]) (patternAmount [[1],[1,1,3,1]]) (patternEdgeCount [[1],[1,1,3,1]]) [] := certificate_1002_checked

theorem certificate_1003_checked : certificate_1003.Valid 14 7 13 certificate_1003_q certificate_1003_edges 6 4 [] := by decide +kernel
theorem certificate_1003_valid : certificate_1003.Valid 14 7 (patternOrder [[1],[1,2],[2]]) (patternClique [[1],[1,2],[2]]) (patternEdges [[1],[1,2],[2]]) (patternAmount [[1],[1,2],[2]]) (patternEdgeCount [[1],[1,2],[2]]) [] := certificate_1003_checked

theorem certificate_1004_checked : certificate_1004.Valid 14 7 14 certificate_1004_q certificate_1004_edges 7 4 [] := by decide +kernel
theorem certificate_1004_valid : certificate_1004.Valid 14 7 (patternOrder [[1],[1,2],[3]]) (patternClique [[1],[1,2],[3]]) (patternEdges [[1],[1,2],[3]]) (patternAmount [[1],[1,2],[3]]) (patternEdgeCount [[1],[1,2],[3]]) [] := certificate_1004_checked

theorem certificate_1005_checked : certificate_1005.Valid 14 7 14 certificate_1005_q certificate_1005_edges 7 5 [] := by decide +kernel
theorem certificate_1005_valid : certificate_1005.Valid 14 7 (patternOrder [[1],[1,2,1,2]]) (patternClique [[1],[1,2,1,2]]) (patternEdges [[1],[1,2,1,2]]) (patternAmount [[1],[1,2,1,2]]) (patternEdgeCount [[1],[1,2,1,2]]) [] := certificate_1005_checked

theorem certificate_1006_checked : certificate_1006.Valid 14 7 14 certificate_1006_q certificate_1006_edges 7 5 [] := by decide +kernel
theorem certificate_1006_valid : certificate_1006.Valid 14 7 (patternOrder [[1],[1,2,2,1]]) (patternClique [[1],[1,2,2,1]]) (patternEdges [[1],[1,2,2,1]]) (patternAmount [[1],[1,2,2,1]]) (patternEdgeCount [[1],[1,2,2,1]]) [] := certificate_1006_checked

theorem certificate_1007_checked : certificate_1007.Valid 14 7 14 certificate_1007_q certificate_1007_edges 7 4 [] := by decide +kernel
theorem certificate_1007_valid : certificate_1007.Valid 14 7 (patternOrder [[1],[1,3],[2]]) (patternClique [[1],[1,3],[2]]) (patternEdges [[1],[1,3],[2]]) (patternAmount [[1],[1,3],[2]]) (patternEdgeCount [[1],[1,3],[2]]) [] := certificate_1007_checked

theorem certificate_1008_checked : certificate_1008.Valid 14 7 14 certificate_1008_q certificate_1008_edges 7 4 [] := by decide +kernel
theorem certificate_1008_valid : certificate_1008.Valid 14 7 (patternOrder [[1],[2],[2,2]]) (patternClique [[1],[2],[2,2]]) (patternEdges [[1],[2],[2,2]]) (patternAmount [[1],[2],[2,2]]) (patternEdgeCount [[1],[2],[2,2]]) [] := certificate_1008_checked

theorem certificate_1009_checked : certificate_1009.Valid 14 7 14 certificate_1009_q certificate_1009_edges 7 5 [] := by decide +kernel
theorem certificate_1009_valid : certificate_1009.Valid 14 7 (patternOrder [[1],[2,1,1,2]]) (patternClique [[1],[2,1,1,2]]) (patternEdges [[1],[2,1,1,2]]) (patternAmount [[1],[2,1,1,2]]) (patternEdgeCount [[1],[2,1,1,2]]) [] := certificate_1009_checked

theorem certificate_1010_checked : certificate_1010.Valid 14 7 12 certificate_1010_q certificate_1010_edges 5 5 [] := by decide +kernel
theorem certificate_1010_valid : certificate_1010.Valid 14 7 (patternOrder [[1,1],[1,1,1]]) (patternClique [[1,1],[1,1,1]]) (patternEdges [[1,1],[1,1,1]]) (patternAmount [[1,1],[1,1,1]]) (patternEdgeCount [[1,1],[1,1,1]]) [] := certificate_1010_checked

theorem certificate_1011_checked : certificate_1011.Valid 14 7 13 certificate_1011_q certificate_1011_edges 6 5 [] := by decide +kernel
theorem certificate_1011_valid : certificate_1011.Valid 14 7 (patternOrder [[1,1],[1,1,2]]) (patternClique [[1,1],[1,1,2]]) (patternEdges [[1,1],[1,1,2]]) (patternAmount [[1,1],[1,1,2]]) (patternEdgeCount [[1,1],[1,1,2]]) [] := certificate_1011_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns14x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_14_7_10_verified_oai : ∀ D ∈ patterns_14_7_10, PatternVerified 14 7 D := by

  simp only [patterns_14_7_10, List.forall_mem_cons]

  exact ⟨⟨certificate_996, certificate_996_valid⟩, ⟨⟨certificate_997, certificate_997_valid⟩, ⟨⟨certificate_998, certificate_998_valid⟩, ⟨⟨certificate_999, certificate_999_valid⟩, ⟨⟨certificate_1000, certificate_1000_valid⟩, ⟨⟨certificate_1001, certificate_1001_valid⟩, ⟨⟨certificate_1002, certificate_1002_valid⟩, ⟨⟨certificate_1003, certificate_1003_valid⟩, ⟨⟨certificate_1004, certificate_1004_valid⟩, ⟨⟨certificate_1005, certificate_1005_valid⟩, ⟨⟨certificate_1006, certificate_1006_valid⟩, ⟨⟨certificate_1007, certificate_1007_valid⟩, ⟨⟨certificate_1008, certificate_1008_valid⟩, ⟨⟨certificate_1009, certificate_1009_valid⟩, ⟨⟨certificate_1010, certificate_1010_valid⟩, ⟨⟨certificate_1011, certificate_1011_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_14_7_10_verified_oai := @OAI.CycleClique.patterns_14_7_10_verified_oai
