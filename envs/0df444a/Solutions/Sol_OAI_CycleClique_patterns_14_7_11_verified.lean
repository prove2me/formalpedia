-- Prove2me | solution 1 for OAI.CycleClique.patterns_14_7_11_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:19:12.279005+00:00
-- url     : https://prove2.me/submissions/1dec164b-4093-44f9-80e9-fc8dac08a10b

import Mathlib
import Definitions.Def_OAIQ107D008
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

theorem certificate_1012_checked : certificate_1012.Valid 14 7 14 certificate_1012_q certificate_1012_edges 7 5 [] := by decide +kernel
theorem certificate_1012_valid : certificate_1012.Valid 14 7 (patternOrder [[1,1],[1,1,3]]) (patternClique [[1,1],[1,1,3]]) (patternEdges [[1,1],[1,1,3]]) (patternAmount [[1,1],[1,1,3]]) (patternEdgeCount [[1,1],[1,1,3]]) [] := certificate_1012_checked

theorem certificate_1013_checked : certificate_1013.Valid 14 7 13 certificate_1013_q certificate_1013_edges 6 5 [] := by decide +kernel
theorem certificate_1013_valid : certificate_1013.Valid 14 7 (patternOrder [[1,1],[1,2,1]]) (patternClique [[1,1],[1,2,1]]) (patternEdges [[1,1],[1,2,1]]) (patternAmount [[1,1],[1,2,1]]) (patternEdgeCount [[1,1],[1,2,1]]) [] := certificate_1013_checked

theorem certificate_1014_checked : certificate_1014.Valid 14 7 14 certificate_1014_q certificate_1014_edges 7 5 [] := by decide +kernel
theorem certificate_1014_valid : certificate_1014.Valid 14 7 (patternOrder [[1,1],[1,2,2]]) (patternClique [[1,1],[1,2,2]]) (patternEdges [[1,1],[1,2,2]]) (patternAmount [[1,1],[1,2,2]]) (patternEdgeCount [[1,1],[1,2,2]]) [] := certificate_1014_checked

theorem certificate_1015_checked : certificate_1015.Valid 14 7 14 certificate_1015_q certificate_1015_edges 7 5 [] := by decide +kernel
theorem certificate_1015_valid : certificate_1015.Valid 14 7 (patternOrder [[1,1],[1,3,1]]) (patternClique [[1,1],[1,3,1]]) (patternEdges [[1,1],[1,3,1]]) (patternAmount [[1,1],[1,3,1]]) (patternEdgeCount [[1,1],[1,3,1]]) [] := certificate_1015_checked

theorem certificate_1016_checked : certificate_1016.Valid 14 7 13 certificate_1016_q certificate_1016_edges 6 4 [] := by decide +kernel
theorem certificate_1016_valid : certificate_1016.Valid 14 7 (patternOrder [[1,1],[2],[2]]) (patternClique [[1,1],[2],[2]]) (patternEdges [[1,1],[2],[2]]) (patternAmount [[1,1],[2],[2]]) (patternEdgeCount [[1,1],[2],[2]]) [] := certificate_1016_checked

theorem certificate_1017_checked : certificate_1017.Valid 14 7 14 certificate_1017_q certificate_1017_edges 7 4 [] := by decide +kernel
theorem certificate_1017_valid : certificate_1017.Valid 14 7 (patternOrder [[1,1],[2],[3]]) (patternClique [[1,1],[2],[3]]) (patternEdges [[1,1],[2],[3]]) (patternAmount [[1,1],[2],[3]]) (patternEdgeCount [[1,1],[2],[3]]) [] := certificate_1017_checked

theorem certificate_1018_checked : certificate_1018.Valid 14 7 14 certificate_1018_q certificate_1018_edges 7 5 [] := by decide +kernel
theorem certificate_1018_valid : certificate_1018.Valid 14 7 (patternOrder [[1,1],[2,1,2]]) (patternClique [[1,1],[2,1,2]]) (patternEdges [[1,1],[2,1,2]]) (patternAmount [[1,1],[2,1,2]]) (patternEdgeCount [[1,1],[2,1,2]]) [] := certificate_1018_checked

theorem certificate_1019_checked : certificate_1019.Valid 14 7 13 certificate_1019_q certificate_1019_edges 6 5 [] := by decide +kernel
theorem certificate_1019_valid : certificate_1019.Valid 14 7 (patternOrder [[1,1,1],[1,2]]) (patternClique [[1,1,1],[1,2]]) (patternEdges [[1,1,1],[1,2]]) (patternAmount [[1,1,1],[1,2]]) (patternEdgeCount [[1,1,1],[1,2]]) [] := certificate_1019_checked

theorem certificate_1020_checked : certificate_1020.Valid 14 7 14 certificate_1020_q certificate_1020_edges 7 5 [] := by decide +kernel
theorem certificate_1020_valid : certificate_1020.Valid 14 7 (patternOrder [[1,1,1],[1,3]]) (patternClique [[1,1,1],[1,3]]) (patternEdges [[1,1,1],[1,3]]) (patternAmount [[1,1,1],[1,3]]) (patternEdgeCount [[1,1,1],[1,3]]) [] := certificate_1020_checked

theorem certificate_1021_checked : certificate_1021.Valid 14 7 14 certificate_1021_q certificate_1021_edges 7 5 [] := by decide +kernel
theorem certificate_1021_valid : certificate_1021.Valid 14 7 (patternOrder [[1,1,1],[2,2]]) (patternClique [[1,1,1],[2,2]]) (patternEdges [[1,1,1],[2,2]]) (patternAmount [[1,1,1],[2,2]]) (patternEdgeCount [[1,1,1],[2,2]]) [] := certificate_1021_checked

theorem certificate_1022_checked : certificate_1022.Valid 14 7 13 certificate_1022_q certificate_1022_edges 6 5 [] := by decide +kernel
theorem certificate_1022_valid : certificate_1022.Valid 14 7 (patternOrder [[1,1,1,1],[2]]) (patternClique [[1,1,1,1],[2]]) (patternEdges [[1,1,1,1],[2]]) (patternAmount [[1,1,1,1],[2]]) (patternEdgeCount [[1,1,1,1],[2]]) [] := certificate_1022_checked

theorem certificate_1023_checked : certificate_1023.Valid 14 7 14 certificate_1023_q certificate_1023_edges 7 5 [] := by decide +kernel
theorem certificate_1023_valid : certificate_1023.Valid 14 7 (patternOrder [[1,1,1,1],[3]]) (patternClique [[1,1,1,1],[3]]) (patternEdges [[1,1,1,1],[3]]) (patternAmount [[1,1,1,1],[3]]) (patternEdgeCount [[1,1,1,1],[3]]) [] := certificate_1023_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates033
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1024_checked : certificate_1024.Valid 14 7 13 certificate_1024_q certificate_1024_edges 6 6 [] := by decide +kernel
theorem certificate_1024_valid : certificate_1024.Valid 14 7 (patternOrder [[1,1,1,1,1,1]]) (patternClique [[1,1,1,1,1,1]]) (patternEdges [[1,1,1,1,1,1]]) (patternAmount [[1,1,1,1,1,1]]) (patternEdgeCount [[1,1,1,1,1,1]]) [] := certificate_1024_checked

theorem certificate_1025_checked : certificate_1025.Valid 14 7 14 certificate_1025_q certificate_1025_edges 7 6 [] := by decide +kernel
theorem certificate_1025_valid : certificate_1025.Valid 14 7 (patternOrder [[1,1,1,1,1,2]]) (patternClique [[1,1,1,1,1,2]]) (patternEdges [[1,1,1,1,1,2]]) (patternAmount [[1,1,1,1,1,2]]) (patternEdgeCount [[1,1,1,1,1,2]]) [] := certificate_1025_checked

theorem certificate_1026_checked : certificate_1026.Valid 14 7 14 certificate_1026_q certificate_1026_edges 7 6 [] := by decide +kernel
theorem certificate_1026_valid : certificate_1026.Valid 14 7 (patternOrder [[1,1,1,1,2,1]]) (patternClique [[1,1,1,1,2,1]]) (patternEdges [[1,1,1,1,2,1]]) (patternAmount [[1,1,1,1,2,1]]) (patternEdgeCount [[1,1,1,1,2,1]]) [] := certificate_1026_checked

theorem certificate_1027_checked : certificate_1027.Valid 14 7 14 certificate_1027_q certificate_1027_edges 7 5 [] := by decide +kernel
theorem certificate_1027_valid : certificate_1027.Valid 14 7 (patternOrder [[1,1,1,2],[2]]) (patternClique [[1,1,1,2],[2]]) (patternEdges [[1,1,1,2],[2]]) (patternAmount [[1,1,1,2],[2]]) (patternEdgeCount [[1,1,1,2],[2]]) [] := certificate_1027_checked

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

theorem patterns_14_7_11_verified_oai : ∀ D ∈ patterns_14_7_11, PatternVerified 14 7 D := by

  simp only [patterns_14_7_11, List.forall_mem_cons]

  exact ⟨⟨certificate_1012, certificate_1012_valid⟩, ⟨⟨certificate_1013, certificate_1013_valid⟩, ⟨⟨certificate_1014, certificate_1014_valid⟩, ⟨⟨certificate_1015, certificate_1015_valid⟩, ⟨⟨certificate_1016, certificate_1016_valid⟩, ⟨⟨certificate_1017, certificate_1017_valid⟩, ⟨⟨certificate_1018, certificate_1018_valid⟩, ⟨⟨certificate_1019, certificate_1019_valid⟩, ⟨⟨certificate_1020, certificate_1020_valid⟩, ⟨⟨certificate_1021, certificate_1021_valid⟩, ⟨⟨certificate_1022, certificate_1022_valid⟩, ⟨⟨certificate_1023, certificate_1023_valid⟩, ⟨⟨certificate_1024, certificate_1024_valid⟩, ⟨⟨certificate_1025, certificate_1025_valid⟩, ⟨⟨certificate_1026, certificate_1026_valid⟩, ⟨⟨certificate_1027, certificate_1027_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_14_7_11_verified_oai := @OAI.CycleClique.patterns_14_7_11_verified_oai
