-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_49_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:54:43.819994+00:00
-- url     : https://prove2.me/submissions/1bda3e91-8c0c-42f5-b9f0-72d6530cdf54

import Mathlib
import Definitions.Def_OAIQ107D132
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates094
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_3004_checked : certificate_3004.Valid 17 8 17 certificate_3004_q certificate_3004_edges 9 6 [] := by decide +kernel
theorem certificate_3004_valid : certificate_3004.Valid 17 8 (patternOrder [[1,1,1],[1,1,4]]) (patternClique [[1,1,1],[1,1,4]]) (patternEdges [[1,1,1],[1,1,4]]) (patternAmount [[1,1,1],[1,1,4]]) (patternEdgeCount [[1,1,1],[1,1,4]]) [] := certificate_3004_checked

theorem certificate_3005_checked : certificate_3005.Valid 17 8 15 certificate_3005_q certificate_3005_edges 7 6 [] := by decide +kernel
theorem certificate_3005_valid : certificate_3005.Valid 17 8 (patternOrder [[1,1,1],[1,2,1]]) (patternClique [[1,1,1],[1,2,1]]) (patternEdges [[1,1,1],[1,2,1]]) (patternAmount [[1,1,1],[1,2,1]]) (patternEdgeCount [[1,1,1],[1,2,1]]) [] := certificate_3005_checked

theorem certificate_3006_checked : certificate_3006.Valid 17 8 16 certificate_3006_q certificate_3006_edges 8 6 [] := by decide +kernel
theorem certificate_3006_valid : certificate_3006.Valid 17 8 (patternOrder [[1,1,1],[1,2,2]]) (patternClique [[1,1,1],[1,2,2]]) (patternEdges [[1,1,1],[1,2,2]]) (patternAmount [[1,1,1],[1,2,2]]) (patternEdgeCount [[1,1,1],[1,2,2]]) [] := certificate_3006_checked

theorem certificate_3007_checked : certificate_3007.Valid 17 8 17 certificate_3007_q certificate_3007_edges 9 6 [] := by decide +kernel
theorem certificate_3007_valid : certificate_3007.Valid 17 8 (patternOrder [[1,1,1],[1,2,3]]) (patternClique [[1,1,1],[1,2,3]]) (patternEdges [[1,1,1],[1,2,3]]) (patternAmount [[1,1,1],[1,2,3]]) (patternEdgeCount [[1,1,1],[1,2,3]]) [] := certificate_3007_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates095
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_3008_checked : certificate_3008.Valid 17 8 16 certificate_3008_q certificate_3008_edges 8 6 [] := by decide +kernel
theorem certificate_3008_valid : certificate_3008.Valid 17 8 (patternOrder [[1,1,1],[1,3,1]]) (patternClique [[1,1,1],[1,3,1]]) (patternEdges [[1,1,1],[1,3,1]]) (patternAmount [[1,1,1],[1,3,1]]) (patternEdgeCount [[1,1,1],[1,3,1]]) [] := certificate_3008_checked

theorem certificate_3009_checked : certificate_3009.Valid 17 8 17 certificate_3009_q certificate_3009_edges 9 6 [] := by decide +kernel
theorem certificate_3009_valid : certificate_3009.Valid 17 8 (patternOrder [[1,1,1],[1,3,2]]) (patternClique [[1,1,1],[1,3,2]]) (patternEdges [[1,1,1],[1,3,2]]) (patternAmount [[1,1,1],[1,3,2]]) (patternEdgeCount [[1,1,1],[1,3,2]]) [] := certificate_3009_checked

theorem certificate_3010_checked : certificate_3010.Valid 17 8 17 certificate_3010_q certificate_3010_edges 9 6 [] := by decide +kernel
theorem certificate_3010_valid : certificate_3010.Valid 17 8 (patternOrder [[1,1,1],[1,4,1]]) (patternClique [[1,1,1],[1,4,1]]) (patternEdges [[1,1,1],[1,4,1]]) (patternAmount [[1,1,1],[1,4,1]]) (patternEdgeCount [[1,1,1],[1,4,1]]) [] := certificate_3010_checked

theorem certificate_3011_checked : certificate_3011.Valid 17 8 15 certificate_3011_q certificate_3011_edges 7 5 [] := by decide +kernel
theorem certificate_3011_valid : certificate_3011.Valid 17 8 (patternOrder [[1,1,1],[2],[2]]) (patternClique [[1,1,1],[2],[2]]) (patternEdges [[1,1,1],[2],[2]]) (patternAmount [[1,1,1],[2],[2]]) (patternEdgeCount [[1,1,1],[2],[2]]) [] := certificate_3011_checked

theorem certificate_3012_checked : certificate_3012.Valid 17 8 16 certificate_3012_q certificate_3012_edges 8 5 [] := by decide +kernel
theorem certificate_3012_valid : certificate_3012.Valid 17 8 (patternOrder [[1,1,1],[2],[3]]) (patternClique [[1,1,1],[2],[3]]) (patternEdges [[1,1,1],[2],[3]]) (patternAmount [[1,1,1],[2],[3]]) (patternEdgeCount [[1,1,1],[2],[3]]) [] := certificate_3012_checked

theorem certificate_3013_checked : certificate_3013.Valid 17 8 17 certificate_3013_q certificate_3013_edges 9 5 [] := by decide +kernel
theorem certificate_3013_valid : certificate_3013.Valid 17 8 (patternOrder [[1,1,1],[2],[4]]) (patternClique [[1,1,1],[2],[4]]) (patternEdges [[1,1,1],[2],[4]]) (patternAmount [[1,1,1],[2],[4]]) (patternEdgeCount [[1,1,1],[2],[4]]) [] := certificate_3013_checked

theorem certificate_3014_checked : certificate_3014.Valid 17 8 16 certificate_3014_q certificate_3014_edges 8 6 [] := by decide +kernel
theorem certificate_3014_valid : certificate_3014.Valid 17 8 (patternOrder [[1,1,1],[2,1,2]]) (patternClique [[1,1,1],[2,1,2]]) (patternEdges [[1,1,1],[2,1,2]]) (patternAmount [[1,1,1],[2,1,2]]) (patternEdgeCount [[1,1,1],[2,1,2]]) [] := certificate_3014_checked

theorem certificate_3015_checked : certificate_3015.Valid 17 8 17 certificate_3015_q certificate_3015_edges 9 6 [] := by decide +kernel
theorem certificate_3015_valid : certificate_3015.Valid 17 8 (patternOrder [[1,1,1],[2,1,3]]) (patternClique [[1,1,1],[2,1,3]]) (patternEdges [[1,1,1],[2,1,3]]) (patternAmount [[1,1,1],[2,1,3]]) (patternEdgeCount [[1,1,1],[2,1,3]]) [] := certificate_3015_checked

theorem certificate_3016_checked : certificate_3016.Valid 17 8 17 certificate_3016_q certificate_3016_edges 9 6 [] := by decide +kernel
theorem certificate_3016_valid : certificate_3016.Valid 17 8 (patternOrder [[1,1,1],[2,2,2]]) (patternClique [[1,1,1],[2,2,2]]) (patternEdges [[1,1,1],[2,2,2]]) (patternAmount [[1,1,1],[2,2,2]]) (patternEdgeCount [[1,1,1],[2,2,2]]) [] := certificate_3016_checked

theorem certificate_3017_checked : certificate_3017.Valid 17 8 17 certificate_3017_q certificate_3017_edges 9 5 [] := by decide +kernel
theorem certificate_3017_valid : certificate_3017.Valid 17 8 (patternOrder [[1,1,1],[3],[3]]) (patternClique [[1,1,1],[3],[3]]) (patternEdges [[1,1,1],[3],[3]]) (patternAmount [[1,1,1],[3],[3]]) (patternEdgeCount [[1,1,1],[3],[3]]) [] := certificate_3017_checked

theorem certificate_3018_checked : certificate_3018.Valid 17 8 15 certificate_3018_q certificate_3018_edges 7 6 [] := by decide +kernel
theorem certificate_3018_valid : certificate_3018.Valid 17 8 (patternOrder [[1,1,1,1],[1,2]]) (patternClique [[1,1,1,1],[1,2]]) (patternEdges [[1,1,1,1],[1,2]]) (patternAmount [[1,1,1,1],[1,2]]) (patternEdgeCount [[1,1,1,1],[1,2]]) [] := certificate_3018_checked

theorem certificate_3019_checked : certificate_3019.Valid 17 8 16 certificate_3019_q certificate_3019_edges 8 6 [] := by decide +kernel
theorem certificate_3019_valid : certificate_3019.Valid 17 8 (patternOrder [[1,1,1,1],[1,3]]) (patternClique [[1,1,1,1],[1,3]]) (patternEdges [[1,1,1,1],[1,3]]) (patternAmount [[1,1,1,1],[1,3]]) (patternEdgeCount [[1,1,1,1],[1,3]]) [] := certificate_3019_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns17x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_17_8_49_verified_oai : ∀ D ∈ patterns_17_8_49, PatternVerified 17 8 D := by

  simp only [patterns_17_8_49, List.forall_mem_cons]

  exact ⟨⟨certificate_3004, certificate_3004_valid⟩, ⟨⟨certificate_3005, certificate_3005_valid⟩, ⟨⟨certificate_3006, certificate_3006_valid⟩, ⟨⟨certificate_3007, certificate_3007_valid⟩, ⟨⟨certificate_3008, certificate_3008_valid⟩, ⟨⟨certificate_3009, certificate_3009_valid⟩, ⟨⟨certificate_3010, certificate_3010_valid⟩, ⟨⟨certificate_3011, certificate_3011_valid⟩, ⟨⟨certificate_3012, certificate_3012_valid⟩, ⟨⟨certificate_3013, certificate_3013_valid⟩, ⟨⟨certificate_3014, certificate_3014_valid⟩, ⟨⟨certificate_3015, certificate_3015_valid⟩, ⟨⟨certificate_3016, certificate_3016_valid⟩, ⟨⟨certificate_3017, certificate_3017_valid⟩, ⟨⟨certificate_3018, certificate_3018_valid⟩, ⟨⟨certificate_3019, certificate_3019_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_49_verified_oai := @OAI.CycleClique.patterns_17_8_49_verified_oai
