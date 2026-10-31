-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_48_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:52:32.769593+00:00
-- url     : https://prove2.me/submissions/6a8d1252-a26d-4e2c-a861-2b2ad271431e

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

theorem certificate_2988_checked : certificate_2988.Valid 17 8 16 certificate_2988_q certificate_2988_edges 8 6 [] := by decide +kernel
theorem certificate_2988_valid : certificate_2988.Valid 17 8 (patternOrder [[1,1],[1,2,2,1]]) (patternClique [[1,1],[1,2,2,1]]) (patternEdges [[1,1],[1,2,2,1]]) (patternAmount [[1,1],[1,2,2,1]]) (patternEdgeCount [[1,1],[1,2,2,1]]) [] := certificate_2988_checked

theorem certificate_2989_checked : certificate_2989.Valid 17 8 17 certificate_2989_q certificate_2989_edges 9 6 [] := by decide +kernel
theorem certificate_2989_valid : certificate_2989.Valid 17 8 (patternOrder [[1,1],[1,2,2,2]]) (patternClique [[1,1],[1,2,2,2]]) (patternEdges [[1,1],[1,2,2,2]]) (patternAmount [[1,1],[1,2,2,2]]) (patternEdgeCount [[1,1],[1,2,2,2]]) [] := certificate_2989_checked

theorem certificate_2990_checked : certificate_2990.Valid 17 8 17 certificate_2990_q certificate_2990_edges 9 6 [] := by decide +kernel
theorem certificate_2990_valid : certificate_2990.Valid 17 8 (patternOrder [[1,1],[1,2,3,1]]) (patternClique [[1,1],[1,2,3,1]]) (patternEdges [[1,1],[1,2,3,1]]) (patternAmount [[1,1],[1,2,3,1]]) (patternEdgeCount [[1,1],[1,2,3,1]]) [] := certificate_2990_checked

theorem certificate_2991_checked : certificate_2991.Valid 17 8 16 certificate_2991_q certificate_2991_edges 8 5 [] := by decide +kernel
theorem certificate_2991_valid : certificate_2991.Valid 17 8 (patternOrder [[1,1],[1,3],[2]]) (patternClique [[1,1],[1,3],[2]]) (patternEdges [[1,1],[1,3],[2]]) (patternAmount [[1,1],[1,3],[2]]) (patternEdgeCount [[1,1],[1,3],[2]]) [] := certificate_2991_checked

theorem certificate_2992_checked : certificate_2992.Valid 17 8 17 certificate_2992_q certificate_2992_edges 9 5 [] := by decide +kernel
theorem certificate_2992_valid : certificate_2992.Valid 17 8 (patternOrder [[1,1],[1,3],[3]]) (patternClique [[1,1],[1,3],[3]]) (patternEdges [[1,1],[1,3],[3]]) (patternAmount [[1,1],[1,3],[3]]) (patternEdgeCount [[1,1],[1,3],[3]]) [] := certificate_2992_checked

theorem certificate_2993_checked : certificate_2993.Valid 17 8 17 certificate_2993_q certificate_2993_edges 9 6 [] := by decide +kernel
theorem certificate_2993_valid : certificate_2993.Valid 17 8 (patternOrder [[1,1],[1,3,1,2]]) (patternClique [[1,1],[1,3,1,2]]) (patternEdges [[1,1],[1,3,1,2]]) (patternAmount [[1,1],[1,3,1,2]]) (patternEdgeCount [[1,1],[1,3,1,2]]) [] := certificate_2993_checked

theorem certificate_2994_checked : certificate_2994.Valid 17 8 17 certificate_2994_q certificate_2994_edges 9 5 [] := by decide +kernel
theorem certificate_2994_valid : certificate_2994.Valid 17 8 (patternOrder [[1,1],[1,4],[2]]) (patternClique [[1,1],[1,4],[2]]) (patternEdges [[1,1],[1,4],[2]]) (patternAmount [[1,1],[1,4],[2]]) (patternEdgeCount [[1,1],[1,4],[2]]) [] := certificate_2994_checked

theorem certificate_2995_checked : certificate_2995.Valid 17 8 16 certificate_2995_q certificate_2995_edges 8 5 [] := by decide +kernel
theorem certificate_2995_valid : certificate_2995.Valid 17 8 (patternOrder [[1,1],[2],[2,2]]) (patternClique [[1,1],[2],[2,2]]) (patternEdges [[1,1],[2],[2,2]]) (patternAmount [[1,1],[2],[2,2]]) (patternEdgeCount [[1,1],[2],[2,2]]) [] := certificate_2995_checked

theorem certificate_2996_checked : certificate_2996.Valid 17 8 17 certificate_2996_q certificate_2996_edges 9 5 [] := by decide +kernel
theorem certificate_2996_valid : certificate_2996.Valid 17 8 (patternOrder [[1,1],[2],[2,3]]) (patternClique [[1,1],[2],[2,3]]) (patternEdges [[1,1],[2],[2,3]]) (patternAmount [[1,1],[2],[2,3]]) (patternEdgeCount [[1,1],[2],[2,3]]) [] := certificate_2996_checked

theorem certificate_2997_checked : certificate_2997.Valid 17 8 16 certificate_2997_q certificate_2997_edges 8 6 [] := by decide +kernel
theorem certificate_2997_valid : certificate_2997.Valid 17 8 (patternOrder [[1,1],[2,1,1,2]]) (patternClique [[1,1],[2,1,1,2]]) (patternEdges [[1,1],[2,1,1,2]]) (patternAmount [[1,1],[2,1,1,2]]) (patternEdgeCount [[1,1],[2,1,1,2]]) [] := certificate_2997_checked

theorem certificate_2998_checked : certificate_2998.Valid 17 8 17 certificate_2998_q certificate_2998_edges 9 6 [] := by decide +kernel
theorem certificate_2998_valid : certificate_2998.Valid 17 8 (patternOrder [[1,1],[2,1,1,3]]) (patternClique [[1,1],[2,1,1,3]]) (patternEdges [[1,1],[2,1,1,3]]) (patternAmount [[1,1],[2,1,1,3]]) (patternEdgeCount [[1,1],[2,1,1,3]]) [] := certificate_2998_checked

theorem certificate_2999_checked : certificate_2999.Valid 17 8 17 certificate_2999_q certificate_2999_edges 9 6 [] := by decide +kernel
theorem certificate_2999_valid : certificate_2999.Valid 17 8 (patternOrder [[1,1],[2,1,2,2]]) (patternClique [[1,1],[2,1,2,2]]) (patternEdges [[1,1],[2,1,2,2]]) (patternAmount [[1,1],[2,1,2,2]]) (patternEdgeCount [[1,1],[2,1,2,2]]) [] := certificate_2999_checked

theorem certificate_3000_checked : certificate_3000.Valid 17 8 17 certificate_3000_q certificate_3000_edges 9 5 [] := by decide +kernel
theorem certificate_3000_valid : certificate_3000.Valid 17 8 (patternOrder [[1,1],[2,2],[3]]) (patternClique [[1,1],[2,2],[3]]) (patternEdges [[1,1],[2,2],[3]]) (patternAmount [[1,1],[2,2],[3]]) (patternEdgeCount [[1,1],[2,2],[3]]) [] := certificate_3000_checked

theorem certificate_3001_checked : certificate_3001.Valid 17 8 14 certificate_3001_q certificate_3001_edges 6 6 [] := by decide +kernel
theorem certificate_3001_valid : certificate_3001.Valid 17 8 (patternOrder [[1,1,1],[1,1,1]]) (patternClique [[1,1,1],[1,1,1]]) (patternEdges [[1,1,1],[1,1,1]]) (patternAmount [[1,1,1],[1,1,1]]) (patternEdgeCount [[1,1,1],[1,1,1]]) [] := certificate_3001_checked

theorem certificate_3002_checked : certificate_3002.Valid 17 8 15 certificate_3002_q certificate_3002_edges 7 6 [] := by decide +kernel
theorem certificate_3002_valid : certificate_3002.Valid 17 8 (patternOrder [[1,1,1],[1,1,2]]) (patternClique [[1,1,1],[1,1,2]]) (patternEdges [[1,1,1],[1,1,2]]) (patternAmount [[1,1,1],[1,1,2]]) (patternEdgeCount [[1,1,1],[1,1,2]]) [] := certificate_3002_checked

theorem certificate_3003_checked : certificate_3003.Valid 17 8 16 certificate_3003_q certificate_3003_edges 8 6 [] := by decide +kernel
theorem certificate_3003_valid : certificate_3003.Valid 17 8 (patternOrder [[1,1,1],[1,1,3]]) (patternClique [[1,1,1],[1,1,3]]) (patternEdges [[1,1,1],[1,1,3]]) (patternAmount [[1,1,1],[1,1,3]]) (patternEdgeCount [[1,1,1],[1,1,3]]) [] := certificate_3003_checked

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

theorem patterns_17_8_48_verified_oai : ∀ D ∈ patterns_17_8_48, PatternVerified 17 8 D := by

  simp only [patterns_17_8_48, List.forall_mem_cons]

  exact ⟨⟨certificate_2988, certificate_2988_valid⟩, ⟨⟨certificate_2989, certificate_2989_valid⟩, ⟨⟨certificate_2990, certificate_2990_valid⟩, ⟨⟨certificate_2991, certificate_2991_valid⟩, ⟨⟨certificate_2992, certificate_2992_valid⟩, ⟨⟨certificate_2993, certificate_2993_valid⟩, ⟨⟨certificate_2994, certificate_2994_valid⟩, ⟨⟨certificate_2995, certificate_2995_valid⟩, ⟨⟨certificate_2996, certificate_2996_valid⟩, ⟨⟨certificate_2997, certificate_2997_valid⟩, ⟨⟨certificate_2998, certificate_2998_valid⟩, ⟨⟨certificate_2999, certificate_2999_valid⟩, ⟨⟨certificate_3000, certificate_3000_valid⟩, ⟨⟨certificate_3001, certificate_3001_valid⟩, ⟨⟨certificate_3002, certificate_3002_valid⟩, ⟨⟨certificate_3003, certificate_3003_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_48_verified_oai := @OAI.CycleClique.patterns_17_8_48_verified_oai
