-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_45_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:48:54.920231+00:00
-- url     : https://prove2.me/submissions/851a1bd3-7977-4427-adc0-d2b080c8e7d5

import Mathlib
import Definitions.Def_OAIQ107D099
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates092
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2940_checked : certificate_2940.Valid 17 8 17 certificate_2940_q certificate_2940_edges 9 6 [] := by decide +kernel
theorem certificate_2940_valid : certificate_2940.Valid 17 8 (patternOrder [[1],[1,2,1,1,3]]) (patternClique [[1],[1,2,1,1,3]]) (patternEdges [[1],[1,2,1,1,3]]) (patternAmount [[1],[1,2,1,1,3]]) (patternEdgeCount [[1],[1,2,1,1,3]]) [] := certificate_2940_checked

theorem certificate_2941_checked : certificate_2941.Valid 17 8 16 certificate_2941_q certificate_2941_edges 8 6 [] := by decide +kernel
theorem certificate_2941_valid : certificate_2941.Valid 17 8 (patternOrder [[1],[1,2,1,2,1]]) (patternClique [[1],[1,2,1,2,1]]) (patternEdges [[1],[1,2,1,2,1]]) (patternAmount [[1],[1,2,1,2,1]]) (patternEdgeCount [[1],[1,2,1,2,1]]) [] := certificate_2941_checked

theorem certificate_2942_checked : certificate_2942.Valid 17 8 17 certificate_2942_q certificate_2942_edges 9 6 [] := by decide +kernel
theorem certificate_2942_valid : certificate_2942.Valid 17 8 (patternOrder [[1],[1,2,1,2,2]]) (patternClique [[1],[1,2,1,2,2]]) (patternEdges [[1],[1,2,1,2,2]]) (patternAmount [[1],[1,2,1,2,2]]) (patternEdgeCount [[1],[1,2,1,2,2]]) [] := certificate_2942_checked

theorem certificate_2943_checked : certificate_2943.Valid 17 8 17 certificate_2943_q certificate_2943_edges 9 6 [] := by decide +kernel
theorem certificate_2943_valid : certificate_2943.Valid 17 8 (patternOrder [[1],[1,2,1,3,1]]) (patternClique [[1],[1,2,1,3,1]]) (patternEdges [[1],[1,2,1,3,1]]) (patternAmount [[1],[1,2,1,3,1]]) (patternEdgeCount [[1],[1,2,1,3,1]]) [] := certificate_2943_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates093
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2944_checked : certificate_2944.Valid 17 8 16 certificate_2944_q certificate_2944_edges 8 5 [] := by decide +kernel
theorem certificate_2944_valid : certificate_2944.Valid 17 8 (patternOrder [[1],[1,2,2],[2]]) (patternClique [[1],[1,2,2],[2]]) (patternEdges [[1],[1,2,2],[2]]) (patternAmount [[1],[1,2,2],[2]]) (patternEdgeCount [[1],[1,2,2],[2]]) [] := certificate_2944_checked

theorem certificate_2945_checked : certificate_2945.Valid 17 8 17 certificate_2945_q certificate_2945_edges 9 5 [] := by decide +kernel
theorem certificate_2945_valid : certificate_2945.Valid 17 8 (patternOrder [[1],[1,2,2],[3]]) (patternClique [[1],[1,2,2],[3]]) (patternEdges [[1],[1,2,2],[3]]) (patternAmount [[1],[1,2,2],[3]]) (patternEdgeCount [[1],[1,2,2],[3]]) [] := certificate_2945_checked

theorem certificate_2946_checked : certificate_2946.Valid 17 8 17 certificate_2946_q certificate_2946_edges 9 6 [] := by decide +kernel
theorem certificate_2946_valid : certificate_2946.Valid 17 8 (patternOrder [[1],[1,2,2,1,2]]) (patternClique [[1],[1,2,2,1,2]]) (patternEdges [[1],[1,2,2,1,2]]) (patternAmount [[1],[1,2,2,1,2]]) (patternEdgeCount [[1],[1,2,2,1,2]]) [] := certificate_2946_checked

theorem certificate_2947_checked : certificate_2947.Valid 17 8 17 certificate_2947_q certificate_2947_edges 9 6 [] := by decide +kernel
theorem certificate_2947_valid : certificate_2947.Valid 17 8 (patternOrder [[1],[1,2,2,2,1]]) (patternClique [[1],[1,2,2,2,1]]) (patternEdges [[1],[1,2,2,2,1]]) (patternAmount [[1],[1,2,2,2,1]]) (patternEdgeCount [[1],[1,2,2,2,1]]) [] := certificate_2947_checked

theorem certificate_2948_checked : certificate_2948.Valid 17 8 17 certificate_2948_q certificate_2948_edges 9 5 [] := by decide +kernel
theorem certificate_2948_valid : certificate_2948.Valid 17 8 (patternOrder [[1],[1,2,3],[2]]) (patternClique [[1],[1,2,3],[2]]) (patternEdges [[1],[1,2,3],[2]]) (patternAmount [[1],[1,2,3],[2]]) (patternEdgeCount [[1],[1,2,3],[2]]) [] := certificate_2948_checked

theorem certificate_2949_checked : certificate_2949.Valid 17 8 17 certificate_2949_q certificate_2949_edges 9 5 [] := by decide +kernel
theorem certificate_2949_valid : certificate_2949.Valid 17 8 (patternOrder [[1],[1,3],[1,3]]) (patternClique [[1],[1,3],[1,3]]) (patternEdges [[1],[1,3],[1,3]]) (patternAmount [[1],[1,3],[1,3]]) (patternEdgeCount [[1],[1,3],[1,3]]) [] := certificate_2949_checked

theorem certificate_2950_checked : certificate_2950.Valid 17 8 17 certificate_2950_q certificate_2950_edges 9 5 [] := by decide +kernel
theorem certificate_2950_valid : certificate_2950.Valid 17 8 (patternOrder [[1],[1,3],[2,2]]) (patternClique [[1],[1,3],[2,2]]) (patternEdges [[1],[1,3],[2,2]]) (patternAmount [[1],[1,3],[2,2]]) (patternEdgeCount [[1],[1,3],[2,2]]) [] := certificate_2950_checked

theorem certificate_2951_checked : certificate_2951.Valid 17 8 16 certificate_2951_q certificate_2951_edges 8 5 [] := by decide +kernel
theorem certificate_2951_valid : certificate_2951.Valid 17 8 (patternOrder [[1],[1,3,1],[2]]) (patternClique [[1],[1,3,1],[2]]) (patternEdges [[1],[1,3,1],[2]]) (patternAmount [[1],[1,3,1],[2]]) (patternEdgeCount [[1],[1,3,1],[2]]) [] := certificate_2951_checked

theorem certificate_2952_checked : certificate_2952.Valid 17 8 17 certificate_2952_q certificate_2952_edges 9 5 [] := by decide +kernel
theorem certificate_2952_valid : certificate_2952.Valid 17 8 (patternOrder [[1],[1,3,1],[3]]) (patternClique [[1],[1,3,1],[3]]) (patternEdges [[1],[1,3,1],[3]]) (patternAmount [[1],[1,3,1],[3]]) (patternEdgeCount [[1],[1,3,1],[3]]) [] := certificate_2952_checked

theorem certificate_2953_checked : certificate_2953.Valid 17 8 17 certificate_2953_q certificate_2953_edges 9 6 [] := by decide +kernel
theorem certificate_2953_valid : certificate_2953.Valid 17 8 (patternOrder [[1],[1,3,1,1,2]]) (patternClique [[1],[1,3,1,1,2]]) (patternEdges [[1],[1,3,1,1,2]]) (patternAmount [[1],[1,3,1,1,2]]) (patternEdgeCount [[1],[1,3,1,1,2]]) [] := certificate_2953_checked

theorem certificate_2954_checked : certificate_2954.Valid 17 8 17 certificate_2954_q certificate_2954_edges 9 5 [] := by decide +kernel
theorem certificate_2954_valid : certificate_2954.Valid 17 8 (patternOrder [[1],[1,3,2],[2]]) (patternClique [[1],[1,3,2],[2]]) (patternEdges [[1],[1,3,2],[2]]) (patternAmount [[1],[1,3,2],[2]]) (patternEdgeCount [[1],[1,3,2],[2]]) [] := certificate_2954_checked

theorem certificate_2955_checked : certificate_2955.Valid 17 8 17 certificate_2955_q certificate_2955_edges 9 5 [] := by decide +kernel
theorem certificate_2955_valid : certificate_2955.Valid 17 8 (patternOrder [[1],[1,4,1],[2]]) (patternClique [[1],[1,4,1],[2]]) (patternEdges [[1],[1,4,1],[2]]) (patternAmount [[1],[1,4,1],[2]]) (patternEdgeCount [[1],[1,4,1],[2]]) [] := certificate_2955_checked

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

theorem patterns_17_8_45_verified_oai : ∀ D ∈ patterns_17_8_45, PatternVerified 17 8 D := by

  simp only [patterns_17_8_45, List.forall_mem_cons]

  exact ⟨⟨certificate_2940, certificate_2940_valid⟩, ⟨⟨certificate_2941, certificate_2941_valid⟩, ⟨⟨certificate_2942, certificate_2942_valid⟩, ⟨⟨certificate_2943, certificate_2943_valid⟩, ⟨⟨certificate_2944, certificate_2944_valid⟩, ⟨⟨certificate_2945, certificate_2945_valid⟩, ⟨⟨certificate_2946, certificate_2946_valid⟩, ⟨⟨certificate_2947, certificate_2947_valid⟩, ⟨⟨certificate_2948, certificate_2948_valid⟩, ⟨⟨certificate_2949, certificate_2949_valid⟩, ⟨⟨certificate_2950, certificate_2950_valid⟩, ⟨⟨certificate_2951, certificate_2951_valid⟩, ⟨⟨certificate_2952, certificate_2952_valid⟩, ⟨⟨certificate_2953, certificate_2953_valid⟩, ⟨⟨certificate_2954, certificate_2954_valid⟩, ⟨⟨certificate_2955, certificate_2955_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_45_verified_oai := @OAI.CycleClique.patterns_17_8_45_verified_oai
