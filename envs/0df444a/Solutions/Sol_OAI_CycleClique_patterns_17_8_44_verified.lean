-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_44_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:53:16.64898+00:00
-- url     : https://prove2.me/submissions/e7d3c331-3cb5-4945-9135-39cd86382881

import Mathlib
import Definitions.Def_OAIQ107D132
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

theorem certificate_2924_checked : certificate_2924.Valid 17 8 16 certificate_2924_q certificate_2924_edges 8 5 [] := by decide +kernel
theorem certificate_2924_valid : certificate_2924.Valid 17 8 (patternOrder [[1],[1,1,3],[2]]) (patternClique [[1],[1,1,3],[2]]) (patternEdges [[1],[1,1,3],[2]]) (patternAmount [[1],[1,1,3],[2]]) (patternEdgeCount [[1],[1,1,3],[2]]) [] := certificate_2924_checked

theorem certificate_2925_checked : certificate_2925.Valid 17 8 17 certificate_2925_q certificate_2925_edges 9 5 [] := by decide +kernel
theorem certificate_2925_valid : certificate_2925.Valid 17 8 (patternOrder [[1],[1,1,3],[3]]) (patternClique [[1],[1,1,3],[3]]) (patternEdges [[1],[1,1,3],[3]]) (patternAmount [[1],[1,1,3],[3]]) (patternEdgeCount [[1],[1,1,3],[3]]) [] := certificate_2925_checked

theorem certificate_2926_checked : certificate_2926.Valid 17 8 16 certificate_2926_q certificate_2926_edges 8 6 [] := by decide +kernel
theorem certificate_2926_valid : certificate_2926.Valid 17 8 (patternOrder [[1],[1,1,3,1,1]]) (patternClique [[1],[1,1,3,1,1]]) (patternEdges [[1],[1,1,3,1,1]]) (patternAmount [[1],[1,1,3,1,1]]) (patternEdgeCount [[1],[1,1,3,1,1]]) [] := certificate_2926_checked

theorem certificate_2927_checked : certificate_2927.Valid 17 8 17 certificate_2927_q certificate_2927_edges 9 6 [] := by decide +kernel
theorem certificate_2927_valid : certificate_2927.Valid 17 8 (patternOrder [[1],[1,1,3,1,2]]) (patternClique [[1],[1,1,3,1,2]]) (patternEdges [[1],[1,1,3,1,2]]) (patternAmount [[1],[1,1,3,1,2]]) (patternEdgeCount [[1],[1,1,3,1,2]]) [] := certificate_2927_checked

theorem certificate_2928_checked : certificate_2928.Valid 17 8 17 certificate_2928_q certificate_2928_edges 9 6 [] := by decide +kernel
theorem certificate_2928_valid : certificate_2928.Valid 17 8 (patternOrder [[1],[1,1,3,2,1]]) (patternClique [[1],[1,1,3,2,1]]) (patternEdges [[1],[1,1,3,2,1]]) (patternAmount [[1],[1,1,3,2,1]]) (patternEdgeCount [[1],[1,1,3,2,1]]) [] := certificate_2928_checked

theorem certificate_2929_checked : certificate_2929.Valid 17 8 17 certificate_2929_q certificate_2929_edges 9 5 [] := by decide +kernel
theorem certificate_2929_valid : certificate_2929.Valid 17 8 (patternOrder [[1],[1,1,4],[2]]) (patternClique [[1],[1,1,4],[2]]) (patternEdges [[1],[1,1,4],[2]]) (patternAmount [[1],[1,1,4],[2]]) (patternEdgeCount [[1],[1,1,4],[2]]) [] := certificate_2929_checked

theorem certificate_2930_checked : certificate_2930.Valid 17 8 17 certificate_2930_q certificate_2930_edges 9 6 [] := by decide +kernel
theorem certificate_2930_valid : certificate_2930.Valid 17 8 (patternOrder [[1],[1,1,4,1,1]]) (patternClique [[1],[1,1,4,1,1]]) (patternEdges [[1],[1,1,4,1,1]]) (patternAmount [[1],[1,1,4,1,1]]) (patternEdgeCount [[1],[1,1,4,1,1]]) [] := certificate_2930_checked

theorem certificate_2931_checked : certificate_2931.Valid 17 8 15 certificate_2931_q certificate_2931_edges 7 5 [] := by decide +kernel
theorem certificate_2931_valid : certificate_2931.Valid 17 8 (patternOrder [[1],[1,2],[1,2]]) (patternClique [[1],[1,2],[1,2]]) (patternEdges [[1],[1,2],[1,2]]) (patternAmount [[1],[1,2],[1,2]]) (patternEdgeCount [[1],[1,2],[1,2]]) [] := certificate_2931_checked

theorem certificate_2932_checked : certificate_2932.Valid 17 8 16 certificate_2932_q certificate_2932_edges 8 5 [] := by decide +kernel
theorem certificate_2932_valid : certificate_2932.Valid 17 8 (patternOrder [[1],[1,2],[1,3]]) (patternClique [[1],[1,2],[1,3]]) (patternEdges [[1],[1,2],[1,3]]) (patternAmount [[1],[1,2],[1,3]]) (patternEdgeCount [[1],[1,2],[1,3]]) [] := certificate_2932_checked

theorem certificate_2933_checked : certificate_2933.Valid 17 8 17 certificate_2933_q certificate_2933_edges 9 5 [] := by decide +kernel
theorem certificate_2933_valid : certificate_2933.Valid 17 8 (patternOrder [[1],[1,2],[1,4]]) (patternClique [[1],[1,2],[1,4]]) (patternEdges [[1],[1,2],[1,4]]) (patternAmount [[1],[1,2],[1,4]]) (patternEdgeCount [[1],[1,2],[1,4]]) [] := certificate_2933_checked

theorem certificate_2934_checked : certificate_2934.Valid 17 8 16 certificate_2934_q certificate_2934_edges 8 5 [] := by decide +kernel
theorem certificate_2934_valid : certificate_2934.Valid 17 8 (patternOrder [[1],[1,2],[2,2]]) (patternClique [[1],[1,2],[2,2]]) (patternEdges [[1],[1,2],[2,2]]) (patternAmount [[1],[1,2],[2,2]]) (patternEdgeCount [[1],[1,2],[2,2]]) [] := certificate_2934_checked

theorem certificate_2935_checked : certificate_2935.Valid 17 8 17 certificate_2935_q certificate_2935_edges 9 5 [] := by decide +kernel
theorem certificate_2935_valid : certificate_2935.Valid 17 8 (patternOrder [[1],[1,2],[2,3]]) (patternClique [[1],[1,2],[2,3]]) (patternEdges [[1],[1,2],[2,3]]) (patternAmount [[1],[1,2],[2,3]]) (patternEdgeCount [[1],[1,2],[2,3]]) [] := certificate_2935_checked

theorem certificate_2936_checked : certificate_2936.Valid 17 8 15 certificate_2936_q certificate_2936_edges 7 5 [] := by decide +kernel
theorem certificate_2936_valid : certificate_2936.Valid 17 8 (patternOrder [[1],[1,2,1],[2]]) (patternClique [[1],[1,2,1],[2]]) (patternEdges [[1],[1,2,1],[2]]) (patternAmount [[1],[1,2,1],[2]]) (patternEdgeCount [[1],[1,2,1],[2]]) [] := certificate_2936_checked

theorem certificate_2937_checked : certificate_2937.Valid 17 8 16 certificate_2937_q certificate_2937_edges 8 5 [] := by decide +kernel
theorem certificate_2937_valid : certificate_2937.Valid 17 8 (patternOrder [[1],[1,2,1],[3]]) (patternClique [[1],[1,2,1],[3]]) (patternEdges [[1],[1,2,1],[3]]) (patternAmount [[1],[1,2,1],[3]]) (patternEdgeCount [[1],[1,2,1],[3]]) [] := certificate_2937_checked

theorem certificate_2938_checked : certificate_2938.Valid 17 8 17 certificate_2938_q certificate_2938_edges 9 5 [] := by decide +kernel
theorem certificate_2938_valid : certificate_2938.Valid 17 8 (patternOrder [[1],[1,2,1],[4]]) (patternClique [[1],[1,2,1],[4]]) (patternEdges [[1],[1,2,1],[4]]) (patternAmount [[1],[1,2,1],[4]]) (patternEdgeCount [[1],[1,2,1],[4]]) [] := certificate_2938_checked

theorem certificate_2939_checked : certificate_2939.Valid 17 8 16 certificate_2939_q certificate_2939_edges 8 6 [] := by decide +kernel
theorem certificate_2939_valid : certificate_2939.Valid 17 8 (patternOrder [[1],[1,2,1,1,2]]) (patternClique [[1],[1,2,1,1,2]]) (patternEdges [[1],[1,2,1,1,2]]) (patternAmount [[1],[1,2,1,1,2]]) (patternEdgeCount [[1],[1,2,1,1,2]]) [] := certificate_2939_checked

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

theorem patterns_17_8_44_verified_oai : ∀ D ∈ patterns_17_8_44, PatternVerified 17 8 D := by

  simp only [patterns_17_8_44, List.forall_mem_cons]

  exact ⟨⟨certificate_2924, certificate_2924_valid⟩, ⟨⟨certificate_2925, certificate_2925_valid⟩, ⟨⟨certificate_2926, certificate_2926_valid⟩, ⟨⟨certificate_2927, certificate_2927_valid⟩, ⟨⟨certificate_2928, certificate_2928_valid⟩, ⟨⟨certificate_2929, certificate_2929_valid⟩, ⟨⟨certificate_2930, certificate_2930_valid⟩, ⟨⟨certificate_2931, certificate_2931_valid⟩, ⟨⟨certificate_2932, certificate_2932_valid⟩, ⟨⟨certificate_2933, certificate_2933_valid⟩, ⟨⟨certificate_2934, certificate_2934_valid⟩, ⟨⟨certificate_2935, certificate_2935_valid⟩, ⟨⟨certificate_2936, certificate_2936_valid⟩, ⟨⟨certificate_2937, certificate_2937_valid⟩, ⟨⟨certificate_2938, certificate_2938_valid⟩, ⟨⟨certificate_2939, certificate_2939_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_44_verified_oai := @OAI.CycleClique.patterns_17_8_44_verified_oai
