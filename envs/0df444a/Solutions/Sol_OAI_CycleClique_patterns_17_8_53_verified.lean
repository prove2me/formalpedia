-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_53_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:00:54.581169+00:00
-- url     : https://prove2.me/submissions/1c6812b4-10ef-4b9b-bc5a-7175b3d1faa4

import Mathlib
import Definitions.Def_OAIQ107D132
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates096
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_3068_checked : certificate_3068.Valid 17 8 17 certificate_3068_q certificate_3068_edges 9 7 [] := by decide +kernel
theorem certificate_3068_valid : certificate_3068.Valid 17 8 (patternOrder [[1,1,2,1,2,1,1]]) (patternClique [[1,1,2,1,2,1,1]]) (patternEdges [[1,1,2,1,2,1,1]]) (patternAmount [[1,1,2,1,2,1,1]]) (patternEdgeCount [[1,1,2,1,2,1,1]]) [] := certificate_3068_checked

theorem certificate_3069_checked : certificate_3069.Valid 17 8 17 certificate_3069_q certificate_3069_edges 9 6 [] := by decide +kernel
theorem certificate_3069_valid : certificate_3069.Valid 17 8 (patternOrder [[1,1,2,2],[1,2]]) (patternClique [[1,1,2,2],[1,2]]) (patternEdges [[1,1,2,2],[1,2]]) (patternAmount [[1,1,2,2],[1,2]]) (patternEdgeCount [[1,1,2,2],[1,2]]) [] := certificate_3069_checked

theorem certificate_3070_checked : certificate_3070.Valid 17 8 17 certificate_3070_q certificate_3070_edges 9 6 [] := by decide +kernel
theorem certificate_3070_valid : certificate_3070.Valid 17 8 (patternOrder [[1,1,2,2,1],[2]]) (patternClique [[1,1,2,2,1],[2]]) (patternEdges [[1,1,2,2,1],[2]]) (patternAmount [[1,1,2,2,1],[2]]) (patternEdgeCount [[1,1,2,2,1],[2]]) [] := certificate_3070_checked

theorem certificate_3071_checked : certificate_3071.Valid 17 8 17 certificate_3071_q certificate_3071_edges 9 6 [] := by decide +kernel
theorem certificate_3071_valid : certificate_3071.Valid 17 8 (patternOrder [[1,1,3],[1,2,1]]) (patternClique [[1,1,3],[1,2,1]]) (patternEdges [[1,1,3],[1,2,1]]) (patternAmount [[1,1,3],[1,2,1]]) (patternEdgeCount [[1,1,3],[1,2,1]]) [] := certificate_3071_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates097
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_3072_checked : certificate_3072.Valid 17 8 17 certificate_3072_q certificate_3072_edges 9 5 [] := by decide +kernel
theorem certificate_3072_valid : certificate_3072.Valid 17 8 (patternOrder [[1,1,3],[2],[2]]) (patternClique [[1,1,3],[2],[2]]) (patternEdges [[1,1,3],[2],[2]]) (patternAmount [[1,1,3],[2],[2]]) (patternEdgeCount [[1,1,3],[2],[2]]) [] := certificate_3072_checked

theorem certificate_3073_checked : certificate_3073.Valid 17 8 17 certificate_3073_q certificate_3073_edges 9 6 [] := by decide +kernel
theorem certificate_3073_valid : certificate_3073.Valid 17 8 (patternOrder [[1,1,3,1],[1,2]]) (patternClique [[1,1,3,1],[1,2]]) (patternEdges [[1,1,3,1],[1,2]]) (patternAmount [[1,1,3,1],[1,2]]) (patternEdgeCount [[1,1,3,1],[1,2]]) [] := certificate_3073_checked

theorem certificate_3074_checked : certificate_3074.Valid 17 8 17 certificate_3074_q certificate_3074_edges 9 6 [] := by decide +kernel
theorem certificate_3074_valid : certificate_3074.Valid 17 8 (patternOrder [[1,1,3,1,1],[2]]) (patternClique [[1,1,3,1,1],[2]]) (patternEdges [[1,1,3,1,1],[2]]) (patternAmount [[1,1,3,1,1],[2]]) (patternEdgeCount [[1,1,3,1,1],[2]]) [] := certificate_3074_checked

theorem certificate_3075_checked : certificate_3075.Valid 17 8 16 certificate_3075_q certificate_3075_edges 8 5 [] := by decide +kernel
theorem certificate_3075_valid : certificate_3075.Valid 17 8 (patternOrder [[1,2],[1,2],[2]]) (patternClique [[1,2],[1,2],[2]]) (patternEdges [[1,2],[1,2],[2]]) (patternAmount [[1,2],[1,2],[2]]) (patternEdgeCount [[1,2],[1,2],[2]]) [] := certificate_3075_checked

theorem certificate_3076_checked : certificate_3076.Valid 17 8 17 certificate_3076_q certificate_3076_edges 9 5 [] := by decide +kernel
theorem certificate_3076_valid : certificate_3076.Valid 17 8 (patternOrder [[1,2],[1,2],[3]]) (patternClique [[1,2],[1,2],[3]]) (patternEdges [[1,2],[1,2],[3]]) (patternAmount [[1,2],[1,2],[3]]) (patternEdgeCount [[1,2],[1,2],[3]]) [] := certificate_3076_checked

theorem certificate_3077_checked : certificate_3077.Valid 17 8 17 certificate_3077_q certificate_3077_edges 9 6 [] := by decide +kernel
theorem certificate_3077_valid : certificate_3077.Valid 17 8 (patternOrder [[1,2],[1,2,1,2]]) (patternClique [[1,2],[1,2,1,2]]) (patternEdges [[1,2],[1,2,1,2]]) (patternAmount [[1,2],[1,2,1,2]]) (patternEdgeCount [[1,2],[1,2,1,2]]) [] := certificate_3077_checked

theorem certificate_3078_checked : certificate_3078.Valid 17 8 17 certificate_3078_q certificate_3078_edges 9 6 [] := by decide +kernel
theorem certificate_3078_valid : certificate_3078.Valid 17 8 (patternOrder [[1,2],[1,2,2,1]]) (patternClique [[1,2],[1,2,2,1]]) (patternEdges [[1,2],[1,2,2,1]]) (patternAmount [[1,2],[1,2,2,1]]) (patternEdgeCount [[1,2],[1,2,2,1]]) [] := certificate_3078_checked

theorem certificate_3079_checked : certificate_3079.Valid 17 8 17 certificate_3079_q certificate_3079_edges 9 5 [] := by decide +kernel
theorem certificate_3079_valid : certificate_3079.Valid 17 8 (patternOrder [[1,2],[1,3],[2]]) (patternClique [[1,2],[1,3],[2]]) (patternEdges [[1,2],[1,3],[2]]) (patternAmount [[1,2],[1,3],[2]]) (patternEdgeCount [[1,2],[1,3],[2]]) [] := certificate_3079_checked

theorem certificate_3080_checked : certificate_3080.Valid 17 8 17 certificate_3080_q certificate_3080_edges 9 5 [] := by decide +kernel
theorem certificate_3080_valid : certificate_3080.Valid 17 8 (patternOrder [[1,2],[2],[2,2]]) (patternClique [[1,2],[2],[2,2]]) (patternEdges [[1,2],[2],[2,2]]) (patternAmount [[1,2],[2],[2,2]]) (patternEdgeCount [[1,2],[2],[2,2]]) [] := certificate_3080_checked

theorem certificate_3081_checked : certificate_3081.Valid 17 8 17 certificate_3081_q certificate_3081_edges 9 6 [] := by decide +kernel
theorem certificate_3081_valid : certificate_3081.Valid 17 8 (patternOrder [[1,2],[2,1,1,2]]) (patternClique [[1,2],[2,1,1,2]]) (patternEdges [[1,2],[2,1,1,2]]) (patternAmount [[1,2],[2,1,1,2]]) (patternEdgeCount [[1,2],[2,1,1,2]]) [] := certificate_3081_checked

theorem certificate_3082_checked : certificate_3082.Valid 17 8 16 certificate_3082_q certificate_3082_edges 8 6 [] := by decide +kernel
theorem certificate_3082_valid : certificate_3082.Valid 17 8 (patternOrder [[1,2,1],[1,2,1]]) (patternClique [[1,2,1],[1,2,1]]) (patternEdges [[1,2,1],[1,2,1]]) (patternAmount [[1,2,1],[1,2,1]]) (patternEdgeCount [[1,2,1],[1,2,1]]) [] := certificate_3082_checked

theorem certificate_3083_checked : certificate_3083.Valid 17 8 17 certificate_3083_q certificate_3083_edges 9 6 [] := by decide +kernel
theorem certificate_3083_valid : certificate_3083.Valid 17 8 (patternOrder [[1,2,1],[1,2,2]]) (patternClique [[1,2,1],[1,2,2]]) (patternEdges [[1,2,1],[1,2,2]]) (patternAmount [[1,2,1],[1,2,2]]) (patternEdgeCount [[1,2,1],[1,2,2]]) [] := certificate_3083_checked

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

theorem patterns_17_8_53_verified_oai : ∀ D ∈ patterns_17_8_53, PatternVerified 17 8 D := by

  simp only [patterns_17_8_53, List.forall_mem_cons]

  exact ⟨⟨certificate_3068, certificate_3068_valid⟩, ⟨⟨certificate_3069, certificate_3069_valid⟩, ⟨⟨certificate_3070, certificate_3070_valid⟩, ⟨⟨certificate_3071, certificate_3071_valid⟩, ⟨⟨certificate_3072, certificate_3072_valid⟩, ⟨⟨certificate_3073, certificate_3073_valid⟩, ⟨⟨certificate_3074, certificate_3074_valid⟩, ⟨⟨certificate_3075, certificate_3075_valid⟩, ⟨⟨certificate_3076, certificate_3076_valid⟩, ⟨⟨certificate_3077, certificate_3077_valid⟩, ⟨⟨certificate_3078, certificate_3078_valid⟩, ⟨⟨certificate_3079, certificate_3079_valid⟩, ⟨⟨certificate_3080, certificate_3080_valid⟩, ⟨⟨certificate_3081, certificate_3081_valid⟩, ⟨⟨certificate_3082, certificate_3082_valid⟩, ⟨⟨certificate_3083, certificate_3083_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_53_verified_oai := @OAI.CycleClique.patterns_17_8_53_verified_oai
