-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_26_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:47:27.092218+00:00
-- url     : https://prove2.me/submissions/2fce86e4-8f63-46f1-a2b1-6336f798dd7f

import Mathlib
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates068
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2168_checked : certificate_2168.Valid 16 8 16 certificate_2168_q certificate_2168_edges 8 5 [] := by decide +kernel
theorem certificate_2168_valid : certificate_2168.Valid 16 8 (patternOrder [[1],[1,3,1],[2]]) (patternClique [[1],[1,3,1],[2]]) (patternEdges [[1],[1,3,1],[2]]) (patternAmount [[1],[1,3,1],[2]]) (patternEdgeCount [[1],[1,3,1],[2]]) [] := certificate_2168_checked

theorem certificate_2169_checked : certificate_2169.Valid 16 8 15 certificate_2169_q certificate_2169_edges 7 4 [] := by decide +kernel
theorem certificate_2169_valid : certificate_2169.Valid 16 8 (patternOrder [[1],[2],[2],[2]]) (patternClique [[1],[2],[2],[2]]) (patternEdges [[1],[2],[2],[2]]) (patternAmount [[1],[2],[2],[2]]) (patternEdgeCount [[1],[2],[2],[2]]) [] := certificate_2169_checked

theorem certificate_2170_checked : certificate_2170.Valid 16 8 16 certificate_2170_q certificate_2170_edges 8 4 [] := by decide +kernel
theorem certificate_2170_valid : certificate_2170.Valid 16 8 (patternOrder [[1],[2],[2],[3]]) (patternClique [[1],[2],[2],[3]]) (patternEdges [[1],[2],[2],[3]]) (patternAmount [[1],[2],[2],[3]]) (patternEdgeCount [[1],[2],[2],[3]]) [] := certificate_2170_checked

theorem certificate_2171_checked : certificate_2171.Valid 16 8 16 certificate_2171_q certificate_2171_edges 8 5 [] := by decide +kernel
theorem certificate_2171_valid : certificate_2171.Valid 16 8 (patternOrder [[1],[2],[2,1,2]]) (patternClique [[1],[2],[2,1,2]]) (patternEdges [[1],[2],[2,1,2]]) (patternAmount [[1],[2],[2,1,2]]) (patternEdgeCount [[1],[2],[2,1,2]]) [] := certificate_2171_checked

theorem certificate_2172_checked : certificate_2172.Valid 16 8 16 certificate_2172_q certificate_2172_edges 8 6 [] := by decide +kernel
theorem certificate_2172_valid : certificate_2172.Valid 16 8 (patternOrder [[1],[2,1,1,1,2]]) (patternClique [[1],[2,1,1,1,2]]) (patternEdges [[1],[2,1,1,1,2]]) (patternAmount [[1],[2,1,1,1,2]]) (patternEdgeCount [[1],[2,1,1,1,2]]) [] := certificate_2172_checked

theorem certificate_2173_checked : certificate_2173.Valid 16 8 14 certificate_2173_q certificate_2173_edges 6 5 [] := by decide +kernel
theorem certificate_2173_valid : certificate_2173.Valid 16 8 (patternOrder [[1,1],[1,1],[2]]) (patternClique [[1,1],[1,1],[2]]) (patternEdges [[1,1],[1,1],[2]]) (patternAmount [[1,1],[1,1],[2]]) (patternEdgeCount [[1,1],[1,1],[2]]) [] := certificate_2173_checked

theorem certificate_2174_checked : certificate_2174.Valid 16 8 15 certificate_2174_q certificate_2174_edges 7 5 [] := by decide +kernel
theorem certificate_2174_valid : certificate_2174.Valid 16 8 (patternOrder [[1,1],[1,1],[3]]) (patternClique [[1,1],[1,1],[3]]) (patternEdges [[1,1],[1,1],[3]]) (patternAmount [[1,1],[1,1],[3]]) (patternEdgeCount [[1,1],[1,1],[3]]) [] := certificate_2174_checked

theorem certificate_2175_checked : certificate_2175.Valid 16 8 16 certificate_2175_q certificate_2175_edges 8 5 [] := by decide +kernel
theorem certificate_2175_valid : certificate_2175.Valid 16 8 (patternOrder [[1,1],[1,1],[4]]) (patternClique [[1,1],[1,1],[4]]) (patternEdges [[1,1],[1,1],[4]]) (patternAmount [[1,1],[1,1],[4]]) (patternEdgeCount [[1,1],[1,1],[4]]) [] := certificate_2175_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates069
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2176_checked : certificate_2176.Valid 16 8 14 certificate_2176_q certificate_2176_edges 6 6 [] := by decide +kernel
theorem certificate_2176_valid : certificate_2176.Valid 16 8 (patternOrder [[1,1],[1,1,1,1]]) (patternClique [[1,1],[1,1,1,1]]) (patternEdges [[1,1],[1,1,1,1]]) (patternAmount [[1,1],[1,1,1,1]]) (patternEdgeCount [[1,1],[1,1,1,1]]) [] := certificate_2176_checked

theorem certificate_2177_checked : certificate_2177.Valid 16 8 15 certificate_2177_q certificate_2177_edges 7 6 [] := by decide +kernel
theorem certificate_2177_valid : certificate_2177.Valid 16 8 (patternOrder [[1,1],[1,1,1,2]]) (patternClique [[1,1],[1,1,1,2]]) (patternEdges [[1,1],[1,1,1,2]]) (patternAmount [[1,1],[1,1,1,2]]) (patternEdgeCount [[1,1],[1,1,1,2]]) [] := certificate_2177_checked

theorem certificate_2178_checked : certificate_2178.Valid 16 8 16 certificate_2178_q certificate_2178_edges 8 6 [] := by decide +kernel
theorem certificate_2178_valid : certificate_2178.Valid 16 8 (patternOrder [[1,1],[1,1,1,3]]) (patternClique [[1,1],[1,1,1,3]]) (patternEdges [[1,1],[1,1,1,3]]) (patternAmount [[1,1],[1,1,1,3]]) (patternEdgeCount [[1,1],[1,1,1,3]]) [] := certificate_2178_checked

theorem certificate_2179_checked : certificate_2179.Valid 16 8 15 certificate_2179_q certificate_2179_edges 7 6 [] := by decide +kernel
theorem certificate_2179_valid : certificate_2179.Valid 16 8 (patternOrder [[1,1],[1,1,2,1]]) (patternClique [[1,1],[1,1,2,1]]) (patternEdges [[1,1],[1,1,2,1]]) (patternAmount [[1,1],[1,1,2,1]]) (patternEdgeCount [[1,1],[1,1,2,1]]) [] := certificate_2179_checked

theorem certificate_2180_checked : certificate_2180.Valid 16 8 16 certificate_2180_q certificate_2180_edges 8 6 [] := by decide +kernel
theorem certificate_2180_valid : certificate_2180.Valid 16 8 (patternOrder [[1,1],[1,1,2,2]]) (patternClique [[1,1],[1,1,2,2]]) (patternEdges [[1,1],[1,1,2,2]]) (patternAmount [[1,1],[1,1,2,2]]) (patternEdgeCount [[1,1],[1,1,2,2]]) [] := certificate_2180_checked

theorem certificate_2181_checked : certificate_2181.Valid 16 8 16 certificate_2181_q certificate_2181_edges 8 6 [] := by decide +kernel
theorem certificate_2181_valid : certificate_2181.Valid 16 8 (patternOrder [[1,1],[1,1,3,1]]) (patternClique [[1,1],[1,1,3,1]]) (patternEdges [[1,1],[1,1,3,1]]) (patternAmount [[1,1],[1,1,3,1]]) (patternEdgeCount [[1,1],[1,1,3,1]]) [] := certificate_2181_checked

theorem certificate_2182_checked : certificate_2182.Valid 16 8 15 certificate_2182_q certificate_2182_edges 7 5 [] := by decide +kernel
theorem certificate_2182_valid : certificate_2182.Valid 16 8 (patternOrder [[1,1],[1,2],[2]]) (patternClique [[1,1],[1,2],[2]]) (patternEdges [[1,1],[1,2],[2]]) (patternAmount [[1,1],[1,2],[2]]) (patternEdgeCount [[1,1],[1,2],[2]]) [] := certificate_2182_checked

theorem certificate_2183_checked : certificate_2183.Valid 16 8 16 certificate_2183_q certificate_2183_edges 8 5 [] := by decide +kernel
theorem certificate_2183_valid : certificate_2183.Valid 16 8 (patternOrder [[1,1],[1,2],[3]]) (patternClique [[1,1],[1,2],[3]]) (patternEdges [[1,1],[1,2],[3]]) (patternAmount [[1,1],[1,2],[3]]) (patternEdgeCount [[1,1],[1,2],[3]]) [] := certificate_2183_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns16x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_16_8_26_verified_oai : ∀ D ∈ patterns_16_8_26, PatternVerified 16 8 D := by

  simp only [patterns_16_8_26, List.forall_mem_cons]

  exact ⟨⟨certificate_2168, certificate_2168_valid⟩, ⟨⟨certificate_2169, certificate_2169_valid⟩, ⟨⟨certificate_2170, certificate_2170_valid⟩, ⟨⟨certificate_2171, certificate_2171_valid⟩, ⟨⟨certificate_2172, certificate_2172_valid⟩, ⟨⟨certificate_2173, certificate_2173_valid⟩, ⟨⟨certificate_2174, certificate_2174_valid⟩, ⟨⟨certificate_2175, certificate_2175_valid⟩, ⟨⟨certificate_2176, certificate_2176_valid⟩, ⟨⟨certificate_2177, certificate_2177_valid⟩, ⟨⟨certificate_2178, certificate_2178_valid⟩, ⟨⟨certificate_2179, certificate_2179_valid⟩, ⟨⟨certificate_2180, certificate_2180_valid⟩, ⟨⟨certificate_2181, certificate_2181_valid⟩, ⟨⟨certificate_2182, certificate_2182_valid⟩, ⟨⟨certificate_2183, certificate_2183_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_26_verified_oai := @OAI.CycleClique.patterns_16_8_26_verified_oai
