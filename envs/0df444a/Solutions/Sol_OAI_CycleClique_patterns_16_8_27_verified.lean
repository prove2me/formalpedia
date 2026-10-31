-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_27_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:48:32.778518+00:00
-- url     : https://prove2.me/submissions/0ef15431-658d-4d31-8260-b07dfd7164ce

import Mathlib
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates069
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2184_checked : certificate_2184.Valid 16 8 16 certificate_2184_q certificate_2184_edges 8 6 [] := by decide +kernel
theorem certificate_2184_valid : certificate_2184.Valid 16 8 (patternOrder [[1,1],[1,2,1,2]]) (patternClique [[1,1],[1,2,1,2]]) (patternEdges [[1,1],[1,2,1,2]]) (patternAmount [[1,1],[1,2,1,2]]) (patternEdgeCount [[1,1],[1,2,1,2]]) [] := certificate_2184_checked

theorem certificate_2185_checked : certificate_2185.Valid 16 8 16 certificate_2185_q certificate_2185_edges 8 6 [] := by decide +kernel
theorem certificate_2185_valid : certificate_2185.Valid 16 8 (patternOrder [[1,1],[1,2,2,1]]) (patternClique [[1,1],[1,2,2,1]]) (patternEdges [[1,1],[1,2,2,1]]) (patternAmount [[1,1],[1,2,2,1]]) (patternEdgeCount [[1,1],[1,2,2,1]]) [] := certificate_2185_checked

theorem certificate_2186_checked : certificate_2186.Valid 16 8 16 certificate_2186_q certificate_2186_edges 8 5 [] := by decide +kernel
theorem certificate_2186_valid : certificate_2186.Valid 16 8 (patternOrder [[1,1],[1,3],[2]]) (patternClique [[1,1],[1,3],[2]]) (patternEdges [[1,1],[1,3],[2]]) (patternAmount [[1,1],[1,3],[2]]) (patternEdgeCount [[1,1],[1,3],[2]]) [] := certificate_2186_checked

theorem certificate_2187_checked : certificate_2187.Valid 16 8 16 certificate_2187_q certificate_2187_edges 8 5 [] := by decide +kernel
theorem certificate_2187_valid : certificate_2187.Valid 16 8 (patternOrder [[1,1],[2],[2,2]]) (patternClique [[1,1],[2],[2,2]]) (patternEdges [[1,1],[2],[2,2]]) (patternAmount [[1,1],[2],[2,2]]) (patternEdgeCount [[1,1],[2],[2,2]]) [] := certificate_2187_checked

theorem certificate_2188_checked : certificate_2188.Valid 16 8 16 certificate_2188_q certificate_2188_edges 8 6 [] := by decide +kernel
theorem certificate_2188_valid : certificate_2188.Valid 16 8 (patternOrder [[1,1],[2,1,1,2]]) (patternClique [[1,1],[2,1,1,2]]) (patternEdges [[1,1],[2,1,1,2]]) (patternAmount [[1,1],[2,1,1,2]]) (patternEdgeCount [[1,1],[2,1,1,2]]) [] := certificate_2188_checked

theorem certificate_2189_checked : certificate_2189.Valid 16 8 14 certificate_2189_q certificate_2189_edges 6 6 [] := by decide +kernel
theorem certificate_2189_valid : certificate_2189.Valid 16 8 (patternOrder [[1,1,1],[1,1,1]]) (patternClique [[1,1,1],[1,1,1]]) (patternEdges [[1,1,1],[1,1,1]]) (patternAmount [[1,1,1],[1,1,1]]) (patternEdgeCount [[1,1,1],[1,1,1]]) [] := certificate_2189_checked

theorem certificate_2190_checked : certificate_2190.Valid 16 8 15 certificate_2190_q certificate_2190_edges 7 6 [] := by decide +kernel
theorem certificate_2190_valid : certificate_2190.Valid 16 8 (patternOrder [[1,1,1],[1,1,2]]) (patternClique [[1,1,1],[1,1,2]]) (patternEdges [[1,1,1],[1,1,2]]) (patternAmount [[1,1,1],[1,1,2]]) (patternEdgeCount [[1,1,1],[1,1,2]]) [] := certificate_2190_checked

theorem certificate_2191_checked : certificate_2191.Valid 16 8 16 certificate_2191_q certificate_2191_edges 8 6 [] := by decide +kernel
theorem certificate_2191_valid : certificate_2191.Valid 16 8 (patternOrder [[1,1,1],[1,1,3]]) (patternClique [[1,1,1],[1,1,3]]) (patternEdges [[1,1,1],[1,1,3]]) (patternAmount [[1,1,1],[1,1,3]]) (patternEdgeCount [[1,1,1],[1,1,3]]) [] := certificate_2191_checked

theorem certificate_2192_checked : certificate_2192.Valid 16 8 15 certificate_2192_q certificate_2192_edges 7 6 [] := by decide +kernel
theorem certificate_2192_valid : certificate_2192.Valid 16 8 (patternOrder [[1,1,1],[1,2,1]]) (patternClique [[1,1,1],[1,2,1]]) (patternEdges [[1,1,1],[1,2,1]]) (patternAmount [[1,1,1],[1,2,1]]) (patternEdgeCount [[1,1,1],[1,2,1]]) [] := certificate_2192_checked

theorem certificate_2193_checked : certificate_2193.Valid 16 8 16 certificate_2193_q certificate_2193_edges 8 6 [] := by decide +kernel
theorem certificate_2193_valid : certificate_2193.Valid 16 8 (patternOrder [[1,1,1],[1,2,2]]) (patternClique [[1,1,1],[1,2,2]]) (patternEdges [[1,1,1],[1,2,2]]) (patternAmount [[1,1,1],[1,2,2]]) (patternEdgeCount [[1,1,1],[1,2,2]]) [] := certificate_2193_checked

theorem certificate_2194_checked : certificate_2194.Valid 16 8 16 certificate_2194_q certificate_2194_edges 8 6 [] := by decide +kernel
theorem certificate_2194_valid : certificate_2194.Valid 16 8 (patternOrder [[1,1,1],[1,3,1]]) (patternClique [[1,1,1],[1,3,1]]) (patternEdges [[1,1,1],[1,3,1]]) (patternAmount [[1,1,1],[1,3,1]]) (patternEdgeCount [[1,1,1],[1,3,1]]) [] := certificate_2194_checked

theorem certificate_2195_checked : certificate_2195.Valid 16 8 15 certificate_2195_q certificate_2195_edges 7 5 [] := by decide +kernel
theorem certificate_2195_valid : certificate_2195.Valid 16 8 (patternOrder [[1,1,1],[2],[2]]) (patternClique [[1,1,1],[2],[2]]) (patternEdges [[1,1,1],[2],[2]]) (patternAmount [[1,1,1],[2],[2]]) (patternEdgeCount [[1,1,1],[2],[2]]) [] := certificate_2195_checked

theorem certificate_2196_checked : certificate_2196.Valid 16 8 16 certificate_2196_q certificate_2196_edges 8 5 [] := by decide +kernel
theorem certificate_2196_valid : certificate_2196.Valid 16 8 (patternOrder [[1,1,1],[2],[3]]) (patternClique [[1,1,1],[2],[3]]) (patternEdges [[1,1,1],[2],[3]]) (patternAmount [[1,1,1],[2],[3]]) (patternEdgeCount [[1,1,1],[2],[3]]) [] := certificate_2196_checked

theorem certificate_2197_checked : certificate_2197.Valid 16 8 16 certificate_2197_q certificate_2197_edges 8 6 [] := by decide +kernel
theorem certificate_2197_valid : certificate_2197.Valid 16 8 (patternOrder [[1,1,1],[2,1,2]]) (patternClique [[1,1,1],[2,1,2]]) (patternEdges [[1,1,1],[2,1,2]]) (patternAmount [[1,1,1],[2,1,2]]) (patternEdgeCount [[1,1,1],[2,1,2]]) [] := certificate_2197_checked

theorem certificate_2198_checked : certificate_2198.Valid 16 8 15 certificate_2198_q certificate_2198_edges 7 6 [] := by decide +kernel
theorem certificate_2198_valid : certificate_2198.Valid 16 8 (patternOrder [[1,1,1,1],[1,2]]) (patternClique [[1,1,1,1],[1,2]]) (patternEdges [[1,1,1,1],[1,2]]) (patternAmount [[1,1,1,1],[1,2]]) (patternEdgeCount [[1,1,1,1],[1,2]]) [] := certificate_2198_checked

theorem certificate_2199_checked : certificate_2199.Valid 16 8 16 certificate_2199_q certificate_2199_edges 8 6 [] := by decide +kernel
theorem certificate_2199_valid : certificate_2199.Valid 16 8 (patternOrder [[1,1,1,1],[1,3]]) (patternClique [[1,1,1,1],[1,3]]) (patternEdges [[1,1,1,1],[1,3]]) (patternAmount [[1,1,1,1],[1,3]]) (patternEdgeCount [[1,1,1,1],[1,3]]) [] := certificate_2199_checked

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

theorem patterns_16_8_27_verified_oai : ∀ D ∈ patterns_16_8_27, PatternVerified 16 8 D := by

  simp only [patterns_16_8_27, List.forall_mem_cons]

  exact ⟨⟨certificate_2184, certificate_2184_valid⟩, ⟨⟨certificate_2185, certificate_2185_valid⟩, ⟨⟨certificate_2186, certificate_2186_valid⟩, ⟨⟨certificate_2187, certificate_2187_valid⟩, ⟨⟨certificate_2188, certificate_2188_valid⟩, ⟨⟨certificate_2189, certificate_2189_valid⟩, ⟨⟨certificate_2190, certificate_2190_valid⟩, ⟨⟨certificate_2191, certificate_2191_valid⟩, ⟨⟨certificate_2192, certificate_2192_valid⟩, ⟨⟨certificate_2193, certificate_2193_valid⟩, ⟨⟨certificate_2194, certificate_2194_valid⟩, ⟨⟨certificate_2195, certificate_2195_valid⟩, ⟨⟨certificate_2196, certificate_2196_valid⟩, ⟨⟨certificate_2197, certificate_2197_valid⟩, ⟨⟨certificate_2198, certificate_2198_valid⟩, ⟨⟨certificate_2199, certificate_2199_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_27_verified_oai := @OAI.CycleClique.patterns_16_8_27_verified_oai
