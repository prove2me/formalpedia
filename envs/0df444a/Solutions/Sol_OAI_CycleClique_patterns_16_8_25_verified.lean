-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_25_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:45:37.115423+00:00
-- url     : https://prove2.me/submissions/316ab926-899a-4332-b65e-2318f00ba4e6

import Mathlib
import Definitions.Def_OAIQ107D068
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

theorem certificate_2152_checked : certificate_2152.Valid 16 8 16 certificate_2152_q certificate_2152_edges 8 6 [] := by decide +kernel
theorem certificate_2152_valid : certificate_2152.Valid 16 8 (patternOrder [[1],[1,1,1,3,1]]) (patternClique [[1],[1,1,1,3,1]]) (patternEdges [[1],[1,1,1,3,1]]) (patternAmount [[1],[1,1,1,3,1]]) (patternEdgeCount [[1],[1,1,1,3,1]]) [] := certificate_2152_checked

theorem certificate_2153_checked : certificate_2153.Valid 16 8 15 certificate_2153_q certificate_2153_edges 7 5 [] := by decide +kernel
theorem certificate_2153_valid : certificate_2153.Valid 16 8 (patternOrder [[1],[1,1,2],[2]]) (patternClique [[1],[1,1,2],[2]]) (patternEdges [[1],[1,1,2],[2]]) (patternAmount [[1],[1,1,2],[2]]) (patternEdgeCount [[1],[1,1,2],[2]]) [] := certificate_2153_checked

theorem certificate_2154_checked : certificate_2154.Valid 16 8 16 certificate_2154_q certificate_2154_edges 8 5 [] := by decide +kernel
theorem certificate_2154_valid : certificate_2154.Valid 16 8 (patternOrder [[1],[1,1,2],[3]]) (patternClique [[1],[1,1,2],[3]]) (patternEdges [[1],[1,1,2],[3]]) (patternAmount [[1],[1,1,2],[3]]) (patternEdgeCount [[1],[1,1,2],[3]]) [] := certificate_2154_checked

theorem certificate_2155_checked : certificate_2155.Valid 16 8 15 certificate_2155_q certificate_2155_edges 7 6 [] := by decide +kernel
theorem certificate_2155_valid : certificate_2155.Valid 16 8 (patternOrder [[1],[1,1,2,1,1]]) (patternClique [[1],[1,1,2,1,1]]) (patternEdges [[1],[1,1,2,1,1]]) (patternAmount [[1],[1,1,2,1,1]]) (patternEdgeCount [[1],[1,1,2,1,1]]) [] := certificate_2155_checked

theorem certificate_2156_checked : certificate_2156.Valid 16 8 16 certificate_2156_q certificate_2156_edges 8 6 [] := by decide +kernel
theorem certificate_2156_valid : certificate_2156.Valid 16 8 (patternOrder [[1],[1,1,2,1,2]]) (patternClique [[1],[1,1,2,1,2]]) (patternEdges [[1],[1,1,2,1,2]]) (patternAmount [[1],[1,1,2,1,2]]) (patternEdgeCount [[1],[1,1,2,1,2]]) [] := certificate_2156_checked

theorem certificate_2157_checked : certificate_2157.Valid 16 8 16 certificate_2157_q certificate_2157_edges 8 6 [] := by decide +kernel
theorem certificate_2157_valid : certificate_2157.Valid 16 8 (patternOrder [[1],[1,1,2,2,1]]) (patternClique [[1],[1,1,2,2,1]]) (patternEdges [[1],[1,1,2,2,1]]) (patternAmount [[1],[1,1,2,2,1]]) (patternEdgeCount [[1],[1,1,2,2,1]]) [] := certificate_2157_checked

theorem certificate_2158_checked : certificate_2158.Valid 16 8 16 certificate_2158_q certificate_2158_edges 8 5 [] := by decide +kernel
theorem certificate_2158_valid : certificate_2158.Valid 16 8 (patternOrder [[1],[1,1,3],[2]]) (patternClique [[1],[1,1,3],[2]]) (patternEdges [[1],[1,1,3],[2]]) (patternAmount [[1],[1,1,3],[2]]) (patternEdgeCount [[1],[1,1,3],[2]]) [] := certificate_2158_checked

theorem certificate_2159_checked : certificate_2159.Valid 16 8 16 certificate_2159_q certificate_2159_edges 8 6 [] := by decide +kernel
theorem certificate_2159_valid : certificate_2159.Valid 16 8 (patternOrder [[1],[1,1,3,1,1]]) (patternClique [[1],[1,1,3,1,1]]) (patternEdges [[1],[1,1,3,1,1]]) (patternAmount [[1],[1,1,3,1,1]]) (patternEdgeCount [[1],[1,1,3,1,1]]) [] := certificate_2159_checked

theorem certificate_2160_checked : certificate_2160.Valid 16 8 15 certificate_2160_q certificate_2160_edges 7 5 [] := by decide +kernel
theorem certificate_2160_valid : certificate_2160.Valid 16 8 (patternOrder [[1],[1,2],[1,2]]) (patternClique [[1],[1,2],[1,2]]) (patternEdges [[1],[1,2],[1,2]]) (patternAmount [[1],[1,2],[1,2]]) (patternEdgeCount [[1],[1,2],[1,2]]) [] := certificate_2160_checked

theorem certificate_2161_checked : certificate_2161.Valid 16 8 16 certificate_2161_q certificate_2161_edges 8 5 [] := by decide +kernel
theorem certificate_2161_valid : certificate_2161.Valid 16 8 (patternOrder [[1],[1,2],[1,3]]) (patternClique [[1],[1,2],[1,3]]) (patternEdges [[1],[1,2],[1,3]]) (patternAmount [[1],[1,2],[1,3]]) (patternEdgeCount [[1],[1,2],[1,3]]) [] := certificate_2161_checked

theorem certificate_2162_checked : certificate_2162.Valid 16 8 16 certificate_2162_q certificate_2162_edges 8 5 [] := by decide +kernel
theorem certificate_2162_valid : certificate_2162.Valid 16 8 (patternOrder [[1],[1,2],[2,2]]) (patternClique [[1],[1,2],[2,2]]) (patternEdges [[1],[1,2],[2,2]]) (patternAmount [[1],[1,2],[2,2]]) (patternEdgeCount [[1],[1,2],[2,2]]) [] := certificate_2162_checked

theorem certificate_2163_checked : certificate_2163.Valid 16 8 15 certificate_2163_q certificate_2163_edges 7 5 [] := by decide +kernel
theorem certificate_2163_valid : certificate_2163.Valid 16 8 (patternOrder [[1],[1,2,1],[2]]) (patternClique [[1],[1,2,1],[2]]) (patternEdges [[1],[1,2,1],[2]]) (patternAmount [[1],[1,2,1],[2]]) (patternEdgeCount [[1],[1,2,1],[2]]) [] := certificate_2163_checked

theorem certificate_2164_checked : certificate_2164.Valid 16 8 16 certificate_2164_q certificate_2164_edges 8 5 [] := by decide +kernel
theorem certificate_2164_valid : certificate_2164.Valid 16 8 (patternOrder [[1],[1,2,1],[3]]) (patternClique [[1],[1,2,1],[3]]) (patternEdges [[1],[1,2,1],[3]]) (patternAmount [[1],[1,2,1],[3]]) (patternEdgeCount [[1],[1,2,1],[3]]) [] := certificate_2164_checked

theorem certificate_2165_checked : certificate_2165.Valid 16 8 16 certificate_2165_q certificate_2165_edges 8 6 [] := by decide +kernel
theorem certificate_2165_valid : certificate_2165.Valid 16 8 (patternOrder [[1],[1,2,1,1,2]]) (patternClique [[1],[1,2,1,1,2]]) (patternEdges [[1],[1,2,1,1,2]]) (patternAmount [[1],[1,2,1,1,2]]) (patternEdgeCount [[1],[1,2,1,1,2]]) [] := certificate_2165_checked

theorem certificate_2166_checked : certificate_2166.Valid 16 8 16 certificate_2166_q certificate_2166_edges 8 6 [] := by decide +kernel
theorem certificate_2166_valid : certificate_2166.Valid 16 8 (patternOrder [[1],[1,2,1,2,1]]) (patternClique [[1],[1,2,1,2,1]]) (patternEdges [[1],[1,2,1,2,1]]) (patternAmount [[1],[1,2,1,2,1]]) (patternEdgeCount [[1],[1,2,1,2,1]]) [] := certificate_2166_checked

theorem certificate_2167_checked : certificate_2167.Valid 16 8 16 certificate_2167_q certificate_2167_edges 8 5 [] := by decide +kernel
theorem certificate_2167_valid : certificate_2167.Valid 16 8 (patternOrder [[1],[1,2,2],[2]]) (patternClique [[1],[1,2,2],[2]]) (patternEdges [[1],[1,2,2],[2]]) (patternAmount [[1],[1,2,2],[2]]) (patternEdgeCount [[1],[1,2,2],[2]]) [] := certificate_2167_checked

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

theorem patterns_16_8_25_verified_oai : ∀ D ∈ patterns_16_8_25, PatternVerified 16 8 D := by

  simp only [patterns_16_8_25, List.forall_mem_cons]

  exact ⟨⟨certificate_2152, certificate_2152_valid⟩, ⟨⟨certificate_2153, certificate_2153_valid⟩, ⟨⟨certificate_2154, certificate_2154_valid⟩, ⟨⟨certificate_2155, certificate_2155_valid⟩, ⟨⟨certificate_2156, certificate_2156_valid⟩, ⟨⟨certificate_2157, certificate_2157_valid⟩, ⟨⟨certificate_2158, certificate_2158_valid⟩, ⟨⟨certificate_2159, certificate_2159_valid⟩, ⟨⟨certificate_2160, certificate_2160_valid⟩, ⟨⟨certificate_2161, certificate_2161_valid⟩, ⟨⟨certificate_2162, certificate_2162_valid⟩, ⟨⟨certificate_2163, certificate_2163_valid⟩, ⟨⟨certificate_2164, certificate_2164_valid⟩, ⟨⟨certificate_2165, certificate_2165_valid⟩, ⟨⟨certificate_2166, certificate_2166_valid⟩, ⟨⟨certificate_2167, certificate_2167_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_25_verified_oai := @OAI.CycleClique.patterns_16_8_25_verified_oai
