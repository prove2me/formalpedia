-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_21_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:44:30.17002+00:00
-- url     : https://prove2.me/submissions/a718b765-5afa-48ea-860d-26463674fc3b

import Mathlib
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates066
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2088_checked : certificate_2088.Valid 16 8 16 certificate_2088_q certificate_2088_edges 8 6 [] := by decide +kernel
theorem certificate_2088_valid : certificate_2088.Valid 16 8 (patternOrder [[],[1,1,1,3,1,1]]) (patternClique [[],[1,1,1,3,1,1]]) (patternEdges [[],[1,1,1,3,1,1]]) (patternAmount [[],[1,1,1,3,1,1]]) (patternEdgeCount [[],[1,1,1,3,1,1]]) [] := certificate_2088_checked

theorem certificate_2089_checked : certificate_2089.Valid 16 8 15 certificate_2089_q certificate_2089_edges 7 5 [] := by decide +kernel
theorem certificate_2089_valid : certificate_2089.Valid 16 8 (patternOrder [[],[1,1,2],[1,2]]) (patternClique [[],[1,1,2],[1,2]]) (patternEdges [[],[1,1,2],[1,2]]) (patternAmount [[],[1,1,2],[1,2]]) (patternEdgeCount [[],[1,1,2],[1,2]]) [] := certificate_2089_checked

theorem certificate_2090_checked : certificate_2090.Valid 16 8 16 certificate_2090_q certificate_2090_edges 8 5 [] := by decide +kernel
theorem certificate_2090_valid : certificate_2090.Valid 16 8 (patternOrder [[],[1,1,2],[1,3]]) (patternClique [[],[1,1,2],[1,3]]) (patternEdges [[],[1,1,2],[1,3]]) (patternAmount [[],[1,1,2],[1,3]]) (patternEdgeCount [[],[1,1,2],[1,3]]) [] := certificate_2090_checked

theorem certificate_2091_checked : certificate_2091.Valid 16 8 16 certificate_2091_q certificate_2091_edges 8 5 [] := by decide +kernel
theorem certificate_2091_valid : certificate_2091.Valid 16 8 (patternOrder [[],[1,1,2],[2,2]]) (patternClique [[],[1,1,2],[2,2]]) (patternEdges [[],[1,1,2],[2,2]]) (patternAmount [[],[1,1,2],[2,2]]) (patternEdgeCount [[],[1,1,2],[2,2]]) [] := certificate_2091_checked

theorem certificate_2092_checked : certificate_2092.Valid 16 8 15 certificate_2092_q certificate_2092_edges 7 5 [] := by decide +kernel
theorem certificate_2092_valid : certificate_2092.Valid 16 8 (patternOrder [[],[1,1,2,1],[2]]) (patternClique [[],[1,1,2,1],[2]]) (patternEdges [[],[1,1,2,1],[2]]) (patternAmount [[],[1,1,2,1],[2]]) (patternEdgeCount [[],[1,1,2,1],[2]]) [] := certificate_2092_checked

theorem certificate_2093_checked : certificate_2093.Valid 16 8 16 certificate_2093_q certificate_2093_edges 8 5 [] := by decide +kernel
theorem certificate_2093_valid : certificate_2093.Valid 16 8 (patternOrder [[],[1,1,2,1],[3]]) (patternClique [[],[1,1,2,1],[3]]) (patternEdges [[],[1,1,2,1],[3]]) (patternAmount [[],[1,1,2,1],[3]]) (patternEdgeCount [[],[1,1,2,1],[3]]) [] := certificate_2093_checked

theorem certificate_2094_checked : certificate_2094.Valid 16 8 16 certificate_2094_q certificate_2094_edges 8 6 [] := by decide +kernel
theorem certificate_2094_valid : certificate_2094.Valid 16 8 (patternOrder [[],[1,1,2,1,1,2]]) (patternClique [[],[1,1,2,1,1,2]]) (patternEdges [[],[1,1,2,1,1,2]]) (patternAmount [[],[1,1,2,1,1,2]]) (patternEdgeCount [[],[1,1,2,1,1,2]]) [] := certificate_2094_checked

theorem certificate_2095_checked : certificate_2095.Valid 16 8 16 certificate_2095_q certificate_2095_edges 8 6 [] := by decide +kernel
theorem certificate_2095_valid : certificate_2095.Valid 16 8 (patternOrder [[],[1,1,2,1,2,1]]) (patternClique [[],[1,1,2,1,2,1]]) (patternEdges [[],[1,1,2,1,2,1]]) (patternAmount [[],[1,1,2,1,2,1]]) (patternEdgeCount [[],[1,1,2,1,2,1]]) [] := certificate_2095_checked

theorem certificate_2096_checked : certificate_2096.Valid 16 8 16 certificate_2096_q certificate_2096_edges 8 5 [] := by decide +kernel
theorem certificate_2096_valid : certificate_2096.Valid 16 8 (patternOrder [[],[1,1,2,2],[2]]) (patternClique [[],[1,1,2,2],[2]]) (patternEdges [[],[1,1,2,2],[2]]) (patternAmount [[],[1,1,2,2],[2]]) (patternEdgeCount [[],[1,1,2,2],[2]]) [] := certificate_2096_checked

theorem certificate_2097_checked : certificate_2097.Valid 16 8 16 certificate_2097_q certificate_2097_edges 8 6 [] := by decide +kernel
theorem certificate_2097_valid : certificate_2097.Valid 16 8 (patternOrder [[],[1,1,2,2,1,1]]) (patternClique [[],[1,1,2,2,1,1]]) (patternEdges [[],[1,1,2,2,1,1]]) (patternAmount [[],[1,1,2,2,1,1]]) (patternEdgeCount [[],[1,1,2,2,1,1]]) [] := certificate_2097_checked

theorem certificate_2098_checked : certificate_2098.Valid 16 8 16 certificate_2098_q certificate_2098_edges 8 5 [] := by decide +kernel
theorem certificate_2098_valid : certificate_2098.Valid 16 8 (patternOrder [[],[1,1,3],[1,2]]) (patternClique [[],[1,1,3],[1,2]]) (patternEdges [[],[1,1,3],[1,2]]) (patternAmount [[],[1,1,3],[1,2]]) (patternEdgeCount [[],[1,1,3],[1,2]]) [] := certificate_2098_checked

theorem certificate_2099_checked : certificate_2099.Valid 16 8 16 certificate_2099_q certificate_2099_edges 8 5 [] := by decide +kernel
theorem certificate_2099_valid : certificate_2099.Valid 16 8 (patternOrder [[],[1,1,3,1],[2]]) (patternClique [[],[1,1,3,1],[2]]) (patternEdges [[],[1,1,3,1],[2]]) (patternAmount [[],[1,1,3,1],[2]]) (patternEdgeCount [[],[1,1,3,1],[2]]) [] := certificate_2099_checked

theorem certificate_2100_checked : certificate_2100.Valid 16 8 15 certificate_2100_q certificate_2100_edges 7 5 [] := by decide +kernel
theorem certificate_2100_valid : certificate_2100.Valid 16 8 (patternOrder [[],[1,2],[1,2,1]]) (patternClique [[],[1,2],[1,2,1]]) (patternEdges [[],[1,2],[1,2,1]]) (patternAmount [[],[1,2],[1,2,1]]) (patternEdgeCount [[],[1,2],[1,2,1]]) [] := certificate_2100_checked

theorem certificate_2101_checked : certificate_2101.Valid 16 8 16 certificate_2101_q certificate_2101_edges 8 5 [] := by decide +kernel
theorem certificate_2101_valid : certificate_2101.Valid 16 8 (patternOrder [[],[1,2],[1,2,2]]) (patternClique [[],[1,2],[1,2,2]]) (patternEdges [[],[1,2],[1,2,2]]) (patternAmount [[],[1,2],[1,2,2]]) (patternEdgeCount [[],[1,2],[1,2,2]]) [] := certificate_2101_checked

theorem certificate_2102_checked : certificate_2102.Valid 16 8 16 certificate_2102_q certificate_2102_edges 8 5 [] := by decide +kernel
theorem certificate_2102_valid : certificate_2102.Valid 16 8 (patternOrder [[],[1,2],[1,3,1]]) (patternClique [[],[1,2],[1,3,1]]) (patternEdges [[],[1,2],[1,3,1]]) (patternAmount [[],[1,2],[1,3,1]]) (patternEdgeCount [[],[1,2],[1,3,1]]) [] := certificate_2102_checked

theorem certificate_2103_checked : certificate_2103.Valid 16 8 15 certificate_2103_q certificate_2103_edges 7 4 [] := by decide +kernel
theorem certificate_2103_valid : certificate_2103.Valid 16 8 (patternOrder [[],[1,2],[2],[2]]) (patternClique [[],[1,2],[2],[2]]) (patternEdges [[],[1,2],[2],[2]]) (patternAmount [[],[1,2],[2],[2]]) (patternEdgeCount [[],[1,2],[2],[2]]) [] := certificate_2103_checked

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

theorem patterns_16_8_21_verified_oai : ∀ D ∈ patterns_16_8_21, PatternVerified 16 8 D := by

  simp only [patterns_16_8_21, List.forall_mem_cons]

  exact ⟨⟨certificate_2088, certificate_2088_valid⟩, ⟨⟨certificate_2089, certificate_2089_valid⟩, ⟨⟨certificate_2090, certificate_2090_valid⟩, ⟨⟨certificate_2091, certificate_2091_valid⟩, ⟨⟨certificate_2092, certificate_2092_valid⟩, ⟨⟨certificate_2093, certificate_2093_valid⟩, ⟨⟨certificate_2094, certificate_2094_valid⟩, ⟨⟨certificate_2095, certificate_2095_valid⟩, ⟨⟨certificate_2096, certificate_2096_valid⟩, ⟨⟨certificate_2097, certificate_2097_valid⟩, ⟨⟨certificate_2098, certificate_2098_valid⟩, ⟨⟨certificate_2099, certificate_2099_valid⟩, ⟨⟨certificate_2100, certificate_2100_valid⟩, ⟨⟨certificate_2101, certificate_2101_valid⟩, ⟨⟨certificate_2102, certificate_2102_valid⟩, ⟨⟨certificate_2103, certificate_2103_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_21_verified_oai := @OAI.CycleClique.patterns_16_8_21_verified_oai
