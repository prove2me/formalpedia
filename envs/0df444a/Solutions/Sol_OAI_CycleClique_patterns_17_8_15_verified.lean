-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_15_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:06:32.35046+00:00
-- url     : https://prove2.me/submissions/e558b5a5-de08-4e28-abe9-8c3a451a2ee8

import Mathlib
import Definitions.Def_OAIQ107D080
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates077
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2460_checked : certificate_2460.Valid 17 8 17 certificate_2460_q certificate_2460_edges 9 4 [] := by decide +kernel
theorem certificate_2460_valid : certificate_2460.Valid 17 8 (patternOrder [[],[],[1],[1,4,3]]) (patternClique [[],[],[1],[1,4,3]]) (patternEdges [[],[],[1],[1,4,3]]) (patternAmount [[],[],[1],[1,4,3]]) (patternEdgeCount [[],[],[1],[1,4,3]]) [] := certificate_2460_checked

theorem certificate_2461_checked : certificate_2461.Valid 17 8 16 certificate_2461_q certificate_2461_edges 8 4 [] := by decide +kernel
theorem certificate_2461_valid : certificate_2461.Valid 17 8 (patternOrder [[],[],[1],[1,5,1]]) (patternClique [[],[],[1],[1,5,1]]) (patternEdges [[],[],[1],[1,5,1]]) (patternAmount [[],[],[1],[1,5,1]]) (patternEdgeCount [[],[],[1],[1,5,1]]) [] := certificate_2461_checked

theorem certificate_2462_checked : certificate_2462.Valid 17 8 17 certificate_2462_q certificate_2462_edges 9 4 [] := by decide +kernel
theorem certificate_2462_valid : certificate_2462.Valid 17 8 (patternOrder [[],[],[1],[1,5,2]]) (patternClique [[],[],[1],[1,5,2]]) (patternEdges [[],[],[1],[1,5,2]]) (patternAmount [[],[],[1],[1,5,2]]) (patternEdgeCount [[],[],[1],[1,5,2]]) [] := certificate_2462_checked

theorem certificate_2463_checked : certificate_2463.Valid 17 8 17 certificate_2463_q certificate_2463_edges 9 4 [] := by decide +kernel
theorem certificate_2463_valid : certificate_2463.Valid 17 8 (patternOrder [[],[],[1],[1,6,1]]) (patternClique [[],[],[1],[1,6,1]]) (patternEdges [[],[],[1],[1,6,1]]) (patternAmount [[],[],[1],[1,6,1]]) (patternEdgeCount [[],[],[1],[1,6,1]]) [] := certificate_2463_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates078
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2464_checked : certificate_2464.Valid 17 8 13 certificate_2464_q certificate_2464_edges 5 3 [] := by decide +kernel
theorem certificate_2464_valid : certificate_2464.Valid 17 8 (patternOrder [[],[],[1],[2],[2]]) (patternClique [[],[],[1],[2],[2]]) (patternEdges [[],[],[1],[2],[2]]) (patternAmount [[],[],[1],[2],[2]]) (patternEdgeCount [[],[],[1],[2],[2]]) [] := certificate_2464_checked

theorem certificate_2465_checked : certificate_2465.Valid 17 8 14 certificate_2465_q certificate_2465_edges 6 3 [] := by decide +kernel
theorem certificate_2465_valid : certificate_2465.Valid 17 8 (patternOrder [[],[],[1],[2],[3]]) (patternClique [[],[],[1],[2],[3]]) (patternEdges [[],[],[1],[2],[3]]) (patternAmount [[],[],[1],[2],[3]]) (patternEdgeCount [[],[],[1],[2],[3]]) [] := certificate_2465_checked

theorem certificate_2466_checked : certificate_2466.Valid 17 8 15 certificate_2466_q certificate_2466_edges 7 3 [] := by decide +kernel
theorem certificate_2466_valid : certificate_2466.Valid 17 8 (patternOrder [[],[],[1],[2],[4]]) (patternClique [[],[],[1],[2],[4]]) (patternEdges [[],[],[1],[2],[4]]) (patternAmount [[],[],[1],[2],[4]]) (patternEdgeCount [[],[],[1],[2],[4]]) [] := certificate_2466_checked

theorem certificate_2467_checked : certificate_2467.Valid 17 8 16 certificate_2467_q certificate_2467_edges 8 3 [] := by decide +kernel
theorem certificate_2467_valid : certificate_2467.Valid 17 8 (patternOrder [[],[],[1],[2],[5]]) (patternClique [[],[],[1],[2],[5]]) (patternEdges [[],[],[1],[2],[5]]) (patternAmount [[],[],[1],[2],[5]]) (patternEdgeCount [[],[],[1],[2],[5]]) [] := certificate_2467_checked

theorem certificate_2468_checked : certificate_2468.Valid 17 8 17 certificate_2468_q certificate_2468_edges 9 3 [] := by decide +kernel
theorem certificate_2468_valid : certificate_2468.Valid 17 8 (patternOrder [[],[],[1],[2],[6]]) (patternClique [[],[],[1],[2],[6]]) (patternEdges [[],[],[1],[2],[6]]) (patternAmount [[],[],[1],[2],[6]]) (patternEdgeCount [[],[],[1],[2],[6]]) [] := certificate_2468_checked

theorem certificate_2469_checked : certificate_2469.Valid 17 8 14 certificate_2469_q certificate_2469_edges 6 4 [] := by decide +kernel
theorem certificate_2469_valid : certificate_2469.Valid 17 8 (patternOrder [[],[],[1],[2,1,2]]) (patternClique [[],[],[1],[2,1,2]]) (patternEdges [[],[],[1],[2,1,2]]) (patternAmount [[],[],[1],[2,1,2]]) (patternEdgeCount [[],[],[1],[2,1,2]]) [] := certificate_2469_checked

theorem certificate_2470_checked : certificate_2470.Valid 17 8 15 certificate_2470_q certificate_2470_edges 7 4 [] := by decide +kernel
theorem certificate_2470_valid : certificate_2470.Valid 17 8 (patternOrder [[],[],[1],[2,1,3]]) (patternClique [[],[],[1],[2,1,3]]) (patternEdges [[],[],[1],[2,1,3]]) (patternAmount [[],[],[1],[2,1,3]]) (patternEdgeCount [[],[],[1],[2,1,3]]) [] := certificate_2470_checked

theorem certificate_2471_checked : certificate_2471.Valid 17 8 16 certificate_2471_q certificate_2471_edges 8 4 [] := by decide +kernel
theorem certificate_2471_valid : certificate_2471.Valid 17 8 (patternOrder [[],[],[1],[2,1,4]]) (patternClique [[],[],[1],[2,1,4]]) (patternEdges [[],[],[1],[2,1,4]]) (patternAmount [[],[],[1],[2,1,4]]) (patternEdgeCount [[],[],[1],[2,1,4]]) [] := certificate_2471_checked

theorem certificate_2472_checked : certificate_2472.Valid 17 8 17 certificate_2472_q certificate_2472_edges 9 4 [] := by decide +kernel
theorem certificate_2472_valid : certificate_2472.Valid 17 8 (patternOrder [[],[],[1],[2,1,5]]) (patternClique [[],[],[1],[2,1,5]]) (patternEdges [[],[],[1],[2,1,5]]) (patternAmount [[],[],[1],[2,1,5]]) (patternEdgeCount [[],[],[1],[2,1,5]]) [] := certificate_2472_checked

theorem certificate_2473_checked : certificate_2473.Valid 17 8 15 certificate_2473_q certificate_2473_edges 7 4 [] := by decide +kernel
theorem certificate_2473_valid : certificate_2473.Valid 17 8 (patternOrder [[],[],[1],[2,2,2]]) (patternClique [[],[],[1],[2,2,2]]) (patternEdges [[],[],[1],[2,2,2]]) (patternAmount [[],[],[1],[2,2,2]]) (patternEdgeCount [[],[],[1],[2,2,2]]) [] := certificate_2473_checked

theorem certificate_2474_checked : certificate_2474.Valid 17 8 16 certificate_2474_q certificate_2474_edges 8 4 [] := by decide +kernel
theorem certificate_2474_valid : certificate_2474.Valid 17 8 (patternOrder [[],[],[1],[2,2,3]]) (patternClique [[],[],[1],[2,2,3]]) (patternEdges [[],[],[1],[2,2,3]]) (patternAmount [[],[],[1],[2,2,3]]) (patternEdgeCount [[],[],[1],[2,2,3]]) [] := certificate_2474_checked

theorem certificate_2475_checked : certificate_2475.Valid 17 8 17 certificate_2475_q certificate_2475_edges 9 4 [] := by decide +kernel
theorem certificate_2475_valid : certificate_2475.Valid 17 8 (patternOrder [[],[],[1],[2,2,4]]) (patternClique [[],[],[1],[2,2,4]]) (patternEdges [[],[],[1],[2,2,4]]) (patternAmount [[],[],[1],[2,2,4]]) (patternEdgeCount [[],[],[1],[2,2,4]]) [] := certificate_2475_checked

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

theorem patterns_17_8_15_verified_oai : ∀ D ∈ patterns_17_8_15, PatternVerified 17 8 D := by

  simp only [patterns_17_8_15, List.forall_mem_cons]

  exact ⟨⟨certificate_2460, certificate_2460_valid⟩, ⟨⟨certificate_2461, certificate_2461_valid⟩, ⟨⟨certificate_2462, certificate_2462_valid⟩, ⟨⟨certificate_2463, certificate_2463_valid⟩, ⟨⟨certificate_2464, certificate_2464_valid⟩, ⟨⟨certificate_2465, certificate_2465_valid⟩, ⟨⟨certificate_2466, certificate_2466_valid⟩, ⟨⟨certificate_2467, certificate_2467_valid⟩, ⟨⟨certificate_2468, certificate_2468_valid⟩, ⟨⟨certificate_2469, certificate_2469_valid⟩, ⟨⟨certificate_2470, certificate_2470_valid⟩, ⟨⟨certificate_2471, certificate_2471_valid⟩, ⟨⟨certificate_2472, certificate_2472_valid⟩, ⟨⟨certificate_2473, certificate_2473_valid⟩, ⟨⟨certificate_2474, certificate_2474_valid⟩, ⟨⟨certificate_2475, certificate_2475_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_15_verified_oai := @OAI.CycleClique.patterns_17_8_15_verified_oai
