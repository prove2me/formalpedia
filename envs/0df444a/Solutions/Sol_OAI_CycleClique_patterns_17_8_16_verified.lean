-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_16_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:07:16.438988+00:00
-- url     : https://prove2.me/submissions/3aefa69c-de08-4d88-819a-2d13b4da97bc

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates078
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2476_checked : certificate_2476.Valid 17 8 16 certificate_2476_q certificate_2476_edges 8 4 [] := by decide +kernel
theorem certificate_2476_valid : certificate_2476.Valid 17 8 (patternOrder [[],[],[1],[2,3,2]]) (patternClique [[],[],[1],[2,3,2]]) (patternEdges [[],[],[1],[2,3,2]]) (patternAmount [[],[],[1],[2,3,2]]) (patternEdgeCount [[],[],[1],[2,3,2]]) [] := certificate_2476_checked

theorem certificate_2477_checked : certificate_2477.Valid 17 8 17 certificate_2477_q certificate_2477_edges 9 4 [] := by decide +kernel
theorem certificate_2477_valid : certificate_2477.Valid 17 8 (patternOrder [[],[],[1],[2,3,3]]) (patternClique [[],[],[1],[2,3,3]]) (patternEdges [[],[],[1],[2,3,3]]) (patternAmount [[],[],[1],[2,3,3]]) (patternEdgeCount [[],[],[1],[2,3,3]]) [] := certificate_2477_checked

theorem certificate_2478_checked : certificate_2478.Valid 17 8 17 certificate_2478_q certificate_2478_edges 9 4 [] := by decide +kernel
theorem certificate_2478_valid : certificate_2478.Valid 17 8 (patternOrder [[],[],[1],[2,4,2]]) (patternClique [[],[],[1],[2,4,2]]) (patternEdges [[],[],[1],[2,4,2]]) (patternAmount [[],[],[1],[2,4,2]]) (patternEdgeCount [[],[],[1],[2,4,2]]) [] := certificate_2478_checked

theorem certificate_2479_checked : certificate_2479.Valid 17 8 15 certificate_2479_q certificate_2479_edges 7 3 [] := by decide +kernel
theorem certificate_2479_valid : certificate_2479.Valid 17 8 (patternOrder [[],[],[1],[3],[3]]) (patternClique [[],[],[1],[3],[3]]) (patternEdges [[],[],[1],[3],[3]]) (patternAmount [[],[],[1],[3],[3]]) (patternEdgeCount [[],[],[1],[3],[3]]) [] := certificate_2479_checked

theorem certificate_2480_checked : certificate_2480.Valid 17 8 16 certificate_2480_q certificate_2480_edges 8 3 [] := by decide +kernel
theorem certificate_2480_valid : certificate_2480.Valid 17 8 (patternOrder [[],[],[1],[3],[4]]) (patternClique [[],[],[1],[3],[4]]) (patternEdges [[],[],[1],[3],[4]]) (patternAmount [[],[],[1],[3],[4]]) (patternEdgeCount [[],[],[1],[3],[4]]) [] := certificate_2480_checked

theorem certificate_2481_checked : certificate_2481.Valid 17 8 17 certificate_2481_q certificate_2481_edges 9 3 [] := by decide +kernel
theorem certificate_2481_valid : certificate_2481.Valid 17 8 (patternOrder [[],[],[1],[3],[5]]) (patternClique [[],[],[1],[3],[5]]) (patternEdges [[],[],[1],[3],[5]]) (patternAmount [[],[],[1],[3],[5]]) (patternEdgeCount [[],[],[1],[3],[5]]) [] := certificate_2481_checked

theorem certificate_2482_checked : certificate_2482.Valid 17 8 16 certificate_2482_q certificate_2482_edges 8 4 [] := by decide +kernel
theorem certificate_2482_valid : certificate_2482.Valid 17 8 (patternOrder [[],[],[1],[3,1,3]]) (patternClique [[],[],[1],[3,1,3]]) (patternEdges [[],[],[1],[3,1,3]]) (patternAmount [[],[],[1],[3,1,3]]) (patternEdgeCount [[],[],[1],[3,1,3]]) [] := certificate_2482_checked

theorem certificate_2483_checked : certificate_2483.Valid 17 8 17 certificate_2483_q certificate_2483_edges 9 4 [] := by decide +kernel
theorem certificate_2483_valid : certificate_2483.Valid 17 8 (patternOrder [[],[],[1],[3,1,4]]) (patternClique [[],[],[1],[3,1,4]]) (patternEdges [[],[],[1],[3,1,4]]) (patternAmount [[],[],[1],[3,1,4]]) (patternEdgeCount [[],[],[1],[3,1,4]]) [] := certificate_2483_checked

theorem certificate_2484_checked : certificate_2484.Valid 17 8 17 certificate_2484_q certificate_2484_edges 9 4 [] := by decide +kernel
theorem certificate_2484_valid : certificate_2484.Valid 17 8 (patternOrder [[],[],[1],[3,2,3]]) (patternClique [[],[],[1],[3,2,3]]) (patternEdges [[],[],[1],[3,2,3]]) (patternAmount [[],[],[1],[3,2,3]]) (patternEdgeCount [[],[],[1],[3,2,3]]) [] := certificate_2484_checked

theorem certificate_2485_checked : certificate_2485.Valid 17 8 17 certificate_2485_q certificate_2485_edges 9 3 [] := by decide +kernel
theorem certificate_2485_valid : certificate_2485.Valid 17 8 (patternOrder [[],[],[1],[4],[4]]) (patternClique [[],[],[1],[4],[4]]) (patternEdges [[],[],[1],[4],[4]]) (patternAmount [[],[],[1],[4],[4]]) (patternEdgeCount [[],[],[1],[4],[4]]) [] := certificate_2485_checked

theorem certificate_2486_checked : certificate_2486.Valid 17 8 12 certificate_2486_q certificate_2486_edges 4 4 [] := by decide +kernel
theorem certificate_2486_valid : certificate_2486.Valid 17 8 (patternOrder [[],[],[1,1],[1,1]]) (patternClique [[],[],[1,1],[1,1]]) (patternEdges [[],[],[1,1],[1,1]]) (patternAmount [[],[],[1,1],[1,1]]) (patternEdgeCount [[],[],[1,1],[1,1]]) [] := certificate_2486_checked

theorem certificate_2487_checked : certificate_2487.Valid 17 8 13 certificate_2487_q certificate_2487_edges 5 4 [] := by decide +kernel
theorem certificate_2487_valid : certificate_2487.Valid 17 8 (patternOrder [[],[],[1,1],[1,2]]) (patternClique [[],[],[1,1],[1,2]]) (patternEdges [[],[],[1,1],[1,2]]) (patternAmount [[],[],[1,1],[1,2]]) (patternEdgeCount [[],[],[1,1],[1,2]]) [] := certificate_2487_checked

theorem certificate_2488_checked : certificate_2488.Valid 17 8 14 certificate_2488_q certificate_2488_edges 6 4 [] := by decide +kernel
theorem certificate_2488_valid : certificate_2488.Valid 17 8 (patternOrder [[],[],[1,1],[1,3]]) (patternClique [[],[],[1,1],[1,3]]) (patternEdges [[],[],[1,1],[1,3]]) (patternAmount [[],[],[1,1],[1,3]]) (patternEdgeCount [[],[],[1,1],[1,3]]) [] := certificate_2488_checked

theorem certificate_2489_checked : certificate_2489.Valid 17 8 15 certificate_2489_q certificate_2489_edges 7 4 [] := by decide +kernel
theorem certificate_2489_valid : certificate_2489.Valid 17 8 (patternOrder [[],[],[1,1],[1,4]]) (patternClique [[],[],[1,1],[1,4]]) (patternEdges [[],[],[1,1],[1,4]]) (patternAmount [[],[],[1,1],[1,4]]) (patternEdgeCount [[],[],[1,1],[1,4]]) [] := certificate_2489_checked

theorem certificate_2490_checked : certificate_2490.Valid 17 8 16 certificate_2490_q certificate_2490_edges 8 4 [] := by decide +kernel
theorem certificate_2490_valid : certificate_2490.Valid 17 8 (patternOrder [[],[],[1,1],[1,5]]) (patternClique [[],[],[1,1],[1,5]]) (patternEdges [[],[],[1,1],[1,5]]) (patternAmount [[],[],[1,1],[1,5]]) (patternEdgeCount [[],[],[1,1],[1,5]]) [] := certificate_2490_checked

theorem certificate_2491_checked : certificate_2491.Valid 17 8 17 certificate_2491_q certificate_2491_edges 9 4 [] := by decide +kernel
theorem certificate_2491_valid : certificate_2491.Valid 17 8 (patternOrder [[],[],[1,1],[1,6]]) (patternClique [[],[],[1,1],[1,6]]) (patternEdges [[],[],[1,1],[1,6]]) (patternAmount [[],[],[1,1],[1,6]]) (patternEdgeCount [[],[],[1,1],[1,6]]) [] := certificate_2491_checked

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

theorem patterns_17_8_16_verified_oai : ∀ D ∈ patterns_17_8_16, PatternVerified 17 8 D := by

  simp only [patterns_17_8_16, List.forall_mem_cons]

  exact ⟨⟨certificate_2476, certificate_2476_valid⟩, ⟨⟨certificate_2477, certificate_2477_valid⟩, ⟨⟨certificate_2478, certificate_2478_valid⟩, ⟨⟨certificate_2479, certificate_2479_valid⟩, ⟨⟨certificate_2480, certificate_2480_valid⟩, ⟨⟨certificate_2481, certificate_2481_valid⟩, ⟨⟨certificate_2482, certificate_2482_valid⟩, ⟨⟨certificate_2483, certificate_2483_valid⟩, ⟨⟨certificate_2484, certificate_2484_valid⟩, ⟨⟨certificate_2485, certificate_2485_valid⟩, ⟨⟨certificate_2486, certificate_2486_valid⟩, ⟨⟨certificate_2487, certificate_2487_valid⟩, ⟨⟨certificate_2488, certificate_2488_valid⟩, ⟨⟨certificate_2489, certificate_2489_valid⟩, ⟨⟨certificate_2490, certificate_2490_valid⟩, ⟨⟨certificate_2491, certificate_2491_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_16_verified_oai := @OAI.CycleClique.patterns_17_8_16_verified_oai
