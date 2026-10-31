-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_17_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:08:43.852178+00:00
-- url     : https://prove2.me/submissions/a5b2074f-1683-43dd-99ce-5e8c8dc36b43

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

theorem certificate_2492_checked : certificate_2492.Valid 17 8 14 certificate_2492_q certificate_2492_edges 6 4 [] := by decide +kernel
theorem certificate_2492_valid : certificate_2492.Valid 17 8 (patternOrder [[],[],[1,1],[2,2]]) (patternClique [[],[],[1,1],[2,2]]) (patternEdges [[],[],[1,1],[2,2]]) (patternAmount [[],[],[1,1],[2,2]]) (patternEdgeCount [[],[],[1,1],[2,2]]) [] := certificate_2492_checked

theorem certificate_2493_checked : certificate_2493.Valid 17 8 15 certificate_2493_q certificate_2493_edges 7 4 [] := by decide +kernel
theorem certificate_2493_valid : certificate_2493.Valid 17 8 (patternOrder [[],[],[1,1],[2,3]]) (patternClique [[],[],[1,1],[2,3]]) (patternEdges [[],[],[1,1],[2,3]]) (patternAmount [[],[],[1,1],[2,3]]) (patternEdgeCount [[],[],[1,1],[2,3]]) [] := certificate_2493_checked

theorem certificate_2494_checked : certificate_2494.Valid 17 8 16 certificate_2494_q certificate_2494_edges 8 4 [] := by decide +kernel
theorem certificate_2494_valid : certificate_2494.Valid 17 8 (patternOrder [[],[],[1,1],[2,4]]) (patternClique [[],[],[1,1],[2,4]]) (patternEdges [[],[],[1,1],[2,4]]) (patternAmount [[],[],[1,1],[2,4]]) (patternEdgeCount [[],[],[1,1],[2,4]]) [] := certificate_2494_checked

theorem certificate_2495_checked : certificate_2495.Valid 17 8 17 certificate_2495_q certificate_2495_edges 9 4 [] := by decide +kernel
theorem certificate_2495_valid : certificate_2495.Valid 17 8 (patternOrder [[],[],[1,1],[2,5]]) (patternClique [[],[],[1,1],[2,5]]) (patternEdges [[],[],[1,1],[2,5]]) (patternAmount [[],[],[1,1],[2,5]]) (patternEdgeCount [[],[],[1,1],[2,5]]) [] := certificate_2495_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates079
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2496_checked : certificate_2496.Valid 17 8 16 certificate_2496_q certificate_2496_edges 8 4 [] := by decide +kernel
theorem certificate_2496_valid : certificate_2496.Valid 17 8 (patternOrder [[],[],[1,1],[3,3]]) (patternClique [[],[],[1,1],[3,3]]) (patternEdges [[],[],[1,1],[3,3]]) (patternAmount [[],[],[1,1],[3,3]]) (patternEdgeCount [[],[],[1,1],[3,3]]) [] := certificate_2496_checked

theorem certificate_2497_checked : certificate_2497.Valid 17 8 17 certificate_2497_q certificate_2497_edges 9 4 [] := by decide +kernel
theorem certificate_2497_valid : certificate_2497.Valid 17 8 (patternOrder [[],[],[1,1],[3,4]]) (patternClique [[],[],[1,1],[3,4]]) (patternEdges [[],[],[1,1],[3,4]]) (patternAmount [[],[],[1,1],[3,4]]) (patternEdgeCount [[],[],[1,1],[3,4]]) [] := certificate_2497_checked

theorem certificate_2498_checked : certificate_2498.Valid 17 8 13 certificate_2498_q certificate_2498_edges 5 4 [] := by decide +kernel
theorem certificate_2498_valid : certificate_2498.Valid 17 8 (patternOrder [[],[],[1,1,1],[2]]) (patternClique [[],[],[1,1,1],[2]]) (patternEdges [[],[],[1,1,1],[2]]) (patternAmount [[],[],[1,1,1],[2]]) (patternEdgeCount [[],[],[1,1,1],[2]]) [] := certificate_2498_checked

theorem certificate_2499_checked : certificate_2499.Valid 17 8 14 certificate_2499_q certificate_2499_edges 6 4 [] := by decide +kernel
theorem certificate_2499_valid : certificate_2499.Valid 17 8 (patternOrder [[],[],[1,1,1],[3]]) (patternClique [[],[],[1,1,1],[3]]) (patternEdges [[],[],[1,1,1],[3]]) (patternAmount [[],[],[1,1,1],[3]]) (patternEdgeCount [[],[],[1,1,1],[3]]) [] := certificate_2499_checked

theorem certificate_2500_checked : certificate_2500.Valid 17 8 15 certificate_2500_q certificate_2500_edges 7 4 [] := by decide +kernel
theorem certificate_2500_valid : certificate_2500.Valid 17 8 (patternOrder [[],[],[1,1,1],[4]]) (patternClique [[],[],[1,1,1],[4]]) (patternEdges [[],[],[1,1,1],[4]]) (patternAmount [[],[],[1,1,1],[4]]) (patternEdgeCount [[],[],[1,1,1],[4]]) [] := certificate_2500_checked

theorem certificate_2501_checked : certificate_2501.Valid 17 8 16 certificate_2501_q certificate_2501_edges 8 4 [] := by decide +kernel
theorem certificate_2501_valid : certificate_2501.Valid 17 8 (patternOrder [[],[],[1,1,1],[5]]) (patternClique [[],[],[1,1,1],[5]]) (patternEdges [[],[],[1,1,1],[5]]) (patternAmount [[],[],[1,1,1],[5]]) (patternEdgeCount [[],[],[1,1,1],[5]]) [] := certificate_2501_checked

theorem certificate_2502_checked : certificate_2502.Valid 17 8 17 certificate_2502_q certificate_2502_edges 9 4 [] := by decide +kernel
theorem certificate_2502_valid : certificate_2502.Valid 17 8 (patternOrder [[],[],[1,1,1],[6]]) (patternClique [[],[],[1,1,1],[6]]) (patternEdges [[],[],[1,1,1],[6]]) (patternAmount [[],[],[1,1,1],[6]]) (patternEdgeCount [[],[],[1,1,1],[6]]) [] := certificate_2502_checked

theorem certificate_2503_checked : certificate_2503.Valid 17 8 13 certificate_2503_q certificate_2503_edges 5 5 [] := by decide +kernel
theorem certificate_2503_valid : certificate_2503.Valid 17 8 (patternOrder [[],[],[1,1,1,1,1]]) (patternClique [[],[],[1,1,1,1,1]]) (patternEdges [[],[],[1,1,1,1,1]]) (patternAmount [[],[],[1,1,1,1,1]]) (patternEdgeCount [[],[],[1,1,1,1,1]]) [] := certificate_2503_checked

theorem certificate_2504_checked : certificate_2504.Valid 17 8 14 certificate_2504_q certificate_2504_edges 6 5 [] := by decide +kernel
theorem certificate_2504_valid : certificate_2504.Valid 17 8 (patternOrder [[],[],[1,1,1,1,2]]) (patternClique [[],[],[1,1,1,1,2]]) (patternEdges [[],[],[1,1,1,1,2]]) (patternAmount [[],[],[1,1,1,1,2]]) (patternEdgeCount [[],[],[1,1,1,1,2]]) [] := certificate_2504_checked

theorem certificate_2505_checked : certificate_2505.Valid 17 8 15 certificate_2505_q certificate_2505_edges 7 5 [] := by decide +kernel
theorem certificate_2505_valid : certificate_2505.Valid 17 8 (patternOrder [[],[],[1,1,1,1,3]]) (patternClique [[],[],[1,1,1,1,3]]) (patternEdges [[],[],[1,1,1,1,3]]) (patternAmount [[],[],[1,1,1,1,3]]) (patternEdgeCount [[],[],[1,1,1,1,3]]) [] := certificate_2505_checked

theorem certificate_2506_checked : certificate_2506.Valid 17 8 16 certificate_2506_q certificate_2506_edges 8 5 [] := by decide +kernel
theorem certificate_2506_valid : certificate_2506.Valid 17 8 (patternOrder [[],[],[1,1,1,1,4]]) (patternClique [[],[],[1,1,1,1,4]]) (patternEdges [[],[],[1,1,1,1,4]]) (patternAmount [[],[],[1,1,1,1,4]]) (patternEdgeCount [[],[],[1,1,1,1,4]]) [] := certificate_2506_checked

theorem certificate_2507_checked : certificate_2507.Valid 17 8 17 certificate_2507_q certificate_2507_edges 9 5 [] := by decide +kernel
theorem certificate_2507_valid : certificate_2507.Valid 17 8 (patternOrder [[],[],[1,1,1,1,5]]) (patternClique [[],[],[1,1,1,1,5]]) (patternEdges [[],[],[1,1,1,1,5]]) (patternAmount [[],[],[1,1,1,1,5]]) (patternEdgeCount [[],[],[1,1,1,1,5]]) [] := certificate_2507_checked

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

theorem patterns_17_8_17_verified_oai : ∀ D ∈ patterns_17_8_17, PatternVerified 17 8 D := by

  simp only [patterns_17_8_17, List.forall_mem_cons]

  exact ⟨⟨certificate_2492, certificate_2492_valid⟩, ⟨⟨certificate_2493, certificate_2493_valid⟩, ⟨⟨certificate_2494, certificate_2494_valid⟩, ⟨⟨certificate_2495, certificate_2495_valid⟩, ⟨⟨certificate_2496, certificate_2496_valid⟩, ⟨⟨certificate_2497, certificate_2497_valid⟩, ⟨⟨certificate_2498, certificate_2498_valid⟩, ⟨⟨certificate_2499, certificate_2499_valid⟩, ⟨⟨certificate_2500, certificate_2500_valid⟩, ⟨⟨certificate_2501, certificate_2501_valid⟩, ⟨⟨certificate_2502, certificate_2502_valid⟩, ⟨⟨certificate_2503, certificate_2503_valid⟩, ⟨⟨certificate_2504, certificate_2504_valid⟩, ⟨⟨certificate_2505, certificate_2505_valid⟩, ⟨⟨certificate_2506, certificate_2506_valid⟩, ⟨⟨certificate_2507, certificate_2507_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_17_verified_oai := @OAI.CycleClique.patterns_17_8_17_verified_oai
