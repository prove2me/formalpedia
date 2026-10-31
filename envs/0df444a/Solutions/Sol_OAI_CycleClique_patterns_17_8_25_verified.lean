-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_25_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:21:09.718023+00:00
-- url     : https://prove2.me/submissions/a0791229-4204-4256-8708-de99685e4ae4

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates082
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2620_checked : certificate_2620.Valid 17 8 17 certificate_2620_q certificate_2620_edges 9 5 [] := by decide +kernel
theorem certificate_2620_valid : certificate_2620.Valid 17 8 (patternOrder [[],[],[2,1,1,2,3]]) (patternClique [[],[],[2,1,1,2,3]]) (patternEdges [[],[],[2,1,1,2,3]]) (patternAmount [[],[],[2,1,1,2,3]]) (patternEdgeCount [[],[],[2,1,1,2,3]]) [] := certificate_2620_checked

theorem certificate_2621_checked : certificate_2621.Valid 17 8 17 certificate_2621_q certificate_2621_edges 9 5 [] := by decide +kernel
theorem certificate_2621_valid : certificate_2621.Valid 17 8 (patternOrder [[],[],[2,1,1,3,2]]) (patternClique [[],[],[2,1,1,3,2]]) (patternEdges [[],[],[2,1,1,3,2]]) (patternAmount [[],[],[2,1,1,3,2]]) (patternEdgeCount [[],[],[2,1,1,3,2]]) [] := certificate_2621_checked

theorem certificate_2622_checked : certificate_2622.Valid 17 8 16 certificate_2622_q certificate_2622_edges 8 4 [] := by decide +kernel
theorem certificate_2622_valid : certificate_2622.Valid 17 8 (patternOrder [[],[],[2,1,2],[3]]) (patternClique [[],[],[2,1,2],[3]]) (patternEdges [[],[],[2,1,2],[3]]) (patternAmount [[],[],[2,1,2],[3]]) (patternEdgeCount [[],[],[2,1,2],[3]]) [] := certificate_2622_checked

theorem certificate_2623_checked : certificate_2623.Valid 17 8 17 certificate_2623_q certificate_2623_edges 9 4 [] := by decide +kernel
theorem certificate_2623_valid : certificate_2623.Valid 17 8 (patternOrder [[],[],[2,1,2],[4]]) (patternClique [[],[],[2,1,2],[4]]) (patternEdges [[],[],[2,1,2],[4]]) (patternAmount [[],[],[2,1,2],[4]]) (patternEdgeCount [[],[],[2,1,2],[4]]) [] := certificate_2623_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates083
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2624_checked : certificate_2624.Valid 17 8 16 certificate_2624_q certificate_2624_edges 8 5 [] := by decide +kernel
theorem certificate_2624_valid : certificate_2624.Valid 17 8 (patternOrder [[],[],[2,1,2,1,2]]) (patternClique [[],[],[2,1,2,1,2]]) (patternEdges [[],[],[2,1,2,1,2]]) (patternAmount [[],[],[2,1,2,1,2]]) (patternEdgeCount [[],[],[2,1,2,1,2]]) [] := certificate_2624_checked

theorem certificate_2625_checked : certificate_2625.Valid 17 8 17 certificate_2625_q certificate_2625_edges 9 5 [] := by decide +kernel
theorem certificate_2625_valid : certificate_2625.Valid 17 8 (patternOrder [[],[],[2,1,2,1,3]]) (patternClique [[],[],[2,1,2,1,3]]) (patternEdges [[],[],[2,1,2,1,3]]) (patternAmount [[],[],[2,1,2,1,3]]) (patternEdgeCount [[],[],[2,1,2,1,3]]) [] := certificate_2625_checked

theorem certificate_2626_checked : certificate_2626.Valid 17 8 17 certificate_2626_q certificate_2626_edges 9 5 [] := by decide +kernel
theorem certificate_2626_valid : certificate_2626.Valid 17 8 (patternOrder [[],[],[2,1,2,2,2]]) (patternClique [[],[],[2,1,2,2,2]]) (patternEdges [[],[],[2,1,2,2,2]]) (patternAmount [[],[],[2,1,2,2,2]]) (patternEdgeCount [[],[],[2,1,2,2,2]]) [] := certificate_2626_checked

theorem certificate_2627_checked : certificate_2627.Valid 17 8 17 certificate_2627_q certificate_2627_edges 9 4 [] := by decide +kernel
theorem certificate_2627_valid : certificate_2627.Valid 17 8 (patternOrder [[],[],[2,1,3],[3]]) (patternClique [[],[],[2,1,3],[3]]) (patternEdges [[],[],[2,1,3],[3]]) (patternAmount [[],[],[2,1,3],[3]]) (patternEdgeCount [[],[],[2,1,3],[3]]) [] := certificate_2627_checked

theorem certificate_2628_checked : certificate_2628.Valid 17 8 17 certificate_2628_q certificate_2628_edges 9 5 [] := by decide +kernel
theorem certificate_2628_valid : certificate_2628.Valid 17 8 (patternOrder [[],[],[2,1,3,1,2]]) (patternClique [[],[],[2,1,3,1,2]]) (patternEdges [[],[],[2,1,3,1,2]]) (patternAmount [[],[],[2,1,3,1,2]]) (patternEdgeCount [[],[],[2,1,3,1,2]]) [] := certificate_2628_checked

theorem certificate_2629_checked : certificate_2629.Valid 17 8 16 certificate_2629_q certificate_2629_edges 8 4 [] := by decide +kernel
theorem certificate_2629_valid : certificate_2629.Valid 17 8 (patternOrder [[],[],[2,2],[2,2]]) (patternClique [[],[],[2,2],[2,2]]) (patternEdges [[],[],[2,2],[2,2]]) (patternAmount [[],[],[2,2],[2,2]]) (patternEdgeCount [[],[],[2,2],[2,2]]) [] := certificate_2629_checked

theorem certificate_2630_checked : certificate_2630.Valid 17 8 17 certificate_2630_q certificate_2630_edges 9 4 [] := by decide +kernel
theorem certificate_2630_valid : certificate_2630.Valid 17 8 (patternOrder [[],[],[2,2],[2,3]]) (patternClique [[],[],[2,2],[2,3]]) (patternEdges [[],[],[2,2],[2,3]]) (patternAmount [[],[],[2,2],[2,3]]) (patternEdgeCount [[],[],[2,2],[2,3]]) [] := certificate_2630_checked

theorem certificate_2631_checked : certificate_2631.Valid 17 8 17 certificate_2631_q certificate_2631_edges 9 5 [] := by decide +kernel
theorem certificate_2631_valid : certificate_2631.Valid 17 8 (patternOrder [[],[],[2,2,1,1,3]]) (patternClique [[],[],[2,2,1,1,3]]) (patternEdges [[],[],[2,2,1,1,3]]) (patternAmount [[],[],[2,2,1,1,3]]) (patternEdgeCount [[],[],[2,2,1,1,3]]) [] := certificate_2631_checked

theorem certificate_2632_checked : certificate_2632.Valid 17 8 17 certificate_2632_q certificate_2632_edges 9 5 [] := by decide +kernel
theorem certificate_2632_valid : certificate_2632.Valid 17 8 (patternOrder [[],[],[2,2,1,2,2]]) (patternClique [[],[],[2,2,1,2,2]]) (patternEdges [[],[],[2,2,1,2,2]]) (patternAmount [[],[],[2,2,1,2,2]]) (patternEdgeCount [[],[],[2,2,1,2,2]]) [] := certificate_2632_checked

theorem certificate_2633_checked : certificate_2633.Valid 17 8 17 certificate_2633_q certificate_2633_edges 9 4 [] := by decide +kernel
theorem certificate_2633_valid : certificate_2633.Valid 17 8 (patternOrder [[],[],[2,2,2],[3]]) (patternClique [[],[],[2,2,2],[3]]) (patternEdges [[],[],[2,2,2],[3]]) (patternAmount [[],[],[2,2,2],[3]]) (patternEdgeCount [[],[],[2,2,2],[3]]) [] := certificate_2633_checked

theorem certificate_2634_checked : certificate_2634.Valid 17 8 17 certificate_2634_q certificate_2634_edges 9 3 [] := by decide +kernel
theorem certificate_2634_valid : certificate_2634.Valid 17 8 (patternOrder [[],[],[3],[3],[3]]) (patternClique [[],[],[3],[3],[3]]) (patternEdges [[],[],[3],[3],[3]]) (patternAmount [[],[],[3],[3],[3]]) (patternEdgeCount [[],[],[3],[3],[3]]) [] := certificate_2634_checked

theorem certificate_2635_checked : certificate_2635.Valid 17 8 17 certificate_2635_q certificate_2635_edges 9 5 [] := by decide +kernel
theorem certificate_2635_valid : certificate_2635.Valid 17 8 (patternOrder [[],[],[3,1,1,1,3]]) (patternClique [[],[],[3,1,1,1,3]]) (patternEdges [[],[],[3,1,1,1,3]]) (patternAmount [[],[],[3,1,1,1,3]]) (patternEdgeCount [[],[],[3,1,1,1,3]]) [] := certificate_2635_checked

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

theorem patterns_17_8_25_verified_oai : ∀ D ∈ patterns_17_8_25, PatternVerified 17 8 D := by

  simp only [patterns_17_8_25, List.forall_mem_cons]

  exact ⟨⟨certificate_2620, certificate_2620_valid⟩, ⟨⟨certificate_2621, certificate_2621_valid⟩, ⟨⟨certificate_2622, certificate_2622_valid⟩, ⟨⟨certificate_2623, certificate_2623_valid⟩, ⟨⟨certificate_2624, certificate_2624_valid⟩, ⟨⟨certificate_2625, certificate_2625_valid⟩, ⟨⟨certificate_2626, certificate_2626_valid⟩, ⟨⟨certificate_2627, certificate_2627_valid⟩, ⟨⟨certificate_2628, certificate_2628_valid⟩, ⟨⟨certificate_2629, certificate_2629_valid⟩, ⟨⟨certificate_2630, certificate_2630_valid⟩, ⟨⟨certificate_2631, certificate_2631_valid⟩, ⟨⟨certificate_2632, certificate_2632_valid⟩, ⟨⟨certificate_2633, certificate_2633_valid⟩, ⟨⟨certificate_2634, certificate_2634_valid⟩, ⟨⟨certificate_2635, certificate_2635_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_25_verified_oai := @OAI.CycleClique.patterns_17_8_25_verified_oai
