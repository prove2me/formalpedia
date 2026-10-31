-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_20_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:16:02.142883+00:00
-- url     : https://prove2.me/submissions/ab44cf55-be86-412a-83b9-e99cb60a2f29

import Mathlib
import Definitions.Def_OAIQ107D083
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates080
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2540_checked : certificate_2540.Valid 17 8 17 certificate_2540_q certificate_2540_edges 9 5 [] := by decide +kernel
theorem certificate_2540_valid : certificate_2540.Valid 17 8 (patternOrder [[],[],[1,1,3,3,1]]) (patternClique [[],[],[1,1,3,3,1]]) (patternEdges [[],[],[1,1,3,3,1]]) (patternAmount [[],[],[1,1,3,3,1]]) (patternEdgeCount [[],[],[1,1,3,3,1]]) [] := certificate_2540_checked

theorem certificate_2541_checked : certificate_2541.Valid 17 8 16 certificate_2541_q certificate_2541_edges 8 4 [] := by decide +kernel
theorem certificate_2541_valid : certificate_2541.Valid 17 8 (patternOrder [[],[],[1,1,4],[2]]) (patternClique [[],[],[1,1,4],[2]]) (patternEdges [[],[],[1,1,4],[2]]) (patternAmount [[],[],[1,1,4],[2]]) (patternEdgeCount [[],[],[1,1,4],[2]]) [] := certificate_2541_checked

theorem certificate_2542_checked : certificate_2542.Valid 17 8 17 certificate_2542_q certificate_2542_edges 9 4 [] := by decide +kernel
theorem certificate_2542_valid : certificate_2542.Valid 17 8 (patternOrder [[],[],[1,1,4],[3]]) (patternClique [[],[],[1,1,4],[3]]) (patternEdges [[],[],[1,1,4],[3]]) (patternAmount [[],[],[1,1,4],[3]]) (patternEdgeCount [[],[],[1,1,4],[3]]) [] := certificate_2542_checked

theorem certificate_2543_checked : certificate_2543.Valid 17 8 16 certificate_2543_q certificate_2543_edges 8 5 [] := by decide +kernel
theorem certificate_2543_valid : certificate_2543.Valid 17 8 (patternOrder [[],[],[1,1,4,1,1]]) (patternClique [[],[],[1,1,4,1,1]]) (patternEdges [[],[],[1,1,4,1,1]]) (patternAmount [[],[],[1,1,4,1,1]]) (patternEdgeCount [[],[],[1,1,4,1,1]]) [] := certificate_2543_checked

theorem certificate_2544_checked : certificate_2544.Valid 17 8 17 certificate_2544_q certificate_2544_edges 9 5 [] := by decide +kernel
theorem certificate_2544_valid : certificate_2544.Valid 17 8 (patternOrder [[],[],[1,1,4,1,2]]) (patternClique [[],[],[1,1,4,1,2]]) (patternEdges [[],[],[1,1,4,1,2]]) (patternAmount [[],[],[1,1,4,1,2]]) (patternEdgeCount [[],[],[1,1,4,1,2]]) [] := certificate_2544_checked

theorem certificate_2545_checked : certificate_2545.Valid 17 8 17 certificate_2545_q certificate_2545_edges 9 5 [] := by decide +kernel
theorem certificate_2545_valid : certificate_2545.Valid 17 8 (patternOrder [[],[],[1,1,4,2,1]]) (patternClique [[],[],[1,1,4,2,1]]) (patternEdges [[],[],[1,1,4,2,1]]) (patternAmount [[],[],[1,1,4,2,1]]) (patternEdgeCount [[],[],[1,1,4,2,1]]) [] := certificate_2545_checked

theorem certificate_2546_checked : certificate_2546.Valid 17 8 17 certificate_2546_q certificate_2546_edges 9 4 [] := by decide +kernel
theorem certificate_2546_valid : certificate_2546.Valid 17 8 (patternOrder [[],[],[1,1,5],[2]]) (patternClique [[],[],[1,1,5],[2]]) (patternEdges [[],[],[1,1,5],[2]]) (patternAmount [[],[],[1,1,5],[2]]) (patternEdgeCount [[],[],[1,1,5],[2]]) [] := certificate_2546_checked

theorem certificate_2547_checked : certificate_2547.Valid 17 8 17 certificate_2547_q certificate_2547_edges 9 5 [] := by decide +kernel
theorem certificate_2547_valid : certificate_2547.Valid 17 8 (patternOrder [[],[],[1,1,5,1,1]]) (patternClique [[],[],[1,1,5,1,1]]) (patternEdges [[],[],[1,1,5,1,1]]) (patternAmount [[],[],[1,1,5,1,1]]) (patternEdgeCount [[],[],[1,1,5,1,1]]) [] := certificate_2547_checked

theorem certificate_2548_checked : certificate_2548.Valid 17 8 14 certificate_2548_q certificate_2548_edges 6 4 [] := by decide +kernel
theorem certificate_2548_valid : certificate_2548.Valid 17 8 (patternOrder [[],[],[1,2],[1,2]]) (patternClique [[],[],[1,2],[1,2]]) (patternEdges [[],[],[1,2],[1,2]]) (patternAmount [[],[],[1,2],[1,2]]) (patternEdgeCount [[],[],[1,2],[1,2]]) [] := certificate_2548_checked

theorem certificate_2549_checked : certificate_2549.Valid 17 8 15 certificate_2549_q certificate_2549_edges 7 4 [] := by decide +kernel
theorem certificate_2549_valid : certificate_2549.Valid 17 8 (patternOrder [[],[],[1,2],[1,3]]) (patternClique [[],[],[1,2],[1,3]]) (patternEdges [[],[],[1,2],[1,3]]) (patternAmount [[],[],[1,2],[1,3]]) (patternEdgeCount [[],[],[1,2],[1,3]]) [] := certificate_2549_checked

theorem certificate_2550_checked : certificate_2550.Valid 17 8 16 certificate_2550_q certificate_2550_edges 8 4 [] := by decide +kernel
theorem certificate_2550_valid : certificate_2550.Valid 17 8 (patternOrder [[],[],[1,2],[1,4]]) (patternClique [[],[],[1,2],[1,4]]) (patternEdges [[],[],[1,2],[1,4]]) (patternAmount [[],[],[1,2],[1,4]]) (patternEdgeCount [[],[],[1,2],[1,4]]) [] := certificate_2550_checked

theorem certificate_2551_checked : certificate_2551.Valid 17 8 17 certificate_2551_q certificate_2551_edges 9 4 [] := by decide +kernel
theorem certificate_2551_valid : certificate_2551.Valid 17 8 (patternOrder [[],[],[1,2],[1,5]]) (patternClique [[],[],[1,2],[1,5]]) (patternEdges [[],[],[1,2],[1,5]]) (patternAmount [[],[],[1,2],[1,5]]) (patternEdgeCount [[],[],[1,2],[1,5]]) [] := certificate_2551_checked

theorem certificate_2552_checked : certificate_2552.Valid 17 8 15 certificate_2552_q certificate_2552_edges 7 4 [] := by decide +kernel
theorem certificate_2552_valid : certificate_2552.Valid 17 8 (patternOrder [[],[],[1,2],[2,2]]) (patternClique [[],[],[1,2],[2,2]]) (patternEdges [[],[],[1,2],[2,2]]) (patternAmount [[],[],[1,2],[2,2]]) (patternEdgeCount [[],[],[1,2],[2,2]]) [] := certificate_2552_checked

theorem certificate_2553_checked : certificate_2553.Valid 17 8 16 certificate_2553_q certificate_2553_edges 8 4 [] := by decide +kernel
theorem certificate_2553_valid : certificate_2553.Valid 17 8 (patternOrder [[],[],[1,2],[2,3]]) (patternClique [[],[],[1,2],[2,3]]) (patternEdges [[],[],[1,2],[2,3]]) (patternAmount [[],[],[1,2],[2,3]]) (patternEdgeCount [[],[],[1,2],[2,3]]) [] := certificate_2553_checked

theorem certificate_2554_checked : certificate_2554.Valid 17 8 17 certificate_2554_q certificate_2554_edges 9 4 [] := by decide +kernel
theorem certificate_2554_valid : certificate_2554.Valid 17 8 (patternOrder [[],[],[1,2],[2,4]]) (patternClique [[],[],[1,2],[2,4]]) (patternEdges [[],[],[1,2],[2,4]]) (patternAmount [[],[],[1,2],[2,4]]) (patternEdgeCount [[],[],[1,2],[2,4]]) [] := certificate_2554_checked

theorem certificate_2555_checked : certificate_2555.Valid 17 8 17 certificate_2555_q certificate_2555_edges 9 4 [] := by decide +kernel
theorem certificate_2555_valid : certificate_2555.Valid 17 8 (patternOrder [[],[],[1,2],[3,3]]) (patternClique [[],[],[1,2],[3,3]]) (patternEdges [[],[],[1,2],[3,3]]) (patternAmount [[],[],[1,2],[3,3]]) (patternEdgeCount [[],[],[1,2],[3,3]]) [] := certificate_2555_checked

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

theorem patterns_17_8_20_verified_oai : ∀ D ∈ patterns_17_8_20, PatternVerified 17 8 D := by

  simp only [patterns_17_8_20, List.forall_mem_cons]

  exact ⟨⟨certificate_2540, certificate_2540_valid⟩, ⟨⟨certificate_2541, certificate_2541_valid⟩, ⟨⟨certificate_2542, certificate_2542_valid⟩, ⟨⟨certificate_2543, certificate_2543_valid⟩, ⟨⟨certificate_2544, certificate_2544_valid⟩, ⟨⟨certificate_2545, certificate_2545_valid⟩, ⟨⟨certificate_2546, certificate_2546_valid⟩, ⟨⟨certificate_2547, certificate_2547_valid⟩, ⟨⟨certificate_2548, certificate_2548_valid⟩, ⟨⟨certificate_2549, certificate_2549_valid⟩, ⟨⟨certificate_2550, certificate_2550_valid⟩, ⟨⟨certificate_2551, certificate_2551_valid⟩, ⟨⟨certificate_2552, certificate_2552_valid⟩, ⟨⟨certificate_2553, certificate_2553_valid⟩, ⟨⟨certificate_2554, certificate_2554_valid⟩, ⟨⟨certificate_2555, certificate_2555_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_20_verified_oai := @OAI.CycleClique.patterns_17_8_20_verified_oai
