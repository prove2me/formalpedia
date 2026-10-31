-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_23_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:18:36.654138+00:00
-- url     : https://prove2.me/submissions/6099780b-2bdd-4e04-b1ec-5cfb48cca2bf

import Mathlib
import Definitions.Def_OAIQ107D085
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates081
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2588_checked : certificate_2588.Valid 17 8 17 certificate_2588_q certificate_2588_edges 9 4 [] := by decide +kernel
theorem certificate_2588_valid : certificate_2588.Valid 17 8 (patternOrder [[],[],[1,3,1],[4]]) (patternClique [[],[],[1,3,1],[4]]) (patternEdges [[],[],[1,3,1],[4]]) (patternAmount [[],[],[1,3,1],[4]]) (patternEdgeCount [[],[],[1,3,1],[4]]) [] := certificate_2588_checked

theorem certificate_2589_checked : certificate_2589.Valid 17 8 16 certificate_2589_q certificate_2589_edges 8 5 [] := by decide +kernel
theorem certificate_2589_valid : certificate_2589.Valid 17 8 (patternOrder [[],[],[1,3,1,1,2]]) (patternClique [[],[],[1,3,1,1,2]]) (patternEdges [[],[],[1,3,1,1,2]]) (patternAmount [[],[],[1,3,1,1,2]]) (patternEdgeCount [[],[],[1,3,1,1,2]]) [] := certificate_2589_checked

theorem certificate_2590_checked : certificate_2590.Valid 17 8 17 certificate_2590_q certificate_2590_edges 9 5 [] := by decide +kernel
theorem certificate_2590_valid : certificate_2590.Valid 17 8 (patternOrder [[],[],[1,3,1,1,3]]) (patternClique [[],[],[1,3,1,1,3]]) (patternEdges [[],[],[1,3,1,1,3]]) (patternAmount [[],[],[1,3,1,1,3]]) (patternEdgeCount [[],[],[1,3,1,1,3]]) [] := certificate_2590_checked

theorem certificate_2591_checked : certificate_2591.Valid 17 8 17 certificate_2591_q certificate_2591_edges 9 5 [] := by decide +kernel
theorem certificate_2591_valid : certificate_2591.Valid 17 8 (patternOrder [[],[],[1,3,1,2,2]]) (patternClique [[],[],[1,3,1,2,2]]) (patternEdges [[],[],[1,3,1,2,2]]) (patternAmount [[],[],[1,3,1,2,2]]) (patternEdgeCount [[],[],[1,3,1,2,2]]) [] := certificate_2591_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates082
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2592_checked : certificate_2592.Valid 17 8 17 certificate_2592_q certificate_2592_edges 9 5 [] := by decide +kernel
theorem certificate_2592_valid : certificate_2592.Valid 17 8 (patternOrder [[],[],[1,3,1,3,1]]) (patternClique [[],[],[1,3,1,3,1]]) (patternEdges [[],[],[1,3,1,3,1]]) (patternAmount [[],[],[1,3,1,3,1]]) (patternEdgeCount [[],[],[1,3,1,3,1]]) [] := certificate_2592_checked

theorem certificate_2593_checked : certificate_2593.Valid 17 8 16 certificate_2593_q certificate_2593_edges 8 4 [] := by decide +kernel
theorem certificate_2593_valid : certificate_2593.Valid 17 8 (patternOrder [[],[],[1,3,2],[2]]) (patternClique [[],[],[1,3,2],[2]]) (patternEdges [[],[],[1,3,2],[2]]) (patternAmount [[],[],[1,3,2],[2]]) (patternEdgeCount [[],[],[1,3,2],[2]]) [] := certificate_2593_checked

theorem certificate_2594_checked : certificate_2594.Valid 17 8 17 certificate_2594_q certificate_2594_edges 9 4 [] := by decide +kernel
theorem certificate_2594_valid : certificate_2594.Valid 17 8 (patternOrder [[],[],[1,3,2],[3]]) (patternClique [[],[],[1,3,2],[3]]) (patternEdges [[],[],[1,3,2],[3]]) (patternAmount [[],[],[1,3,2],[3]]) (patternEdgeCount [[],[],[1,3,2],[3]]) [] := certificate_2594_checked

theorem certificate_2595_checked : certificate_2595.Valid 17 8 17 certificate_2595_q certificate_2595_edges 9 5 [] := by decide +kernel
theorem certificate_2595_valid : certificate_2595.Valid 17 8 (patternOrder [[],[],[1,3,2,1,2]]) (patternClique [[],[],[1,3,2,1,2]]) (patternEdges [[],[],[1,3,2,1,2]]) (patternAmount [[],[],[1,3,2,1,2]]) (patternEdgeCount [[],[],[1,3,2,1,2]]) [] := certificate_2595_checked

theorem certificate_2596_checked : certificate_2596.Valid 17 8 17 certificate_2596_q certificate_2596_edges 9 4 [] := by decide +kernel
theorem certificate_2596_valid : certificate_2596.Valid 17 8 (patternOrder [[],[],[1,3,3],[2]]) (patternClique [[],[],[1,3,3],[2]]) (patternEdges [[],[],[1,3,3],[2]]) (patternAmount [[],[],[1,3,3],[2]]) (patternEdgeCount [[],[],[1,3,3],[2]]) [] := certificate_2596_checked

theorem certificate_2597_checked : certificate_2597.Valid 17 8 17 certificate_2597_q certificate_2597_edges 9 4 [] := by decide +kernel
theorem certificate_2597_valid : certificate_2597.Valid 17 8 (patternOrder [[],[],[1,4],[2,2]]) (patternClique [[],[],[1,4],[2,2]]) (patternEdges [[],[],[1,4],[2,2]]) (patternAmount [[],[],[1,4],[2,2]]) (patternEdgeCount [[],[],[1,4],[2,2]]) [] := certificate_2597_checked

theorem certificate_2598_checked : certificate_2598.Valid 17 8 16 certificate_2598_q certificate_2598_edges 8 4 [] := by decide +kernel
theorem certificate_2598_valid : certificate_2598.Valid 17 8 (patternOrder [[],[],[1,4,1],[2]]) (patternClique [[],[],[1,4,1],[2]]) (patternEdges [[],[],[1,4,1],[2]]) (patternAmount [[],[],[1,4,1],[2]]) (patternEdgeCount [[],[],[1,4,1],[2]]) [] := certificate_2598_checked

theorem certificate_2599_checked : certificate_2599.Valid 17 8 17 certificate_2599_q certificate_2599_edges 9 4 [] := by decide +kernel
theorem certificate_2599_valid : certificate_2599.Valid 17 8 (patternOrder [[],[],[1,4,1],[3]]) (patternClique [[],[],[1,4,1],[3]]) (patternEdges [[],[],[1,4,1],[3]]) (patternAmount [[],[],[1,4,1],[3]]) (patternEdgeCount [[],[],[1,4,1],[3]]) [] := certificate_2599_checked

theorem certificate_2600_checked : certificate_2600.Valid 17 8 17 certificate_2600_q certificate_2600_edges 9 5 [] := by decide +kernel
theorem certificate_2600_valid : certificate_2600.Valid 17 8 (patternOrder [[],[],[1,4,1,1,2]]) (patternClique [[],[],[1,4,1,1,2]]) (patternEdges [[],[],[1,4,1,1,2]]) (patternAmount [[],[],[1,4,1,1,2]]) (patternEdgeCount [[],[],[1,4,1,1,2]]) [] := certificate_2600_checked

theorem certificate_2601_checked : certificate_2601.Valid 17 8 17 certificate_2601_q certificate_2601_edges 9 4 [] := by decide +kernel
theorem certificate_2601_valid : certificate_2601.Valid 17 8 (patternOrder [[],[],[1,4,2],[2]]) (patternClique [[],[],[1,4,2],[2]]) (patternEdges [[],[],[1,4,2],[2]]) (patternAmount [[],[],[1,4,2],[2]]) (patternEdgeCount [[],[],[1,4,2],[2]]) [] := certificate_2601_checked

theorem certificate_2602_checked : certificate_2602.Valid 17 8 17 certificate_2602_q certificate_2602_edges 9 4 [] := by decide +kernel
theorem certificate_2602_valid : certificate_2602.Valid 17 8 (patternOrder [[],[],[1,5,1],[2]]) (patternClique [[],[],[1,5,1],[2]]) (patternEdges [[],[],[1,5,1],[2]]) (patternAmount [[],[],[1,5,1],[2]]) (patternEdgeCount [[],[],[1,5,1],[2]]) [] := certificate_2602_checked

theorem certificate_2603_checked : certificate_2603.Valid 17 8 14 certificate_2603_q certificate_2603_edges 6 3 [] := by decide +kernel
theorem certificate_2603_valid : certificate_2603.Valid 17 8 (patternOrder [[],[],[2],[2],[2]]) (patternClique [[],[],[2],[2],[2]]) (patternEdges [[],[],[2],[2],[2]]) (patternAmount [[],[],[2],[2],[2]]) (patternEdgeCount [[],[],[2],[2],[2]]) [] := certificate_2603_checked

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

theorem patterns_17_8_23_verified_oai : ∀ D ∈ patterns_17_8_23, PatternVerified 17 8 D := by

  simp only [patterns_17_8_23, List.forall_mem_cons]

  exact ⟨⟨certificate_2588, certificate_2588_valid⟩, ⟨⟨certificate_2589, certificate_2589_valid⟩, ⟨⟨certificate_2590, certificate_2590_valid⟩, ⟨⟨certificate_2591, certificate_2591_valid⟩, ⟨⟨certificate_2592, certificate_2592_valid⟩, ⟨⟨certificate_2593, certificate_2593_valid⟩, ⟨⟨certificate_2594, certificate_2594_valid⟩, ⟨⟨certificate_2595, certificate_2595_valid⟩, ⟨⟨certificate_2596, certificate_2596_valid⟩, ⟨⟨certificate_2597, certificate_2597_valid⟩, ⟨⟨certificate_2598, certificate_2598_valid⟩, ⟨⟨certificate_2599, certificate_2599_valid⟩, ⟨⟨certificate_2600, certificate_2600_valid⟩, ⟨⟨certificate_2601, certificate_2601_valid⟩, ⟨⟨certificate_2602, certificate_2602_valid⟩, ⟨⟨certificate_2603, certificate_2603_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_23_verified_oai := @OAI.CycleClique.patterns_17_8_23_verified_oai
