-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_21_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:16:03.534616+00:00
-- url     : https://prove2.me/submissions/32fd248e-70dc-4416-847c-04a9ed03b3fa

import Mathlib
import Definitions.Def_OAIQ107D131
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

theorem certificate_2556_checked : certificate_2556.Valid 17 8 14 certificate_2556_q certificate_2556_edges 6 4 [] := by decide +kernel
theorem certificate_2556_valid : certificate_2556.Valid 17 8 (patternOrder [[],[],[1,2,1],[2]]) (patternClique [[],[],[1,2,1],[2]]) (patternEdges [[],[],[1,2,1],[2]]) (patternAmount [[],[],[1,2,1],[2]]) (patternEdgeCount [[],[],[1,2,1],[2]]) [] := certificate_2556_checked

theorem certificate_2557_checked : certificate_2557.Valid 17 8 15 certificate_2557_q certificate_2557_edges 7 4 [] := by decide +kernel
theorem certificate_2557_valid : certificate_2557.Valid 17 8 (patternOrder [[],[],[1,2,1],[3]]) (patternClique [[],[],[1,2,1],[3]]) (patternEdges [[],[],[1,2,1],[3]]) (patternAmount [[],[],[1,2,1],[3]]) (patternEdgeCount [[],[],[1,2,1],[3]]) [] := certificate_2557_checked

theorem certificate_2558_checked : certificate_2558.Valid 17 8 16 certificate_2558_q certificate_2558_edges 8 4 [] := by decide +kernel
theorem certificate_2558_valid : certificate_2558.Valid 17 8 (patternOrder [[],[],[1,2,1],[4]]) (patternClique [[],[],[1,2,1],[4]]) (patternEdges [[],[],[1,2,1],[4]]) (patternAmount [[],[],[1,2,1],[4]]) (patternEdgeCount [[],[],[1,2,1],[4]]) [] := certificate_2558_checked

theorem certificate_2559_checked : certificate_2559.Valid 17 8 17 certificate_2559_q certificate_2559_edges 9 4 [] := by decide +kernel
theorem certificate_2559_valid : certificate_2559.Valid 17 8 (patternOrder [[],[],[1,2,1],[5]]) (patternClique [[],[],[1,2,1],[5]]) (patternEdges [[],[],[1,2,1],[5]]) (patternAmount [[],[],[1,2,1],[5]]) (patternEdgeCount [[],[],[1,2,1],[5]]) [] := certificate_2559_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates081
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2560_checked : certificate_2560.Valid 17 8 15 certificate_2560_q certificate_2560_edges 7 5 [] := by decide +kernel
theorem certificate_2560_valid : certificate_2560.Valid 17 8 (patternOrder [[],[],[1,2,1,1,2]]) (patternClique [[],[],[1,2,1,1,2]]) (patternEdges [[],[],[1,2,1,1,2]]) (patternAmount [[],[],[1,2,1,1,2]]) (patternEdgeCount [[],[],[1,2,1,1,2]]) [] := certificate_2560_checked

theorem certificate_2561_checked : certificate_2561.Valid 17 8 16 certificate_2561_q certificate_2561_edges 8 5 [] := by decide +kernel
theorem certificate_2561_valid : certificate_2561.Valid 17 8 (patternOrder [[],[],[1,2,1,1,3]]) (patternClique [[],[],[1,2,1,1,3]]) (patternEdges [[],[],[1,2,1,1,3]]) (patternAmount [[],[],[1,2,1,1,3]]) (patternEdgeCount [[],[],[1,2,1,1,3]]) [] := certificate_2561_checked

theorem certificate_2562_checked : certificate_2562.Valid 17 8 17 certificate_2562_q certificate_2562_edges 9 5 [] := by decide +kernel
theorem certificate_2562_valid : certificate_2562.Valid 17 8 (patternOrder [[],[],[1,2,1,1,4]]) (patternClique [[],[],[1,2,1,1,4]]) (patternEdges [[],[],[1,2,1,1,4]]) (patternAmount [[],[],[1,2,1,1,4]]) (patternEdgeCount [[],[],[1,2,1,1,4]]) [] := certificate_2562_checked

theorem certificate_2563_checked : certificate_2563.Valid 17 8 15 certificate_2563_q certificate_2563_edges 7 5 [] := by decide +kernel
theorem certificate_2563_valid : certificate_2563.Valid 17 8 (patternOrder [[],[],[1,2,1,2,1]]) (patternClique [[],[],[1,2,1,2,1]]) (patternEdges [[],[],[1,2,1,2,1]]) (patternAmount [[],[],[1,2,1,2,1]]) (patternEdgeCount [[],[],[1,2,1,2,1]]) [] := certificate_2563_checked

theorem certificate_2564_checked : certificate_2564.Valid 17 8 16 certificate_2564_q certificate_2564_edges 8 5 [] := by decide +kernel
theorem certificate_2564_valid : certificate_2564.Valid 17 8 (patternOrder [[],[],[1,2,1,2,2]]) (patternClique [[],[],[1,2,1,2,2]]) (patternEdges [[],[],[1,2,1,2,2]]) (patternAmount [[],[],[1,2,1,2,2]]) (patternEdgeCount [[],[],[1,2,1,2,2]]) [] := certificate_2564_checked

theorem certificate_2565_checked : certificate_2565.Valid 17 8 17 certificate_2565_q certificate_2565_edges 9 5 [] := by decide +kernel
theorem certificate_2565_valid : certificate_2565.Valid 17 8 (patternOrder [[],[],[1,2,1,2,3]]) (patternClique [[],[],[1,2,1,2,3]]) (patternEdges [[],[],[1,2,1,2,3]]) (patternAmount [[],[],[1,2,1,2,3]]) (patternEdgeCount [[],[],[1,2,1,2,3]]) [] := certificate_2565_checked

theorem certificate_2566_checked : certificate_2566.Valid 17 8 16 certificate_2566_q certificate_2566_edges 8 5 [] := by decide +kernel
theorem certificate_2566_valid : certificate_2566.Valid 17 8 (patternOrder [[],[],[1,2,1,3,1]]) (patternClique [[],[],[1,2,1,3,1]]) (patternEdges [[],[],[1,2,1,3,1]]) (patternAmount [[],[],[1,2,1,3,1]]) (patternEdgeCount [[],[],[1,2,1,3,1]]) [] := certificate_2566_checked

theorem certificate_2567_checked : certificate_2567.Valid 17 8 17 certificate_2567_q certificate_2567_edges 9 5 [] := by decide +kernel
theorem certificate_2567_valid : certificate_2567.Valid 17 8 (patternOrder [[],[],[1,2,1,3,2]]) (patternClique [[],[],[1,2,1,3,2]]) (patternEdges [[],[],[1,2,1,3,2]]) (patternAmount [[],[],[1,2,1,3,2]]) (patternEdgeCount [[],[],[1,2,1,3,2]]) [] := certificate_2567_checked

theorem certificate_2568_checked : certificate_2568.Valid 17 8 17 certificate_2568_q certificate_2568_edges 9 5 [] := by decide +kernel
theorem certificate_2568_valid : certificate_2568.Valid 17 8 (patternOrder [[],[],[1,2,1,4,1]]) (patternClique [[],[],[1,2,1,4,1]]) (patternEdges [[],[],[1,2,1,4,1]]) (patternAmount [[],[],[1,2,1,4,1]]) (patternEdgeCount [[],[],[1,2,1,4,1]]) [] := certificate_2568_checked

theorem certificate_2569_checked : certificate_2569.Valid 17 8 15 certificate_2569_q certificate_2569_edges 7 4 [] := by decide +kernel
theorem certificate_2569_valid : certificate_2569.Valid 17 8 (patternOrder [[],[],[1,2,2],[2]]) (patternClique [[],[],[1,2,2],[2]]) (patternEdges [[],[],[1,2,2],[2]]) (patternAmount [[],[],[1,2,2],[2]]) (patternEdgeCount [[],[],[1,2,2],[2]]) [] := certificate_2569_checked

theorem certificate_2570_checked : certificate_2570.Valid 17 8 16 certificate_2570_q certificate_2570_edges 8 4 [] := by decide +kernel
theorem certificate_2570_valid : certificate_2570.Valid 17 8 (patternOrder [[],[],[1,2,2],[3]]) (patternClique [[],[],[1,2,2],[3]]) (patternEdges [[],[],[1,2,2],[3]]) (patternAmount [[],[],[1,2,2],[3]]) (patternEdgeCount [[],[],[1,2,2],[3]]) [] := certificate_2570_checked

theorem certificate_2571_checked : certificate_2571.Valid 17 8 17 certificate_2571_q certificate_2571_edges 9 4 [] := by decide +kernel
theorem certificate_2571_valid : certificate_2571.Valid 17 8 (patternOrder [[],[],[1,2,2],[4]]) (patternClique [[],[],[1,2,2],[4]]) (patternEdges [[],[],[1,2,2],[4]]) (patternAmount [[],[],[1,2,2],[4]]) (patternEdgeCount [[],[],[1,2,2],[4]]) [] := certificate_2571_checked

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

theorem patterns_17_8_21_verified_oai : ∀ D ∈ patterns_17_8_21, PatternVerified 17 8 D := by

  simp only [patterns_17_8_21, List.forall_mem_cons]

  exact ⟨⟨certificate_2556, certificate_2556_valid⟩, ⟨⟨certificate_2557, certificate_2557_valid⟩, ⟨⟨certificate_2558, certificate_2558_valid⟩, ⟨⟨certificate_2559, certificate_2559_valid⟩, ⟨⟨certificate_2560, certificate_2560_valid⟩, ⟨⟨certificate_2561, certificate_2561_valid⟩, ⟨⟨certificate_2562, certificate_2562_valid⟩, ⟨⟨certificate_2563, certificate_2563_valid⟩, ⟨⟨certificate_2564, certificate_2564_valid⟩, ⟨⟨certificate_2565, certificate_2565_valid⟩, ⟨⟨certificate_2566, certificate_2566_valid⟩, ⟨⟨certificate_2567, certificate_2567_valid⟩, ⟨⟨certificate_2568, certificate_2568_valid⟩, ⟨⟨certificate_2569, certificate_2569_valid⟩, ⟨⟨certificate_2570, certificate_2570_valid⟩, ⟨⟨certificate_2571, certificate_2571_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_21_verified_oai := @OAI.CycleClique.patterns_17_8_21_verified_oai
