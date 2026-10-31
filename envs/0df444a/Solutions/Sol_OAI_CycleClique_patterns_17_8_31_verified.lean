-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_31_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:29:13.641465+00:00
-- url     : https://prove2.me/submissions/7091e181-9ca4-42a0-bf00-a263fc9db050

import Mathlib
import Definitions.Def_OAIQ107D090
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates085
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2716_checked : certificate_2716.Valid 17 8 17 certificate_2716_q certificate_2716_edges 9 5 [] := by decide +kernel
theorem certificate_2716_valid : certificate_2716.Valid 17 8 (patternOrder [[],[1,1],[1,2,4]]) (patternClique [[],[1,1],[1,2,4]]) (patternEdges [[],[1,1],[1,2,4]]) (patternAmount [[],[1,1],[1,2,4]]) (patternEdgeCount [[],[1,1],[1,2,4]]) [] := certificate_2716_checked

theorem certificate_2717_checked : certificate_2717.Valid 17 8 15 certificate_2717_q certificate_2717_edges 7 5 [] := by decide +kernel
theorem certificate_2717_valid : certificate_2717.Valid 17 8 (patternOrder [[],[1,1],[1,3,1]]) (patternClique [[],[1,1],[1,3,1]]) (patternEdges [[],[1,1],[1,3,1]]) (patternAmount [[],[1,1],[1,3,1]]) (patternEdgeCount [[],[1,1],[1,3,1]]) [] := certificate_2717_checked

theorem certificate_2718_checked : certificate_2718.Valid 17 8 16 certificate_2718_q certificate_2718_edges 8 5 [] := by decide +kernel
theorem certificate_2718_valid : certificate_2718.Valid 17 8 (patternOrder [[],[1,1],[1,3,2]]) (patternClique [[],[1,1],[1,3,2]]) (patternEdges [[],[1,1],[1,3,2]]) (patternAmount [[],[1,1],[1,3,2]]) (patternEdgeCount [[],[1,1],[1,3,2]]) [] := certificate_2718_checked

theorem certificate_2719_checked : certificate_2719.Valid 17 8 17 certificate_2719_q certificate_2719_edges 9 5 [] := by decide +kernel
theorem certificate_2719_valid : certificate_2719.Valid 17 8 (patternOrder [[],[1,1],[1,3,3]]) (patternClique [[],[1,1],[1,3,3]]) (patternEdges [[],[1,1],[1,3,3]]) (patternAmount [[],[1,1],[1,3,3]]) (patternEdgeCount [[],[1,1],[1,3,3]]) [] := certificate_2719_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates086
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2720_checked : certificate_2720.Valid 17 8 16 certificate_2720_q certificate_2720_edges 8 5 [] := by decide +kernel
theorem certificate_2720_valid : certificate_2720.Valid 17 8 (patternOrder [[],[1,1],[1,4,1]]) (patternClique [[],[1,1],[1,4,1]]) (patternEdges [[],[1,1],[1,4,1]]) (patternAmount [[],[1,1],[1,4,1]]) (patternEdgeCount [[],[1,1],[1,4,1]]) [] := certificate_2720_checked

theorem certificate_2721_checked : certificate_2721.Valid 17 8 17 certificate_2721_q certificate_2721_edges 9 5 [] := by decide +kernel
theorem certificate_2721_valid : certificate_2721.Valid 17 8 (patternOrder [[],[1,1],[1,4,2]]) (patternClique [[],[1,1],[1,4,2]]) (patternEdges [[],[1,1],[1,4,2]]) (patternAmount [[],[1,1],[1,4,2]]) (patternEdgeCount [[],[1,1],[1,4,2]]) [] := certificate_2721_checked

theorem certificate_2722_checked : certificate_2722.Valid 17 8 17 certificate_2722_q certificate_2722_edges 9 5 [] := by decide +kernel
theorem certificate_2722_valid : certificate_2722.Valid 17 8 (patternOrder [[],[1,1],[1,5,1]]) (patternClique [[],[1,1],[1,5,1]]) (patternEdges [[],[1,1],[1,5,1]]) (patternAmount [[],[1,1],[1,5,1]]) (patternEdgeCount [[],[1,1],[1,5,1]]) [] := certificate_2722_checked

theorem certificate_2723_checked : certificate_2723.Valid 17 8 14 certificate_2723_q certificate_2723_edges 6 4 [] := by decide +kernel
theorem certificate_2723_valid : certificate_2723.Valid 17 8 (patternOrder [[],[1,1],[2],[2]]) (patternClique [[],[1,1],[2],[2]]) (patternEdges [[],[1,1],[2],[2]]) (patternAmount [[],[1,1],[2],[2]]) (patternEdgeCount [[],[1,1],[2],[2]]) [] := certificate_2723_checked

theorem certificate_2724_checked : certificate_2724.Valid 17 8 15 certificate_2724_q certificate_2724_edges 7 4 [] := by decide +kernel
theorem certificate_2724_valid : certificate_2724.Valid 17 8 (patternOrder [[],[1,1],[2],[3]]) (patternClique [[],[1,1],[2],[3]]) (patternEdges [[],[1,1],[2],[3]]) (patternAmount [[],[1,1],[2],[3]]) (patternEdgeCount [[],[1,1],[2],[3]]) [] := certificate_2724_checked

theorem certificate_2725_checked : certificate_2725.Valid 17 8 16 certificate_2725_q certificate_2725_edges 8 4 [] := by decide +kernel
theorem certificate_2725_valid : certificate_2725.Valid 17 8 (patternOrder [[],[1,1],[2],[4]]) (patternClique [[],[1,1],[2],[4]]) (patternEdges [[],[1,1],[2],[4]]) (patternAmount [[],[1,1],[2],[4]]) (patternEdgeCount [[],[1,1],[2],[4]]) [] := certificate_2725_checked

theorem certificate_2726_checked : certificate_2726.Valid 17 8 17 certificate_2726_q certificate_2726_edges 9 4 [] := by decide +kernel
theorem certificate_2726_valid : certificate_2726.Valid 17 8 (patternOrder [[],[1,1],[2],[5]]) (patternClique [[],[1,1],[2],[5]]) (patternEdges [[],[1,1],[2],[5]]) (patternAmount [[],[1,1],[2],[5]]) (patternEdgeCount [[],[1,1],[2],[5]]) [] := certificate_2726_checked

theorem certificate_2727_checked : certificate_2727.Valid 17 8 15 certificate_2727_q certificate_2727_edges 7 5 [] := by decide +kernel
theorem certificate_2727_valid : certificate_2727.Valid 17 8 (patternOrder [[],[1,1],[2,1,2]]) (patternClique [[],[1,1],[2,1,2]]) (patternEdges [[],[1,1],[2,1,2]]) (patternAmount [[],[1,1],[2,1,2]]) (patternEdgeCount [[],[1,1],[2,1,2]]) [] := certificate_2727_checked

theorem certificate_2728_checked : certificate_2728.Valid 17 8 16 certificate_2728_q certificate_2728_edges 8 5 [] := by decide +kernel
theorem certificate_2728_valid : certificate_2728.Valid 17 8 (patternOrder [[],[1,1],[2,1,3]]) (patternClique [[],[1,1],[2,1,3]]) (patternEdges [[],[1,1],[2,1,3]]) (patternAmount [[],[1,1],[2,1,3]]) (patternEdgeCount [[],[1,1],[2,1,3]]) [] := certificate_2728_checked

theorem certificate_2729_checked : certificate_2729.Valid 17 8 17 certificate_2729_q certificate_2729_edges 9 5 [] := by decide +kernel
theorem certificate_2729_valid : certificate_2729.Valid 17 8 (patternOrder [[],[1,1],[2,1,4]]) (patternClique [[],[1,1],[2,1,4]]) (patternEdges [[],[1,1],[2,1,4]]) (patternAmount [[],[1,1],[2,1,4]]) (patternEdgeCount [[],[1,1],[2,1,4]]) [] := certificate_2729_checked

theorem certificate_2730_checked : certificate_2730.Valid 17 8 16 certificate_2730_q certificate_2730_edges 8 5 [] := by decide +kernel
theorem certificate_2730_valid : certificate_2730.Valid 17 8 (patternOrder [[],[1,1],[2,2,2]]) (patternClique [[],[1,1],[2,2,2]]) (patternEdges [[],[1,1],[2,2,2]]) (patternAmount [[],[1,1],[2,2,2]]) (patternEdgeCount [[],[1,1],[2,2,2]]) [] := certificate_2730_checked

theorem certificate_2731_checked : certificate_2731.Valid 17 8 17 certificate_2731_q certificate_2731_edges 9 5 [] := by decide +kernel
theorem certificate_2731_valid : certificate_2731.Valid 17 8 (patternOrder [[],[1,1],[2,2,3]]) (patternClique [[],[1,1],[2,2,3]]) (patternEdges [[],[1,1],[2,2,3]]) (patternAmount [[],[1,1],[2,2,3]]) (patternEdgeCount [[],[1,1],[2,2,3]]) [] := certificate_2731_checked

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

theorem patterns_17_8_31_verified_oai : ∀ D ∈ patterns_17_8_31, PatternVerified 17 8 D := by

  simp only [patterns_17_8_31, List.forall_mem_cons]

  exact ⟨⟨certificate_2716, certificate_2716_valid⟩, ⟨⟨certificate_2717, certificate_2717_valid⟩, ⟨⟨certificate_2718, certificate_2718_valid⟩, ⟨⟨certificate_2719, certificate_2719_valid⟩, ⟨⟨certificate_2720, certificate_2720_valid⟩, ⟨⟨certificate_2721, certificate_2721_valid⟩, ⟨⟨certificate_2722, certificate_2722_valid⟩, ⟨⟨certificate_2723, certificate_2723_valid⟩, ⟨⟨certificate_2724, certificate_2724_valid⟩, ⟨⟨certificate_2725, certificate_2725_valid⟩, ⟨⟨certificate_2726, certificate_2726_valid⟩, ⟨⟨certificate_2727, certificate_2727_valid⟩, ⟨⟨certificate_2728, certificate_2728_valid⟩, ⟨⟨certificate_2729, certificate_2729_valid⟩, ⟨⟨certificate_2730, certificate_2730_valid⟩, ⟨⟨certificate_2731, certificate_2731_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_31_verified_oai := @OAI.CycleClique.patterns_17_8_31_verified_oai
