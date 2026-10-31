-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_32_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:30:40.876639+00:00
-- url     : https://prove2.me/submissions/75fe90fd-badd-4c9c-bc42-5e5232f7b3eb

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates086
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2732_checked : certificate_2732.Valid 17 8 17 certificate_2732_q certificate_2732_edges 9 5 [] := by decide +kernel
theorem certificate_2732_valid : certificate_2732.Valid 17 8 (patternOrder [[],[1,1],[2,3,2]]) (patternClique [[],[1,1],[2,3,2]]) (patternEdges [[],[1,1],[2,3,2]]) (patternAmount [[],[1,1],[2,3,2]]) (patternEdgeCount [[],[1,1],[2,3,2]]) [] := certificate_2732_checked

theorem certificate_2733_checked : certificate_2733.Valid 17 8 16 certificate_2733_q certificate_2733_edges 8 4 [] := by decide +kernel
theorem certificate_2733_valid : certificate_2733.Valid 17 8 (patternOrder [[],[1,1],[3],[3]]) (patternClique [[],[1,1],[3],[3]]) (patternEdges [[],[1,1],[3],[3]]) (patternAmount [[],[1,1],[3],[3]]) (patternEdgeCount [[],[1,1],[3],[3]]) [] := certificate_2733_checked

theorem certificate_2734_checked : certificate_2734.Valid 17 8 17 certificate_2734_q certificate_2734_edges 9 4 [] := by decide +kernel
theorem certificate_2734_valid : certificate_2734.Valid 17 8 (patternOrder [[],[1,1],[3],[4]]) (patternClique [[],[1,1],[3],[4]]) (patternEdges [[],[1,1],[3],[4]]) (patternAmount [[],[1,1],[3],[4]]) (patternEdgeCount [[],[1,1],[3],[4]]) [] := certificate_2734_checked

theorem certificate_2735_checked : certificate_2735.Valid 17 8 17 certificate_2735_q certificate_2735_edges 9 5 [] := by decide +kernel
theorem certificate_2735_valid : certificate_2735.Valid 17 8 (patternOrder [[],[1,1],[3,1,3]]) (patternClique [[],[1,1],[3,1,3]]) (patternEdges [[],[1,1],[3,1,3]]) (patternAmount [[],[1,1],[3,1,3]]) (patternEdgeCount [[],[1,1],[3,1,3]]) [] := certificate_2735_checked

theorem certificate_2736_checked : certificate_2736.Valid 17 8 14 certificate_2736_q certificate_2736_edges 6 5 [] := by decide +kernel
theorem certificate_2736_valid : certificate_2736.Valid 17 8 (patternOrder [[],[1,1,1],[1,2]]) (patternClique [[],[1,1,1],[1,2]]) (patternEdges [[],[1,1,1],[1,2]]) (patternAmount [[],[1,1,1],[1,2]]) (patternEdgeCount [[],[1,1,1],[1,2]]) [] := certificate_2736_checked

theorem certificate_2737_checked : certificate_2737.Valid 17 8 15 certificate_2737_q certificate_2737_edges 7 5 [] := by decide +kernel
theorem certificate_2737_valid : certificate_2737.Valid 17 8 (patternOrder [[],[1,1,1],[1,3]]) (patternClique [[],[1,1,1],[1,3]]) (patternEdges [[],[1,1,1],[1,3]]) (patternAmount [[],[1,1,1],[1,3]]) (patternEdgeCount [[],[1,1,1],[1,3]]) [] := certificate_2737_checked

theorem certificate_2738_checked : certificate_2738.Valid 17 8 16 certificate_2738_q certificate_2738_edges 8 5 [] := by decide +kernel
theorem certificate_2738_valid : certificate_2738.Valid 17 8 (patternOrder [[],[1,1,1],[1,4]]) (patternClique [[],[1,1,1],[1,4]]) (patternEdges [[],[1,1,1],[1,4]]) (patternAmount [[],[1,1,1],[1,4]]) (patternEdgeCount [[],[1,1,1],[1,4]]) [] := certificate_2738_checked

theorem certificate_2739_checked : certificate_2739.Valid 17 8 17 certificate_2739_q certificate_2739_edges 9 5 [] := by decide +kernel
theorem certificate_2739_valid : certificate_2739.Valid 17 8 (patternOrder [[],[1,1,1],[1,5]]) (patternClique [[],[1,1,1],[1,5]]) (patternEdges [[],[1,1,1],[1,5]]) (patternAmount [[],[1,1,1],[1,5]]) (patternEdgeCount [[],[1,1,1],[1,5]]) [] := certificate_2739_checked

theorem certificate_2740_checked : certificate_2740.Valid 17 8 15 certificate_2740_q certificate_2740_edges 7 5 [] := by decide +kernel
theorem certificate_2740_valid : certificate_2740.Valid 17 8 (patternOrder [[],[1,1,1],[2,2]]) (patternClique [[],[1,1,1],[2,2]]) (patternEdges [[],[1,1,1],[2,2]]) (patternAmount [[],[1,1,1],[2,2]]) (patternEdgeCount [[],[1,1,1],[2,2]]) [] := certificate_2740_checked

theorem certificate_2741_checked : certificate_2741.Valid 17 8 16 certificate_2741_q certificate_2741_edges 8 5 [] := by decide +kernel
theorem certificate_2741_valid : certificate_2741.Valid 17 8 (patternOrder [[],[1,1,1],[2,3]]) (patternClique [[],[1,1,1],[2,3]]) (patternEdges [[],[1,1,1],[2,3]]) (patternAmount [[],[1,1,1],[2,3]]) (patternEdgeCount [[],[1,1,1],[2,3]]) [] := certificate_2741_checked

theorem certificate_2742_checked : certificate_2742.Valid 17 8 17 certificate_2742_q certificate_2742_edges 9 5 [] := by decide +kernel
theorem certificate_2742_valid : certificate_2742.Valid 17 8 (patternOrder [[],[1,1,1],[2,4]]) (patternClique [[],[1,1,1],[2,4]]) (patternEdges [[],[1,1,1],[2,4]]) (patternAmount [[],[1,1,1],[2,4]]) (patternEdgeCount [[],[1,1,1],[2,4]]) [] := certificate_2742_checked

theorem certificate_2743_checked : certificate_2743.Valid 17 8 17 certificate_2743_q certificate_2743_edges 9 5 [] := by decide +kernel
theorem certificate_2743_valid : certificate_2743.Valid 17 8 (patternOrder [[],[1,1,1],[3,3]]) (patternClique [[],[1,1,1],[3,3]]) (patternEdges [[],[1,1,1],[3,3]]) (patternAmount [[],[1,1,1],[3,3]]) (patternEdgeCount [[],[1,1,1],[3,3]]) [] := certificate_2743_checked

theorem certificate_2744_checked : certificate_2744.Valid 17 8 14 certificate_2744_q certificate_2744_edges 6 5 [] := by decide +kernel
theorem certificate_2744_valid : certificate_2744.Valid 17 8 (patternOrder [[],[1,1,1,1],[2]]) (patternClique [[],[1,1,1,1],[2]]) (patternEdges [[],[1,1,1,1],[2]]) (patternAmount [[],[1,1,1,1],[2]]) (patternEdgeCount [[],[1,1,1,1],[2]]) [] := certificate_2744_checked

theorem certificate_2745_checked : certificate_2745.Valid 17 8 15 certificate_2745_q certificate_2745_edges 7 5 [] := by decide +kernel
theorem certificate_2745_valid : certificate_2745.Valid 17 8 (patternOrder [[],[1,1,1,1],[3]]) (patternClique [[],[1,1,1,1],[3]]) (patternEdges [[],[1,1,1,1],[3]]) (patternAmount [[],[1,1,1,1],[3]]) (patternEdgeCount [[],[1,1,1,1],[3]]) [] := certificate_2745_checked

theorem certificate_2746_checked : certificate_2746.Valid 17 8 16 certificate_2746_q certificate_2746_edges 8 5 [] := by decide +kernel
theorem certificate_2746_valid : certificate_2746.Valid 17 8 (patternOrder [[],[1,1,1,1],[4]]) (patternClique [[],[1,1,1,1],[4]]) (patternEdges [[],[1,1,1,1],[4]]) (patternAmount [[],[1,1,1,1],[4]]) (patternEdgeCount [[],[1,1,1,1],[4]]) [] := certificate_2746_checked

theorem certificate_2747_checked : certificate_2747.Valid 17 8 17 certificate_2747_q certificate_2747_edges 9 5 [] := by decide +kernel
theorem certificate_2747_valid : certificate_2747.Valid 17 8 (patternOrder [[],[1,1,1,1],[5]]) (patternClique [[],[1,1,1,1],[5]]) (patternEdges [[],[1,1,1,1],[5]]) (patternAmount [[],[1,1,1,1],[5]]) (patternEdgeCount [[],[1,1,1,1],[5]]) [] := certificate_2747_checked

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

theorem patterns_17_8_32_verified_oai : ∀ D ∈ patterns_17_8_32, PatternVerified 17 8 D := by

  simp only [patterns_17_8_32, List.forall_mem_cons]

  exact ⟨⟨certificate_2732, certificate_2732_valid⟩, ⟨⟨certificate_2733, certificate_2733_valid⟩, ⟨⟨certificate_2734, certificate_2734_valid⟩, ⟨⟨certificate_2735, certificate_2735_valid⟩, ⟨⟨certificate_2736, certificate_2736_valid⟩, ⟨⟨certificate_2737, certificate_2737_valid⟩, ⟨⟨certificate_2738, certificate_2738_valid⟩, ⟨⟨certificate_2739, certificate_2739_valid⟩, ⟨⟨certificate_2740, certificate_2740_valid⟩, ⟨⟨certificate_2741, certificate_2741_valid⟩, ⟨⟨certificate_2742, certificate_2742_valid⟩, ⟨⟨certificate_2743, certificate_2743_valid⟩, ⟨⟨certificate_2744, certificate_2744_valid⟩, ⟨⟨certificate_2745, certificate_2745_valid⟩, ⟨⟨certificate_2746, certificate_2746_valid⟩, ⟨⟨certificate_2747, certificate_2747_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_32_verified_oai := @OAI.CycleClique.patterns_17_8_32_verified_oai
