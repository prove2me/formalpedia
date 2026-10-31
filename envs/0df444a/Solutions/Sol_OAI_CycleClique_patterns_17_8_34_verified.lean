-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_34_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:32:09.888437+00:00
-- url     : https://prove2.me/submissions/934311c3-f708-4280-afbb-bb4429ec2c30

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates087
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2764_checked : certificate_2764.Valid 17 8 16 certificate_2764_q certificate_2764_edges 8 6 [] := by decide +kernel
theorem certificate_2764_valid : certificate_2764.Valid 17 8 (patternOrder [[],[1,1,1,2,2,1]]) (patternClique [[],[1,1,1,2,2,1]]) (patternEdges [[],[1,1,1,2,2,1]]) (patternAmount [[],[1,1,1,2,2,1]]) (patternEdgeCount [[],[1,1,1,2,2,1]]) [] := certificate_2764_checked

theorem certificate_2765_checked : certificate_2765.Valid 17 8 17 certificate_2765_q certificate_2765_edges 9 6 [] := by decide +kernel
theorem certificate_2765_valid : certificate_2765.Valid 17 8 (patternOrder [[],[1,1,1,2,2,2]]) (patternClique [[],[1,1,1,2,2,2]]) (patternEdges [[],[1,1,1,2,2,2]]) (patternAmount [[],[1,1,1,2,2,2]]) (patternEdgeCount [[],[1,1,1,2,2,2]]) [] := certificate_2765_checked

theorem certificate_2766_checked : certificate_2766.Valid 17 8 17 certificate_2766_q certificate_2766_edges 9 6 [] := by decide +kernel
theorem certificate_2766_valid : certificate_2766.Valid 17 8 (patternOrder [[],[1,1,1,2,3,1]]) (patternClique [[],[1,1,1,2,3,1]]) (patternEdges [[],[1,1,1,2,3,1]]) (patternAmount [[],[1,1,1,2,3,1]]) (patternEdgeCount [[],[1,1,1,2,3,1]]) [] := certificate_2766_checked

theorem certificate_2767_checked : certificate_2767.Valid 17 8 16 certificate_2767_q certificate_2767_edges 8 5 [] := by decide +kernel
theorem certificate_2767_valid : certificate_2767.Valid 17 8 (patternOrder [[],[1,1,1,3],[2]]) (patternClique [[],[1,1,1,3],[2]]) (patternEdges [[],[1,1,1,3],[2]]) (patternAmount [[],[1,1,1,3],[2]]) (patternEdgeCount [[],[1,1,1,3],[2]]) [] := certificate_2767_checked

theorem certificate_2768_checked : certificate_2768.Valid 17 8 17 certificate_2768_q certificate_2768_edges 9 5 [] := by decide +kernel
theorem certificate_2768_valid : certificate_2768.Valid 17 8 (patternOrder [[],[1,1,1,3],[3]]) (patternClique [[],[1,1,1,3],[3]]) (patternEdges [[],[1,1,1,3],[3]]) (patternAmount [[],[1,1,1,3],[3]]) (patternEdgeCount [[],[1,1,1,3],[3]]) [] := certificate_2768_checked

theorem certificate_2769_checked : certificate_2769.Valid 17 8 16 certificate_2769_q certificate_2769_edges 8 6 [] := by decide +kernel
theorem certificate_2769_valid : certificate_2769.Valid 17 8 (patternOrder [[],[1,1,1,3,1,1]]) (patternClique [[],[1,1,1,3,1,1]]) (patternEdges [[],[1,1,1,3,1,1]]) (patternAmount [[],[1,1,1,3,1,1]]) (patternEdgeCount [[],[1,1,1,3,1,1]]) [] := certificate_2769_checked

theorem certificate_2770_checked : certificate_2770.Valid 17 8 17 certificate_2770_q certificate_2770_edges 9 6 [] := by decide +kernel
theorem certificate_2770_valid : certificate_2770.Valid 17 8 (patternOrder [[],[1,1,1,3,1,2]]) (patternClique [[],[1,1,1,3,1,2]]) (patternEdges [[],[1,1,1,3,1,2]]) (patternAmount [[],[1,1,1,3,1,2]]) (patternEdgeCount [[],[1,1,1,3,1,2]]) [] := certificate_2770_checked

theorem certificate_2771_checked : certificate_2771.Valid 17 8 17 certificate_2771_q certificate_2771_edges 9 6 [] := by decide +kernel
theorem certificate_2771_valid : certificate_2771.Valid 17 8 (patternOrder [[],[1,1,1,3,2,1]]) (patternClique [[],[1,1,1,3,2,1]]) (patternEdges [[],[1,1,1,3,2,1]]) (patternAmount [[],[1,1,1,3,2,1]]) (patternEdgeCount [[],[1,1,1,3,2,1]]) [] := certificate_2771_checked

theorem certificate_2772_checked : certificate_2772.Valid 17 8 17 certificate_2772_q certificate_2772_edges 9 5 [] := by decide +kernel
theorem certificate_2772_valid : certificate_2772.Valid 17 8 (patternOrder [[],[1,1,1,4],[2]]) (patternClique [[],[1,1,1,4],[2]]) (patternEdges [[],[1,1,1,4],[2]]) (patternAmount [[],[1,1,1,4],[2]]) (patternEdgeCount [[],[1,1,1,4],[2]]) [] := certificate_2772_checked

theorem certificate_2773_checked : certificate_2773.Valid 17 8 17 certificate_2773_q certificate_2773_edges 9 6 [] := by decide +kernel
theorem certificate_2773_valid : certificate_2773.Valid 17 8 (patternOrder [[],[1,1,1,4,1,1]]) (patternClique [[],[1,1,1,4,1,1]]) (patternEdges [[],[1,1,1,4,1,1]]) (patternAmount [[],[1,1,1,4,1,1]]) (patternEdgeCount [[],[1,1,1,4,1,1]]) [] := certificate_2773_checked

theorem certificate_2774_checked : certificate_2774.Valid 17 8 15 certificate_2774_q certificate_2774_edges 7 5 [] := by decide +kernel
theorem certificate_2774_valid : certificate_2774.Valid 17 8 (patternOrder [[],[1,1,2],[1,2]]) (patternClique [[],[1,1,2],[1,2]]) (patternEdges [[],[1,1,2],[1,2]]) (patternAmount [[],[1,1,2],[1,2]]) (patternEdgeCount [[],[1,1,2],[1,2]]) [] := certificate_2774_checked

theorem certificate_2775_checked : certificate_2775.Valid 17 8 16 certificate_2775_q certificate_2775_edges 8 5 [] := by decide +kernel
theorem certificate_2775_valid : certificate_2775.Valid 17 8 (patternOrder [[],[1,1,2],[1,3]]) (patternClique [[],[1,1,2],[1,3]]) (patternEdges [[],[1,1,2],[1,3]]) (patternAmount [[],[1,1,2],[1,3]]) (patternEdgeCount [[],[1,1,2],[1,3]]) [] := certificate_2775_checked

theorem certificate_2776_checked : certificate_2776.Valid 17 8 17 certificate_2776_q certificate_2776_edges 9 5 [] := by decide +kernel
theorem certificate_2776_valid : certificate_2776.Valid 17 8 (patternOrder [[],[1,1,2],[1,4]]) (patternClique [[],[1,1,2],[1,4]]) (patternEdges [[],[1,1,2],[1,4]]) (patternAmount [[],[1,1,2],[1,4]]) (patternEdgeCount [[],[1,1,2],[1,4]]) [] := certificate_2776_checked

theorem certificate_2777_checked : certificate_2777.Valid 17 8 16 certificate_2777_q certificate_2777_edges 8 5 [] := by decide +kernel
theorem certificate_2777_valid : certificate_2777.Valid 17 8 (patternOrder [[],[1,1,2],[2,2]]) (patternClique [[],[1,1,2],[2,2]]) (patternEdges [[],[1,1,2],[2,2]]) (patternAmount [[],[1,1,2],[2,2]]) (patternEdgeCount [[],[1,1,2],[2,2]]) [] := certificate_2777_checked

theorem certificate_2778_checked : certificate_2778.Valid 17 8 17 certificate_2778_q certificate_2778_edges 9 5 [] := by decide +kernel
theorem certificate_2778_valid : certificate_2778.Valid 17 8 (patternOrder [[],[1,1,2],[2,3]]) (patternClique [[],[1,1,2],[2,3]]) (patternEdges [[],[1,1,2],[2,3]]) (patternAmount [[],[1,1,2],[2,3]]) (patternEdgeCount [[],[1,1,2],[2,3]]) [] := certificate_2778_checked

theorem certificate_2779_checked : certificate_2779.Valid 17 8 15 certificate_2779_q certificate_2779_edges 7 5 [] := by decide +kernel
theorem certificate_2779_valid : certificate_2779.Valid 17 8 (patternOrder [[],[1,1,2,1],[2]]) (patternClique [[],[1,1,2,1],[2]]) (patternEdges [[],[1,1,2,1],[2]]) (patternAmount [[],[1,1,2,1],[2]]) (patternEdgeCount [[],[1,1,2,1],[2]]) [] := certificate_2779_checked

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

theorem patterns_17_8_34_verified_oai : ∀ D ∈ patterns_17_8_34, PatternVerified 17 8 D := by

  simp only [patterns_17_8_34, List.forall_mem_cons]

  exact ⟨⟨certificate_2764, certificate_2764_valid⟩, ⟨⟨certificate_2765, certificate_2765_valid⟩, ⟨⟨certificate_2766, certificate_2766_valid⟩, ⟨⟨certificate_2767, certificate_2767_valid⟩, ⟨⟨certificate_2768, certificate_2768_valid⟩, ⟨⟨certificate_2769, certificate_2769_valid⟩, ⟨⟨certificate_2770, certificate_2770_valid⟩, ⟨⟨certificate_2771, certificate_2771_valid⟩, ⟨⟨certificate_2772, certificate_2772_valid⟩, ⟨⟨certificate_2773, certificate_2773_valid⟩, ⟨⟨certificate_2774, certificate_2774_valid⟩, ⟨⟨certificate_2775, certificate_2775_valid⟩, ⟨⟨certificate_2776, certificate_2776_valid⟩, ⟨⟨certificate_2777, certificate_2777_valid⟩, ⟨⟨certificate_2778, certificate_2778_valid⟩, ⟨⟨certificate_2779, certificate_2779_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_34_verified_oai := @OAI.CycleClique.patterns_17_8_34_verified_oai
