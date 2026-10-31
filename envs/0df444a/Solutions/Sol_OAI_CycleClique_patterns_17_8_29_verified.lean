-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_29_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:26:38.426136+00:00
-- url     : https://prove2.me/submissions/9e31802c-4d86-4c97-a1aa-7371b26b100d

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates084
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2684_checked : certificate_2684.Valid 17 8 16 certificate_2684_q certificate_2684_edges 8 5 [] := by decide +kernel
theorem certificate_2684_valid : certificate_2684.Valid 17 8 (patternOrder [[],[1],[1,3,1,2]]) (patternClique [[],[1],[1,3,1,2]]) (patternEdges [[],[1],[1,3,1,2]]) (patternAmount [[],[1],[1,3,1,2]]) (patternEdgeCount [[],[1],[1,3,1,2]]) [] := certificate_2684_checked

theorem certificate_2685_checked : certificate_2685.Valid 17 8 17 certificate_2685_q certificate_2685_edges 9 5 [] := by decide +kernel
theorem certificate_2685_valid : certificate_2685.Valid 17 8 (patternOrder [[],[1],[1,3,1,3]]) (patternClique [[],[1],[1,3,1,3]]) (patternEdges [[],[1],[1,3,1,3]]) (patternAmount [[],[1],[1,3,1,3]]) (patternEdgeCount [[],[1],[1,3,1,3]]) [] := certificate_2685_checked

theorem certificate_2686_checked : certificate_2686.Valid 17 8 17 certificate_2686_q certificate_2686_edges 9 5 [] := by decide +kernel
theorem certificate_2686_valid : certificate_2686.Valid 17 8 (patternOrder [[],[1],[1,3,2,2]]) (patternClique [[],[1],[1,3,2,2]]) (patternEdges [[],[1],[1,3,2,2]]) (patternAmount [[],[1],[1,3,2,2]]) (patternEdgeCount [[],[1],[1,3,2,2]]) [] := certificate_2686_checked

theorem certificate_2687_checked : certificate_2687.Valid 17 8 17 certificate_2687_q certificate_2687_edges 9 5 [] := by decide +kernel
theorem certificate_2687_valid : certificate_2687.Valid 17 8 (patternOrder [[],[1],[1,3,3,1]]) (patternClique [[],[1],[1,3,3,1]]) (patternEdges [[],[1],[1,3,3,1]]) (patternAmount [[],[1],[1,3,3,1]]) (patternEdgeCount [[],[1],[1,3,3,1]]) [] := certificate_2687_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates085
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2688_checked : certificate_2688.Valid 17 8 16 certificate_2688_q certificate_2688_edges 8 4 [] := by decide +kernel
theorem certificate_2688_valid : certificate_2688.Valid 17 8 (patternOrder [[],[1],[1,4],[2]]) (patternClique [[],[1],[1,4],[2]]) (patternEdges [[],[1],[1,4],[2]]) (patternAmount [[],[1],[1,4],[2]]) (patternEdgeCount [[],[1],[1,4],[2]]) [] := certificate_2688_checked

theorem certificate_2689_checked : certificate_2689.Valid 17 8 17 certificate_2689_q certificate_2689_edges 9 4 [] := by decide +kernel
theorem certificate_2689_valid : certificate_2689.Valid 17 8 (patternOrder [[],[1],[1,4],[3]]) (patternClique [[],[1],[1,4],[3]]) (patternEdges [[],[1],[1,4],[3]]) (patternAmount [[],[1],[1,4],[3]]) (patternEdgeCount [[],[1],[1,4],[3]]) [] := certificate_2689_checked

theorem certificate_2690_checked : certificate_2690.Valid 17 8 17 certificate_2690_q certificate_2690_edges 9 5 [] := by decide +kernel
theorem certificate_2690_valid : certificate_2690.Valid 17 8 (patternOrder [[],[1],[1,4,1,2]]) (patternClique [[],[1],[1,4,1,2]]) (patternEdges [[],[1],[1,4,1,2]]) (patternAmount [[],[1],[1,4,1,2]]) (patternEdgeCount [[],[1],[1,4,1,2]]) [] := certificate_2690_checked

theorem certificate_2691_checked : certificate_2691.Valid 17 8 17 certificate_2691_q certificate_2691_edges 9 4 [] := by decide +kernel
theorem certificate_2691_valid : certificate_2691.Valid 17 8 (patternOrder [[],[1],[1,5],[2]]) (patternClique [[],[1],[1,5],[2]]) (patternEdges [[],[1],[1,5],[2]]) (patternAmount [[],[1],[1,5],[2]]) (patternEdgeCount [[],[1],[1,5],[2]]) [] := certificate_2691_checked

theorem certificate_2692_checked : certificate_2692.Valid 17 8 15 certificate_2692_q certificate_2692_edges 7 4 [] := by decide +kernel
theorem certificate_2692_valid : certificate_2692.Valid 17 8 (patternOrder [[],[1],[2],[2,2]]) (patternClique [[],[1],[2],[2,2]]) (patternEdges [[],[1],[2],[2,2]]) (patternAmount [[],[1],[2],[2,2]]) (patternEdgeCount [[],[1],[2],[2,2]]) [] := certificate_2692_checked

theorem certificate_2693_checked : certificate_2693.Valid 17 8 16 certificate_2693_q certificate_2693_edges 8 4 [] := by decide +kernel
theorem certificate_2693_valid : certificate_2693.Valid 17 8 (patternOrder [[],[1],[2],[2,3]]) (patternClique [[],[1],[2],[2,3]]) (patternEdges [[],[1],[2],[2,3]]) (patternAmount [[],[1],[2],[2,3]]) (patternEdgeCount [[],[1],[2],[2,3]]) [] := certificate_2693_checked

theorem certificate_2694_checked : certificate_2694.Valid 17 8 17 certificate_2694_q certificate_2694_edges 9 4 [] := by decide +kernel
theorem certificate_2694_valid : certificate_2694.Valid 17 8 (patternOrder [[],[1],[2],[2,4]]) (patternClique [[],[1],[2],[2,4]]) (patternEdges [[],[1],[2],[2,4]]) (patternAmount [[],[1],[2],[2,4]]) (patternEdgeCount [[],[1],[2],[2,4]]) [] := certificate_2694_checked

theorem certificate_2695_checked : certificate_2695.Valid 17 8 17 certificate_2695_q certificate_2695_edges 9 4 [] := by decide +kernel
theorem certificate_2695_valid : certificate_2695.Valid 17 8 (patternOrder [[],[1],[2],[3,3]]) (patternClique [[],[1],[2],[3,3]]) (patternEdges [[],[1],[2],[3,3]]) (patternAmount [[],[1],[2],[3,3]]) (patternEdgeCount [[],[1],[2],[3,3]]) [] := certificate_2695_checked

theorem certificate_2696_checked : certificate_2696.Valid 17 8 15 certificate_2696_q certificate_2696_edges 7 5 [] := by decide +kernel
theorem certificate_2696_valid : certificate_2696.Valid 17 8 (patternOrder [[],[1],[2,1,1,2]]) (patternClique [[],[1],[2,1,1,2]]) (patternEdges [[],[1],[2,1,1,2]]) (patternAmount [[],[1],[2,1,1,2]]) (patternEdgeCount [[],[1],[2,1,1,2]]) [] := certificate_2696_checked

theorem certificate_2697_checked : certificate_2697.Valid 17 8 16 certificate_2697_q certificate_2697_edges 8 5 [] := by decide +kernel
theorem certificate_2697_valid : certificate_2697.Valid 17 8 (patternOrder [[],[1],[2,1,1,3]]) (patternClique [[],[1],[2,1,1,3]]) (patternEdges [[],[1],[2,1,1,3]]) (patternAmount [[],[1],[2,1,1,3]]) (patternEdgeCount [[],[1],[2,1,1,3]]) [] := certificate_2697_checked

theorem certificate_2698_checked : certificate_2698.Valid 17 8 17 certificate_2698_q certificate_2698_edges 9 5 [] := by decide +kernel
theorem certificate_2698_valid : certificate_2698.Valid 17 8 (patternOrder [[],[1],[2,1,1,4]]) (patternClique [[],[1],[2,1,1,4]]) (patternEdges [[],[1],[2,1,1,4]]) (patternAmount [[],[1],[2,1,1,4]]) (patternEdgeCount [[],[1],[2,1,1,4]]) [] := certificate_2698_checked

theorem certificate_2699_checked : certificate_2699.Valid 17 8 16 certificate_2699_q certificate_2699_edges 8 5 [] := by decide +kernel
theorem certificate_2699_valid : certificate_2699.Valid 17 8 (patternOrder [[],[1],[2,1,2,2]]) (patternClique [[],[1],[2,1,2,2]]) (patternEdges [[],[1],[2,1,2,2]]) (patternAmount [[],[1],[2,1,2,2]]) (patternEdgeCount [[],[1],[2,1,2,2]]) [] := certificate_2699_checked

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

theorem patterns_17_8_29_verified_oai : ∀ D ∈ patterns_17_8_29, PatternVerified 17 8 D := by

  simp only [patterns_17_8_29, List.forall_mem_cons]

  exact ⟨⟨certificate_2684, certificate_2684_valid⟩, ⟨⟨certificate_2685, certificate_2685_valid⟩, ⟨⟨certificate_2686, certificate_2686_valid⟩, ⟨⟨certificate_2687, certificate_2687_valid⟩, ⟨⟨certificate_2688, certificate_2688_valid⟩, ⟨⟨certificate_2689, certificate_2689_valid⟩, ⟨⟨certificate_2690, certificate_2690_valid⟩, ⟨⟨certificate_2691, certificate_2691_valid⟩, ⟨⟨certificate_2692, certificate_2692_valid⟩, ⟨⟨certificate_2693, certificate_2693_valid⟩, ⟨⟨certificate_2694, certificate_2694_valid⟩, ⟨⟨certificate_2695, certificate_2695_valid⟩, ⟨⟨certificate_2696, certificate_2696_valid⟩, ⟨⟨certificate_2697, certificate_2697_valid⟩, ⟨⟨certificate_2698, certificate_2698_valid⟩, ⟨⟨certificate_2699, certificate_2699_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_29_verified_oai := @OAI.CycleClique.patterns_17_8_29_verified_oai
