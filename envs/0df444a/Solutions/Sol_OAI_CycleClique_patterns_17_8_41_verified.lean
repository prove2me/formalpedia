-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_41_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:46:23.193526+00:00
-- url     : https://prove2.me/submissions/1b2f2364-6a08-46db-9f4f-843d773f5adc

import Mathlib
import Definitions.Def_OAIQ107D132
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates090
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2876_checked : certificate_2876.Valid 17 8 16 certificate_2876_q certificate_2876_edges 8 5 [] := by decide +kernel
theorem certificate_2876_valid : certificate_2876.Valid 17 8 (patternOrder [[1],[1],[1,4,1]]) (patternClique [[1],[1],[1,4,1]]) (patternEdges [[1],[1],[1,4,1]]) (patternAmount [[1],[1],[1,4,1]]) (patternEdgeCount [[1],[1],[1,4,1]]) [] := certificate_2876_checked

theorem certificate_2877_checked : certificate_2877.Valid 17 8 17 certificate_2877_q certificate_2877_edges 9 5 [] := by decide +kernel
theorem certificate_2877_valid : certificate_2877.Valid 17 8 (patternOrder [[1],[1],[1,4,2]]) (patternClique [[1],[1],[1,4,2]]) (patternEdges [[1],[1],[1,4,2]]) (patternAmount [[1],[1],[1,4,2]]) (patternEdgeCount [[1],[1],[1,4,2]]) [] := certificate_2877_checked

theorem certificate_2878_checked : certificate_2878.Valid 17 8 17 certificate_2878_q certificate_2878_edges 9 5 [] := by decide +kernel
theorem certificate_2878_valid : certificate_2878.Valid 17 8 (patternOrder [[1],[1],[1,5,1]]) (patternClique [[1],[1],[1,5,1]]) (patternEdges [[1],[1],[1,5,1]]) (patternAmount [[1],[1],[1,5,1]]) (patternEdgeCount [[1],[1],[1,5,1]]) [] := certificate_2878_checked

theorem certificate_2879_checked : certificate_2879.Valid 17 8 14 certificate_2879_q certificate_2879_edges 6 4 [] := by decide +kernel
theorem certificate_2879_valid : certificate_2879.Valid 17 8 (patternOrder [[1],[1],[2],[2]]) (patternClique [[1],[1],[2],[2]]) (patternEdges [[1],[1],[2],[2]]) (patternAmount [[1],[1],[2],[2]]) (patternEdgeCount [[1],[1],[2],[2]]) [] := certificate_2879_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates091
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2880_checked : certificate_2880.Valid 17 8 15 certificate_2880_q certificate_2880_edges 7 4 [] := by decide +kernel
theorem certificate_2880_valid : certificate_2880.Valid 17 8 (patternOrder [[1],[1],[2],[3]]) (patternClique [[1],[1],[2],[3]]) (patternEdges [[1],[1],[2],[3]]) (patternAmount [[1],[1],[2],[3]]) (patternEdgeCount [[1],[1],[2],[3]]) [] := certificate_2880_checked

theorem certificate_2881_checked : certificate_2881.Valid 17 8 16 certificate_2881_q certificate_2881_edges 8 4 [] := by decide +kernel
theorem certificate_2881_valid : certificate_2881.Valid 17 8 (patternOrder [[1],[1],[2],[4]]) (patternClique [[1],[1],[2],[4]]) (patternEdges [[1],[1],[2],[4]]) (patternAmount [[1],[1],[2],[4]]) (patternEdgeCount [[1],[1],[2],[4]]) [] := certificate_2881_checked

theorem certificate_2882_checked : certificate_2882.Valid 17 8 17 certificate_2882_q certificate_2882_edges 9 4 [] := by decide +kernel
theorem certificate_2882_valid : certificate_2882.Valid 17 8 (patternOrder [[1],[1],[2],[5]]) (patternClique [[1],[1],[2],[5]]) (patternEdges [[1],[1],[2],[5]]) (patternAmount [[1],[1],[2],[5]]) (patternEdgeCount [[1],[1],[2],[5]]) [] := certificate_2882_checked

theorem certificate_2883_checked : certificate_2883.Valid 17 8 15 certificate_2883_q certificate_2883_edges 7 5 [] := by decide +kernel
theorem certificate_2883_valid : certificate_2883.Valid 17 8 (patternOrder [[1],[1],[2,1,2]]) (patternClique [[1],[1],[2,1,2]]) (patternEdges [[1],[1],[2,1,2]]) (patternAmount [[1],[1],[2,1,2]]) (patternEdgeCount [[1],[1],[2,1,2]]) [] := certificate_2883_checked

theorem certificate_2884_checked : certificate_2884.Valid 17 8 16 certificate_2884_q certificate_2884_edges 8 5 [] := by decide +kernel
theorem certificate_2884_valid : certificate_2884.Valid 17 8 (patternOrder [[1],[1],[2,1,3]]) (patternClique [[1],[1],[2,1,3]]) (patternEdges [[1],[1],[2,1,3]]) (patternAmount [[1],[1],[2,1,3]]) (patternEdgeCount [[1],[1],[2,1,3]]) [] := certificate_2884_checked

theorem certificate_2885_checked : certificate_2885.Valid 17 8 17 certificate_2885_q certificate_2885_edges 9 5 [] := by decide +kernel
theorem certificate_2885_valid : certificate_2885.Valid 17 8 (patternOrder [[1],[1],[2,1,4]]) (patternClique [[1],[1],[2,1,4]]) (patternEdges [[1],[1],[2,1,4]]) (patternAmount [[1],[1],[2,1,4]]) (patternEdgeCount [[1],[1],[2,1,4]]) [] := certificate_2885_checked

theorem certificate_2886_checked : certificate_2886.Valid 17 8 16 certificate_2886_q certificate_2886_edges 8 5 [] := by decide +kernel
theorem certificate_2886_valid : certificate_2886.Valid 17 8 (patternOrder [[1],[1],[2,2,2]]) (patternClique [[1],[1],[2,2,2]]) (patternEdges [[1],[1],[2,2,2]]) (patternAmount [[1],[1],[2,2,2]]) (patternEdgeCount [[1],[1],[2,2,2]]) [] := certificate_2886_checked

theorem certificate_2887_checked : certificate_2887.Valid 17 8 17 certificate_2887_q certificate_2887_edges 9 5 [] := by decide +kernel
theorem certificate_2887_valid : certificate_2887.Valid 17 8 (patternOrder [[1],[1],[2,2,3]]) (patternClique [[1],[1],[2,2,3]]) (patternEdges [[1],[1],[2,2,3]]) (patternAmount [[1],[1],[2,2,3]]) (patternEdgeCount [[1],[1],[2,2,3]]) [] := certificate_2887_checked

theorem certificate_2888_checked : certificate_2888.Valid 17 8 17 certificate_2888_q certificate_2888_edges 9 5 [] := by decide +kernel
theorem certificate_2888_valid : certificate_2888.Valid 17 8 (patternOrder [[1],[1],[2,3,2]]) (patternClique [[1],[1],[2,3,2]]) (patternEdges [[1],[1],[2,3,2]]) (patternAmount [[1],[1],[2,3,2]]) (patternEdgeCount [[1],[1],[2,3,2]]) [] := certificate_2888_checked

theorem certificate_2889_checked : certificate_2889.Valid 17 8 16 certificate_2889_q certificate_2889_edges 8 4 [] := by decide +kernel
theorem certificate_2889_valid : certificate_2889.Valid 17 8 (patternOrder [[1],[1],[3],[3]]) (patternClique [[1],[1],[3],[3]]) (patternEdges [[1],[1],[3],[3]]) (patternAmount [[1],[1],[3],[3]]) (patternEdgeCount [[1],[1],[3],[3]]) [] := certificate_2889_checked

theorem certificate_2890_checked : certificate_2890.Valid 17 8 17 certificate_2890_q certificate_2890_edges 9 4 [] := by decide +kernel
theorem certificate_2890_valid : certificate_2890.Valid 17 8 (patternOrder [[1],[1],[3],[4]]) (patternClique [[1],[1],[3],[4]]) (patternEdges [[1],[1],[3],[4]]) (patternAmount [[1],[1],[3],[4]]) (patternEdgeCount [[1],[1],[3],[4]]) [] := certificate_2890_checked

theorem certificate_2891_checked : certificate_2891.Valid 17 8 17 certificate_2891_q certificate_2891_edges 9 5 [] := by decide +kernel
theorem certificate_2891_valid : certificate_2891.Valid 17 8 (patternOrder [[1],[1],[3,1,3]]) (patternClique [[1],[1],[3,1,3]]) (patternEdges [[1],[1],[3,1,3]]) (patternAmount [[1],[1],[3,1,3]]) (patternEdgeCount [[1],[1],[3,1,3]]) [] := certificate_2891_checked

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

theorem patterns_17_8_41_verified_oai : ∀ D ∈ patterns_17_8_41, PatternVerified 17 8 D := by

  simp only [patterns_17_8_41, List.forall_mem_cons]

  exact ⟨⟨certificate_2876, certificate_2876_valid⟩, ⟨⟨certificate_2877, certificate_2877_valid⟩, ⟨⟨certificate_2878, certificate_2878_valid⟩, ⟨⟨certificate_2879, certificate_2879_valid⟩, ⟨⟨certificate_2880, certificate_2880_valid⟩, ⟨⟨certificate_2881, certificate_2881_valid⟩, ⟨⟨certificate_2882, certificate_2882_valid⟩, ⟨⟨certificate_2883, certificate_2883_valid⟩, ⟨⟨certificate_2884, certificate_2884_valid⟩, ⟨⟨certificate_2885, certificate_2885_valid⟩, ⟨⟨certificate_2886, certificate_2886_valid⟩, ⟨⟨certificate_2887, certificate_2887_valid⟩, ⟨⟨certificate_2888, certificate_2888_valid⟩, ⟨⟨certificate_2889, certificate_2889_valid⟩, ⟨⟨certificate_2890, certificate_2890_valid⟩, ⟨⟨certificate_2891, certificate_2891_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_41_verified_oai := @OAI.CycleClique.patterns_17_8_41_verified_oai
