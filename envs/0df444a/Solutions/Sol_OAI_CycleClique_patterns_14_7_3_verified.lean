-- Prove2me | solution 1 for OAI.CycleClique.patterns_14_7_3_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:24:25.415784+00:00
-- url     : https://prove2.me/submissions/732f6056-ddfb-4150-b573-0f1b4ad5f6fa

import Mathlib
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates028
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_884_checked : certificate_884.Valid 14 7 13 certificate_884_q certificate_884_edges 6 3 [] := by decide +kernel
theorem certificate_884_valid : certificate_884.Valid 14 7 (patternOrder [[],[],[],[2,2,2]]) (patternClique [[],[],[],[2,2,2]]) (patternEdges [[],[],[],[2,2,2]]) (patternAmount [[],[],[],[2,2,2]]) (patternEdgeCount [[],[],[],[2,2,2]]) [] := certificate_884_checked

theorem certificate_885_checked : certificate_885.Valid 14 7 14 certificate_885_q certificate_885_edges 7 3 [] := by decide +kernel
theorem certificate_885_valid : certificate_885.Valid 14 7 (patternOrder [[],[],[],[2,2,3]]) (patternClique [[],[],[],[2,2,3]]) (patternEdges [[],[],[],[2,2,3]]) (patternAmount [[],[],[],[2,2,3]]) (patternEdgeCount [[],[],[],[2,2,3]]) [] := certificate_885_checked

theorem certificate_886_checked : certificate_886.Valid 14 7 14 certificate_886_q certificate_886_edges 7 3 [] := by decide +kernel
theorem certificate_886_valid : certificate_886.Valid 14 7 (patternOrder [[],[],[],[2,3,2]]) (patternClique [[],[],[],[2,3,2]]) (patternEdges [[],[],[],[2,3,2]]) (patternAmount [[],[],[],[2,3,2]]) (patternEdgeCount [[],[],[],[2,3,2]]) [] := certificate_886_checked

theorem certificate_887_checked : certificate_887.Valid 14 7 13 certificate_887_q certificate_887_edges 6 2 [] := by decide +kernel
theorem certificate_887_valid : certificate_887.Valid 14 7 (patternOrder [[],[],[],[3],[3]]) (patternClique [[],[],[],[3],[3]]) (patternEdges [[],[],[],[3],[3]]) (patternAmount [[],[],[],[3],[3]]) (patternEdgeCount [[],[],[],[3],[3]]) [] := certificate_887_checked

theorem certificate_888_checked : certificate_888.Valid 14 7 14 certificate_888_q certificate_888_edges 7 2 [] := by decide +kernel
theorem certificate_888_valid : certificate_888.Valid 14 7 (patternOrder [[],[],[],[3],[4]]) (patternClique [[],[],[],[3],[4]]) (patternEdges [[],[],[],[3],[4]]) (patternAmount [[],[],[],[3],[4]]) (patternEdgeCount [[],[],[],[3],[4]]) [] := certificate_888_checked

theorem certificate_889_checked : certificate_889.Valid 14 7 14 certificate_889_q certificate_889_edges 7 3 [] := by decide +kernel
theorem certificate_889_valid : certificate_889.Valid 14 7 (patternOrder [[],[],[],[3,1,3]]) (patternClique [[],[],[],[3,1,3]]) (patternEdges [[],[],[],[3,1,3]]) (patternAmount [[],[],[],[3,1,3]]) (patternEdgeCount [[],[],[],[3,1,3]]) [] := certificate_889_checked

theorem certificate_890_checked : certificate_890.Valid 14 7 10 certificate_890_q certificate_890_edges 3 3 [] := by decide +kernel
theorem certificate_890_valid : certificate_890.Valid 14 7 (patternOrder [[],[],[1],[1,1]]) (patternClique [[],[],[1],[1,1]]) (patternEdges [[],[],[1],[1,1]]) (patternAmount [[],[],[1],[1,1]]) (patternEdgeCount [[],[],[1],[1,1]]) [] := certificate_890_checked

theorem certificate_891_checked : certificate_891.Valid 14 7 11 certificate_891_q certificate_891_edges 4 3 [] := by decide +kernel
theorem certificate_891_valid : certificate_891.Valid 14 7 (patternOrder [[],[],[1],[1,2]]) (patternClique [[],[],[1],[1,2]]) (patternEdges [[],[],[1],[1,2]]) (patternAmount [[],[],[1],[1,2]]) (patternEdgeCount [[],[],[1],[1,2]]) [] := certificate_891_checked

theorem certificate_892_checked : certificate_892.Valid 14 7 12 certificate_892_q certificate_892_edges 5 3 [] := by decide +kernel
theorem certificate_892_valid : certificate_892.Valid 14 7 (patternOrder [[],[],[1],[1,3]]) (patternClique [[],[],[1],[1,3]]) (patternEdges [[],[],[1],[1,3]]) (patternAmount [[],[],[1],[1,3]]) (patternEdgeCount [[],[],[1],[1,3]]) [] := certificate_892_checked

theorem certificate_893_checked : certificate_893.Valid 14 7 13 certificate_893_q certificate_893_edges 6 3 [] := by decide +kernel
theorem certificate_893_valid : certificate_893.Valid 14 7 (patternOrder [[],[],[1],[1,4]]) (patternClique [[],[],[1],[1,4]]) (patternEdges [[],[],[1],[1,4]]) (patternAmount [[],[],[1],[1,4]]) (patternEdgeCount [[],[],[1],[1,4]]) [] := certificate_893_checked

theorem certificate_894_checked : certificate_894.Valid 14 7 14 certificate_894_q certificate_894_edges 7 3 [] := by decide +kernel
theorem certificate_894_valid : certificate_894.Valid 14 7 (patternOrder [[],[],[1],[1,5]]) (patternClique [[],[],[1],[1,5]]) (patternEdges [[],[],[1],[1,5]]) (patternAmount [[],[],[1],[1,5]]) (patternEdgeCount [[],[],[1],[1,5]]) [] := certificate_894_checked

theorem certificate_895_checked : certificate_895.Valid 14 7 12 certificate_895_q certificate_895_edges 5 3 [] := by decide +kernel
theorem certificate_895_valid : certificate_895.Valid 14 7 (patternOrder [[],[],[1],[2,2]]) (patternClique [[],[],[1],[2,2]]) (patternEdges [[],[],[1],[2,2]]) (patternAmount [[],[],[1],[2,2]]) (patternEdgeCount [[],[],[1],[2,2]]) [] := certificate_895_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates029
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_896_checked : certificate_896.Valid 14 7 13 certificate_896_q certificate_896_edges 6 3 [] := by decide +kernel
theorem certificate_896_valid : certificate_896.Valid 14 7 (patternOrder [[],[],[1],[2,3]]) (patternClique [[],[],[1],[2,3]]) (patternEdges [[],[],[1],[2,3]]) (patternAmount [[],[],[1],[2,3]]) (patternEdgeCount [[],[],[1],[2,3]]) [] := certificate_896_checked

theorem certificate_897_checked : certificate_897.Valid 14 7 14 certificate_897_q certificate_897_edges 7 3 [] := by decide +kernel
theorem certificate_897_valid : certificate_897.Valid 14 7 (patternOrder [[],[],[1],[2,4]]) (patternClique [[],[],[1],[2,4]]) (patternEdges [[],[],[1],[2,4]]) (patternAmount [[],[],[1],[2,4]]) (patternEdgeCount [[],[],[1],[2,4]]) [] := certificate_897_checked

theorem certificate_898_checked : certificate_898.Valid 14 7 14 certificate_898_q certificate_898_edges 7 3 [] := by decide +kernel
theorem certificate_898_valid : certificate_898.Valid 14 7 (patternOrder [[],[],[1],[3,3]]) (patternClique [[],[],[1],[3,3]]) (patternEdges [[],[],[1],[3,3]]) (patternAmount [[],[],[1],[3,3]]) (patternEdgeCount [[],[],[1],[3,3]]) [] := certificate_898_checked

theorem certificate_899_checked : certificate_899.Valid 14 7 11 certificate_899_q certificate_899_edges 4 3 [] := by decide +kernel
theorem certificate_899_valid : certificate_899.Valid 14 7 (patternOrder [[],[],[1,1],[2]]) (patternClique [[],[],[1,1],[2]]) (patternEdges [[],[],[1,1],[2]]) (patternAmount [[],[],[1,1],[2]]) (patternEdgeCount [[],[],[1,1],[2]]) [] := certificate_899_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns14x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_14_7_3_verified_oai : ∀ D ∈ patterns_14_7_3, PatternVerified 14 7 D := by

  simp only [patterns_14_7_3, List.forall_mem_cons]

  exact ⟨⟨certificate_884, certificate_884_valid⟩, ⟨⟨certificate_885, certificate_885_valid⟩, ⟨⟨certificate_886, certificate_886_valid⟩, ⟨⟨certificate_887, certificate_887_valid⟩, ⟨⟨certificate_888, certificate_888_valid⟩, ⟨⟨certificate_889, certificate_889_valid⟩, ⟨⟨certificate_890, certificate_890_valid⟩, ⟨⟨certificate_891, certificate_891_valid⟩, ⟨⟨certificate_892, certificate_892_valid⟩, ⟨⟨certificate_893, certificate_893_valid⟩, ⟨⟨certificate_894, certificate_894_valid⟩, ⟨⟨certificate_895, certificate_895_valid⟩, ⟨⟨certificate_896, certificate_896_valid⟩, ⟨⟨certificate_897, certificate_897_valid⟩, ⟨⟨certificate_898, certificate_898_valid⟩, ⟨⟨certificate_899, certificate_899_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_14_7_3_verified_oai := @OAI.CycleClique.patterns_14_7_3_verified_oai
