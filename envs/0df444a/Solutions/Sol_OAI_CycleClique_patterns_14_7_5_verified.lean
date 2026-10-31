-- Prove2me | solution 1 for OAI.CycleClique.patterns_14_7_5_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:28:08.602793+00:00
-- url     : https://prove2.me/submissions/69ced5cd-2f83-404d-a69e-121e0dd810ec

import Mathlib
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates029
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_916_checked : certificate_916.Valid 14 7 13 certificate_916_q certificate_916_edges 6 4 [] := by decide +kernel
theorem certificate_916_valid : certificate_916.Valid 14 7 (patternOrder [[],[],[1,2,1,2]]) (patternClique [[],[],[1,2,1,2]]) (patternEdges [[],[],[1,2,1,2]]) (patternAmount [[],[],[1,2,1,2]]) (patternEdgeCount [[],[],[1,2,1,2]]) [] := certificate_916_checked

theorem certificate_917_checked : certificate_917.Valid 14 7 14 certificate_917_q certificate_917_edges 7 4 [] := by decide +kernel
theorem certificate_917_valid : certificate_917.Valid 14 7 (patternOrder [[],[],[1,2,1,3]]) (patternClique [[],[],[1,2,1,3]]) (patternEdges [[],[],[1,2,1,3]]) (patternAmount [[],[],[1,2,1,3]]) (patternEdgeCount [[],[],[1,2,1,3]]) [] := certificate_917_checked

theorem certificate_918_checked : certificate_918.Valid 14 7 13 certificate_918_q certificate_918_edges 6 4 [] := by decide +kernel
theorem certificate_918_valid : certificate_918.Valid 14 7 (patternOrder [[],[],[1,2,2,1]]) (patternClique [[],[],[1,2,2,1]]) (patternEdges [[],[],[1,2,2,1]]) (patternAmount [[],[],[1,2,2,1]]) (patternEdgeCount [[],[],[1,2,2,1]]) [] := certificate_918_checked

theorem certificate_919_checked : certificate_919.Valid 14 7 14 certificate_919_q certificate_919_edges 7 4 [] := by decide +kernel
theorem certificate_919_valid : certificate_919.Valid 14 7 (patternOrder [[],[],[1,2,2,2]]) (patternClique [[],[],[1,2,2,2]]) (patternEdges [[],[],[1,2,2,2]]) (patternAmount [[],[],[1,2,2,2]]) (patternEdgeCount [[],[],[1,2,2,2]]) [] := certificate_919_checked

theorem certificate_920_checked : certificate_920.Valid 14 7 14 certificate_920_q certificate_920_edges 7 4 [] := by decide +kernel
theorem certificate_920_valid : certificate_920.Valid 14 7 (patternOrder [[],[],[1,2,3,1]]) (patternClique [[],[],[1,2,3,1]]) (patternEdges [[],[],[1,2,3,1]]) (patternAmount [[],[],[1,2,3,1]]) (patternEdgeCount [[],[],[1,2,3,1]]) [] := certificate_920_checked

theorem certificate_921_checked : certificate_921.Valid 14 7 13 certificate_921_q certificate_921_edges 6 3 [] := by decide +kernel
theorem certificate_921_valid : certificate_921.Valid 14 7 (patternOrder [[],[],[1,3],[2]]) (patternClique [[],[],[1,3],[2]]) (patternEdges [[],[],[1,3],[2]]) (patternAmount [[],[],[1,3],[2]]) (patternEdgeCount [[],[],[1,3],[2]]) [] := certificate_921_checked

theorem certificate_922_checked : certificate_922.Valid 14 7 14 certificate_922_q certificate_922_edges 7 3 [] := by decide +kernel
theorem certificate_922_valid : certificate_922.Valid 14 7 (patternOrder [[],[],[1,3],[3]]) (patternClique [[],[],[1,3],[3]]) (patternEdges [[],[],[1,3],[3]]) (patternAmount [[],[],[1,3],[3]]) (patternEdgeCount [[],[],[1,3],[3]]) [] := certificate_922_checked

theorem certificate_923_checked : certificate_923.Valid 14 7 14 certificate_923_q certificate_923_edges 7 4 [] := by decide +kernel
theorem certificate_923_valid : certificate_923.Valid 14 7 (patternOrder [[],[],[1,3,1,2]]) (patternClique [[],[],[1,3,1,2]]) (patternEdges [[],[],[1,3,1,2]]) (patternAmount [[],[],[1,3,1,2]]) (patternEdgeCount [[],[],[1,3,1,2]]) [] := certificate_923_checked

theorem certificate_924_checked : certificate_924.Valid 14 7 14 certificate_924_q certificate_924_edges 7 3 [] := by decide +kernel
theorem certificate_924_valid : certificate_924.Valid 14 7 (patternOrder [[],[],[1,4],[2]]) (patternClique [[],[],[1,4],[2]]) (patternEdges [[],[],[1,4],[2]]) (patternAmount [[],[],[1,4],[2]]) (patternEdgeCount [[],[],[1,4],[2]]) [] := certificate_924_checked

theorem certificate_925_checked : certificate_925.Valid 14 7 13 certificate_925_q certificate_925_edges 6 3 [] := by decide +kernel
theorem certificate_925_valid : certificate_925.Valid 14 7 (patternOrder [[],[],[2],[2,2]]) (patternClique [[],[],[2],[2,2]]) (patternEdges [[],[],[2],[2,2]]) (patternAmount [[],[],[2],[2,2]]) (patternEdgeCount [[],[],[2],[2,2]]) [] := certificate_925_checked

theorem certificate_926_checked : certificate_926.Valid 14 7 14 certificate_926_q certificate_926_edges 7 3 [] := by decide +kernel
theorem certificate_926_valid : certificate_926.Valid 14 7 (patternOrder [[],[],[2],[2,3]]) (patternClique [[],[],[2],[2,3]]) (patternEdges [[],[],[2],[2,3]]) (patternAmount [[],[],[2],[2,3]]) (patternEdgeCount [[],[],[2],[2,3]]) [] := certificate_926_checked

theorem certificate_927_checked : certificate_927.Valid 14 7 13 certificate_927_q certificate_927_edges 6 4 [] := by decide +kernel
theorem certificate_927_valid : certificate_927.Valid 14 7 (patternOrder [[],[],[2,1,1,2]]) (patternClique [[],[],[2,1,1,2]]) (patternEdges [[],[],[2,1,1,2]]) (patternAmount [[],[],[2,1,1,2]]) (patternEdgeCount [[],[],[2,1,1,2]]) [] := certificate_927_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates030
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_928_checked : certificate_928.Valid 14 7 14 certificate_928_q certificate_928_edges 7 4 [] := by decide +kernel
theorem certificate_928_valid : certificate_928.Valid 14 7 (patternOrder [[],[],[2,1,1,3]]) (patternClique [[],[],[2,1,1,3]]) (patternEdges [[],[],[2,1,1,3]]) (patternAmount [[],[],[2,1,1,3]]) (patternEdgeCount [[],[],[2,1,1,3]]) [] := certificate_928_checked

theorem certificate_929_checked : certificate_929.Valid 14 7 14 certificate_929_q certificate_929_edges 7 4 [] := by decide +kernel
theorem certificate_929_valid : certificate_929.Valid 14 7 (patternOrder [[],[],[2,1,2,2]]) (patternClique [[],[],[2,1,2,2]]) (patternEdges [[],[],[2,1,2,2]]) (patternAmount [[],[],[2,1,2,2]]) (patternEdgeCount [[],[],[2,1,2,2]]) [] := certificate_929_checked

theorem certificate_930_checked : certificate_930.Valid 14 7 14 certificate_930_q certificate_930_edges 7 3 [] := by decide +kernel
theorem certificate_930_valid : certificate_930.Valid 14 7 (patternOrder [[],[],[2,2],[3]]) (patternClique [[],[],[2,2],[3]]) (patternEdges [[],[],[2,2],[3]]) (patternAmount [[],[],[2,2],[3]]) (patternEdgeCount [[],[],[2,2],[3]]) [] := certificate_930_checked

theorem certificate_931_checked : certificate_931.Valid 14 7 10 certificate_931_q certificate_931_edges 3 3 [] := by decide +kernel
theorem certificate_931_valid : certificate_931.Valid 14 7 (patternOrder [[],[1],[1],[1]]) (patternClique [[],[1],[1],[1]]) (patternEdges [[],[1],[1],[1]]) (patternAmount [[],[1],[1],[1]]) (patternEdgeCount [[],[1],[1],[1]]) [] := certificate_931_checked

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

theorem patterns_14_7_5_verified_oai : ∀ D ∈ patterns_14_7_5, PatternVerified 14 7 D := by

  simp only [patterns_14_7_5, List.forall_mem_cons]

  exact ⟨⟨certificate_916, certificate_916_valid⟩, ⟨⟨certificate_917, certificate_917_valid⟩, ⟨⟨certificate_918, certificate_918_valid⟩, ⟨⟨certificate_919, certificate_919_valid⟩, ⟨⟨certificate_920, certificate_920_valid⟩, ⟨⟨certificate_921, certificate_921_valid⟩, ⟨⟨certificate_922, certificate_922_valid⟩, ⟨⟨certificate_923, certificate_923_valid⟩, ⟨⟨certificate_924, certificate_924_valid⟩, ⟨⟨certificate_925, certificate_925_valid⟩, ⟨⟨certificate_926, certificate_926_valid⟩, ⟨⟨certificate_927, certificate_927_valid⟩, ⟨⟨certificate_928, certificate_928_valid⟩, ⟨⟨certificate_929, certificate_929_valid⟩, ⟨⟨certificate_930, certificate_930_valid⟩, ⟨⟨certificate_931, certificate_931_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_14_7_5_verified_oai := @OAI.CycleClique.patterns_14_7_5_verified_oai
