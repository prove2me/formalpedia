-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_43_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:51:04.667985+00:00
-- url     : https://prove2.me/submissions/3fb6d25e-3e0f-43f6-8685-f7941e85520e

import Mathlib
import Definitions.Def_OAIQ107D132
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates091
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2908_checked : certificate_2908.Valid 17 8 17 certificate_2908_q certificate_2908_edges 9 6 [] := by decide +kernel
theorem certificate_2908_valid : certificate_2908.Valid 17 8 (patternOrder [[1],[1,1,1,1,4]]) (patternClique [[1],[1,1,1,1,4]]) (patternEdges [[1],[1,1,1,1,4]]) (patternAmount [[1],[1,1,1,1,4]]) (patternEdgeCount [[1],[1,1,1,1,4]]) [] := certificate_2908_checked

theorem certificate_2909_checked : certificate_2909.Valid 17 8 15 certificate_2909_q certificate_2909_edges 7 6 [] := by decide +kernel
theorem certificate_2909_valid : certificate_2909.Valid 17 8 (patternOrder [[1],[1,1,1,2,1]]) (patternClique [[1],[1,1,1,2,1]]) (patternEdges [[1],[1,1,1,2,1]]) (patternAmount [[1],[1,1,1,2,1]]) (patternEdgeCount [[1],[1,1,1,2,1]]) [] := certificate_2909_checked

theorem certificate_2910_checked : certificate_2910.Valid 17 8 16 certificate_2910_q certificate_2910_edges 8 6 [] := by decide +kernel
theorem certificate_2910_valid : certificate_2910.Valid 17 8 (patternOrder [[1],[1,1,1,2,2]]) (patternClique [[1],[1,1,1,2,2]]) (patternEdges [[1],[1,1,1,2,2]]) (patternAmount [[1],[1,1,1,2,2]]) (patternEdgeCount [[1],[1,1,1,2,2]]) [] := certificate_2910_checked

theorem certificate_2911_checked : certificate_2911.Valid 17 8 17 certificate_2911_q certificate_2911_edges 9 6 [] := by decide +kernel
theorem certificate_2911_valid : certificate_2911.Valid 17 8 (patternOrder [[1],[1,1,1,2,3]]) (patternClique [[1],[1,1,1,2,3]]) (patternEdges [[1],[1,1,1,2,3]]) (patternAmount [[1],[1,1,1,2,3]]) (patternEdgeCount [[1],[1,1,1,2,3]]) [] := certificate_2911_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates092
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2912_checked : certificate_2912.Valid 17 8 16 certificate_2912_q certificate_2912_edges 8 6 [] := by decide +kernel
theorem certificate_2912_valid : certificate_2912.Valid 17 8 (patternOrder [[1],[1,1,1,3,1]]) (patternClique [[1],[1,1,1,3,1]]) (patternEdges [[1],[1,1,1,3,1]]) (patternAmount [[1],[1,1,1,3,1]]) (patternEdgeCount [[1],[1,1,1,3,1]]) [] := certificate_2912_checked

theorem certificate_2913_checked : certificate_2913.Valid 17 8 17 certificate_2913_q certificate_2913_edges 9 6 [] := by decide +kernel
theorem certificate_2913_valid : certificate_2913.Valid 17 8 (patternOrder [[1],[1,1,1,3,2]]) (patternClique [[1],[1,1,1,3,2]]) (patternEdges [[1],[1,1,1,3,2]]) (patternAmount [[1],[1,1,1,3,2]]) (patternEdgeCount [[1],[1,1,1,3,2]]) [] := certificate_2913_checked

theorem certificate_2914_checked : certificate_2914.Valid 17 8 17 certificate_2914_q certificate_2914_edges 9 6 [] := by decide +kernel
theorem certificate_2914_valid : certificate_2914.Valid 17 8 (patternOrder [[1],[1,1,1,4,1]]) (patternClique [[1],[1,1,1,4,1]]) (patternEdges [[1],[1,1,1,4,1]]) (patternAmount [[1],[1,1,1,4,1]]) (patternEdgeCount [[1],[1,1,1,4,1]]) [] := certificate_2914_checked

theorem certificate_2915_checked : certificate_2915.Valid 17 8 15 certificate_2915_q certificate_2915_edges 7 5 [] := by decide +kernel
theorem certificate_2915_valid : certificate_2915.Valid 17 8 (patternOrder [[1],[1,1,2],[2]]) (patternClique [[1],[1,1,2],[2]]) (patternEdges [[1],[1,1,2],[2]]) (patternAmount [[1],[1,1,2],[2]]) (patternEdgeCount [[1],[1,1,2],[2]]) [] := certificate_2915_checked

theorem certificate_2916_checked : certificate_2916.Valid 17 8 16 certificate_2916_q certificate_2916_edges 8 5 [] := by decide +kernel
theorem certificate_2916_valid : certificate_2916.Valid 17 8 (patternOrder [[1],[1,1,2],[3]]) (patternClique [[1],[1,1,2],[3]]) (patternEdges [[1],[1,1,2],[3]]) (patternAmount [[1],[1,1,2],[3]]) (patternEdgeCount [[1],[1,1,2],[3]]) [] := certificate_2916_checked

theorem certificate_2917_checked : certificate_2917.Valid 17 8 17 certificate_2917_q certificate_2917_edges 9 5 [] := by decide +kernel
theorem certificate_2917_valid : certificate_2917.Valid 17 8 (patternOrder [[1],[1,1,2],[4]]) (patternClique [[1],[1,1,2],[4]]) (patternEdges [[1],[1,1,2],[4]]) (patternAmount [[1],[1,1,2],[4]]) (patternEdgeCount [[1],[1,1,2],[4]]) [] := certificate_2917_checked

theorem certificate_2918_checked : certificate_2918.Valid 17 8 15 certificate_2918_q certificate_2918_edges 7 6 [] := by decide +kernel
theorem certificate_2918_valid : certificate_2918.Valid 17 8 (patternOrder [[1],[1,1,2,1,1]]) (patternClique [[1],[1,1,2,1,1]]) (patternEdges [[1],[1,1,2,1,1]]) (patternAmount [[1],[1,1,2,1,1]]) (patternEdgeCount [[1],[1,1,2,1,1]]) [] := certificate_2918_checked

theorem certificate_2919_checked : certificate_2919.Valid 17 8 16 certificate_2919_q certificate_2919_edges 8 6 [] := by decide +kernel
theorem certificate_2919_valid : certificate_2919.Valid 17 8 (patternOrder [[1],[1,1,2,1,2]]) (patternClique [[1],[1,1,2,1,2]]) (patternEdges [[1],[1,1,2,1,2]]) (patternAmount [[1],[1,1,2,1,2]]) (patternEdgeCount [[1],[1,1,2,1,2]]) [] := certificate_2919_checked

theorem certificate_2920_checked : certificate_2920.Valid 17 8 17 certificate_2920_q certificate_2920_edges 9 6 [] := by decide +kernel
theorem certificate_2920_valid : certificate_2920.Valid 17 8 (patternOrder [[1],[1,1,2,1,3]]) (patternClique [[1],[1,1,2,1,3]]) (patternEdges [[1],[1,1,2,1,3]]) (patternAmount [[1],[1,1,2,1,3]]) (patternEdgeCount [[1],[1,1,2,1,3]]) [] := certificate_2920_checked

theorem certificate_2921_checked : certificate_2921.Valid 17 8 16 certificate_2921_q certificate_2921_edges 8 6 [] := by decide +kernel
theorem certificate_2921_valid : certificate_2921.Valid 17 8 (patternOrder [[1],[1,1,2,2,1]]) (patternClique [[1],[1,1,2,2,1]]) (patternEdges [[1],[1,1,2,2,1]]) (patternAmount [[1],[1,1,2,2,1]]) (patternEdgeCount [[1],[1,1,2,2,1]]) [] := certificate_2921_checked

theorem certificate_2922_checked : certificate_2922.Valid 17 8 17 certificate_2922_q certificate_2922_edges 9 6 [] := by decide +kernel
theorem certificate_2922_valid : certificate_2922.Valid 17 8 (patternOrder [[1],[1,1,2,2,2]]) (patternClique [[1],[1,1,2,2,2]]) (patternEdges [[1],[1,1,2,2,2]]) (patternAmount [[1],[1,1,2,2,2]]) (patternEdgeCount [[1],[1,1,2,2,2]]) [] := certificate_2922_checked

theorem certificate_2923_checked : certificate_2923.Valid 17 8 17 certificate_2923_q certificate_2923_edges 9 6 [] := by decide +kernel
theorem certificate_2923_valid : certificate_2923.Valid 17 8 (patternOrder [[1],[1,1,2,3,1]]) (patternClique [[1],[1,1,2,3,1]]) (patternEdges [[1],[1,1,2,3,1]]) (patternAmount [[1],[1,1,2,3,1]]) (patternEdgeCount [[1],[1,1,2,3,1]]) [] := certificate_2923_checked

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

theorem patterns_17_8_43_verified_oai : ∀ D ∈ patterns_17_8_43, PatternVerified 17 8 D := by

  simp only [patterns_17_8_43, List.forall_mem_cons]

  exact ⟨⟨certificate_2908, certificate_2908_valid⟩, ⟨⟨certificate_2909, certificate_2909_valid⟩, ⟨⟨certificate_2910, certificate_2910_valid⟩, ⟨⟨certificate_2911, certificate_2911_valid⟩, ⟨⟨certificate_2912, certificate_2912_valid⟩, ⟨⟨certificate_2913, certificate_2913_valid⟩, ⟨⟨certificate_2914, certificate_2914_valid⟩, ⟨⟨certificate_2915, certificate_2915_valid⟩, ⟨⟨certificate_2916, certificate_2916_valid⟩, ⟨⟨certificate_2917, certificate_2917_valid⟩, ⟨⟨certificate_2918, certificate_2918_valid⟩, ⟨⟨certificate_2919, certificate_2919_valid⟩, ⟨⟨certificate_2920, certificate_2920_valid⟩, ⟨⟨certificate_2921, certificate_2921_valid⟩, ⟨⟨certificate_2922, certificate_2922_valid⟩, ⟨⟨certificate_2923, certificate_2923_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_43_verified_oai := @OAI.CycleClique.patterns_17_8_43_verified_oai
