-- Prove2me | solution 1 for OAI.CycleClique.patterns_14_7_4_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:27:01.65259+00:00
-- url     : https://prove2.me/submissions/b451b1b4-50db-4c68-a547-1cbb3bd3fdf1

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

theorem certificate_900_checked : certificate_900.Valid 14 7 12 certificate_900_q certificate_900_edges 5 3 [] := by decide +kernel
theorem certificate_900_valid : certificate_900.Valid 14 7 (patternOrder [[],[],[1,1],[3]]) (patternClique [[],[],[1,1],[3]]) (patternEdges [[],[],[1,1],[3]]) (patternAmount [[],[],[1,1],[3]]) (patternEdgeCount [[],[],[1,1],[3]]) [] := certificate_900_checked

theorem certificate_901_checked : certificate_901.Valid 14 7 13 certificate_901_q certificate_901_edges 6 3 [] := by decide +kernel
theorem certificate_901_valid : certificate_901.Valid 14 7 (patternOrder [[],[],[1,1],[4]]) (patternClique [[],[],[1,1],[4]]) (patternEdges [[],[],[1,1],[4]]) (patternAmount [[],[],[1,1],[4]]) (patternEdgeCount [[],[],[1,1],[4]]) [] := certificate_901_checked

theorem certificate_902_checked : certificate_902.Valid 14 7 14 certificate_902_q certificate_902_edges 7 3 [] := by decide +kernel
theorem certificate_902_valid : certificate_902.Valid 14 7 (patternOrder [[],[],[1,1],[5]]) (patternClique [[],[],[1,1],[5]]) (patternEdges [[],[],[1,1],[5]]) (patternAmount [[],[],[1,1],[5]]) (patternEdgeCount [[],[],[1,1],[5]]) [] := certificate_902_checked

theorem certificate_903_checked : certificate_903.Valid 14 7 11 certificate_903_q certificate_903_edges 4 4 [] := by decide +kernel
theorem certificate_903_valid : certificate_903.Valid 14 7 (patternOrder [[],[],[1,1,1,1]]) (patternClique [[],[],[1,1,1,1]]) (patternEdges [[],[],[1,1,1,1]]) (patternAmount [[],[],[1,1,1,1]]) (patternEdgeCount [[],[],[1,1,1,1]]) [] := certificate_903_checked

theorem certificate_904_checked : certificate_904.Valid 14 7 12 certificate_904_q certificate_904_edges 5 4 [] := by decide +kernel
theorem certificate_904_valid : certificate_904.Valid 14 7 (patternOrder [[],[],[1,1,1,2]]) (patternClique [[],[],[1,1,1,2]]) (patternEdges [[],[],[1,1,1,2]]) (patternAmount [[],[],[1,1,1,2]]) (patternEdgeCount [[],[],[1,1,1,2]]) [] := certificate_904_checked

theorem certificate_905_checked : certificate_905.Valid 14 7 13 certificate_905_q certificate_905_edges 6 4 [] := by decide +kernel
theorem certificate_905_valid : certificate_905.Valid 14 7 (patternOrder [[],[],[1,1,1,3]]) (patternClique [[],[],[1,1,1,3]]) (patternEdges [[],[],[1,1,1,3]]) (patternAmount [[],[],[1,1,1,3]]) (patternEdgeCount [[],[],[1,1,1,3]]) [] := certificate_905_checked

theorem certificate_906_checked : certificate_906.Valid 14 7 14 certificate_906_q certificate_906_edges 7 4 [] := by decide +kernel
theorem certificate_906_valid : certificate_906.Valid 14 7 (patternOrder [[],[],[1,1,1,4]]) (patternClique [[],[],[1,1,1,4]]) (patternEdges [[],[],[1,1,1,4]]) (patternAmount [[],[],[1,1,1,4]]) (patternEdgeCount [[],[],[1,1,1,4]]) [] := certificate_906_checked

theorem certificate_907_checked : certificate_907.Valid 14 7 12 certificate_907_q certificate_907_edges 5 4 [] := by decide +kernel
theorem certificate_907_valid : certificate_907.Valid 14 7 (patternOrder [[],[],[1,1,2,1]]) (patternClique [[],[],[1,1,2,1]]) (patternEdges [[],[],[1,1,2,1]]) (patternAmount [[],[],[1,1,2,1]]) (patternEdgeCount [[],[],[1,1,2,1]]) [] := certificate_907_checked

theorem certificate_908_checked : certificate_908.Valid 14 7 13 certificate_908_q certificate_908_edges 6 4 [] := by decide +kernel
theorem certificate_908_valid : certificate_908.Valid 14 7 (patternOrder [[],[],[1,1,2,2]]) (patternClique [[],[],[1,1,2,2]]) (patternEdges [[],[],[1,1,2,2]]) (patternAmount [[],[],[1,1,2,2]]) (patternEdgeCount [[],[],[1,1,2,2]]) [] := certificate_908_checked

theorem certificate_909_checked : certificate_909.Valid 14 7 14 certificate_909_q certificate_909_edges 7 4 [] := by decide +kernel
theorem certificate_909_valid : certificate_909.Valid 14 7 (patternOrder [[],[],[1,1,2,3]]) (patternClique [[],[],[1,1,2,3]]) (patternEdges [[],[],[1,1,2,3]]) (patternAmount [[],[],[1,1,2,3]]) (patternEdgeCount [[],[],[1,1,2,3]]) [] := certificate_909_checked

theorem certificate_910_checked : certificate_910.Valid 14 7 13 certificate_910_q certificate_910_edges 6 4 [] := by decide +kernel
theorem certificate_910_valid : certificate_910.Valid 14 7 (patternOrder [[],[],[1,1,3,1]]) (patternClique [[],[],[1,1,3,1]]) (patternEdges [[],[],[1,1,3,1]]) (patternAmount [[],[],[1,1,3,1]]) (patternEdgeCount [[],[],[1,1,3,1]]) [] := certificate_910_checked

theorem certificate_911_checked : certificate_911.Valid 14 7 14 certificate_911_q certificate_911_edges 7 4 [] := by decide +kernel
theorem certificate_911_valid : certificate_911.Valid 14 7 (patternOrder [[],[],[1,1,3,2]]) (patternClique [[],[],[1,1,3,2]]) (patternEdges [[],[],[1,1,3,2]]) (patternAmount [[],[],[1,1,3,2]]) (patternEdgeCount [[],[],[1,1,3,2]]) [] := certificate_911_checked

theorem certificate_912_checked : certificate_912.Valid 14 7 14 certificate_912_q certificate_912_edges 7 4 [] := by decide +kernel
theorem certificate_912_valid : certificate_912.Valid 14 7 (patternOrder [[],[],[1,1,4,1]]) (patternClique [[],[],[1,1,4,1]]) (patternEdges [[],[],[1,1,4,1]]) (patternAmount [[],[],[1,1,4,1]]) (patternEdgeCount [[],[],[1,1,4,1]]) [] := certificate_912_checked

theorem certificate_913_checked : certificate_913.Valid 14 7 12 certificate_913_q certificate_913_edges 5 3 [] := by decide +kernel
theorem certificate_913_valid : certificate_913.Valid 14 7 (patternOrder [[],[],[1,2],[2]]) (patternClique [[],[],[1,2],[2]]) (patternEdges [[],[],[1,2],[2]]) (patternAmount [[],[],[1,2],[2]]) (patternEdgeCount [[],[],[1,2],[2]]) [] := certificate_913_checked

theorem certificate_914_checked : certificate_914.Valid 14 7 13 certificate_914_q certificate_914_edges 6 3 [] := by decide +kernel
theorem certificate_914_valid : certificate_914.Valid 14 7 (patternOrder [[],[],[1,2],[3]]) (patternClique [[],[],[1,2],[3]]) (patternEdges [[],[],[1,2],[3]]) (patternAmount [[],[],[1,2],[3]]) (patternEdgeCount [[],[],[1,2],[3]]) [] := certificate_914_checked

theorem certificate_915_checked : certificate_915.Valid 14 7 14 certificate_915_q certificate_915_edges 7 3 [] := by decide +kernel
theorem certificate_915_valid : certificate_915.Valid 14 7 (patternOrder [[],[],[1,2],[4]]) (patternClique [[],[],[1,2],[4]]) (patternEdges [[],[],[1,2],[4]]) (patternAmount [[],[],[1,2],[4]]) (patternEdgeCount [[],[],[1,2],[4]]) [] := certificate_915_checked

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

theorem patterns_14_7_4_verified_oai : ∀ D ∈ patterns_14_7_4, PatternVerified 14 7 D := by

  simp only [patterns_14_7_4, List.forall_mem_cons]

  exact ⟨⟨certificate_900, certificate_900_valid⟩, ⟨⟨certificate_901, certificate_901_valid⟩, ⟨⟨certificate_902, certificate_902_valid⟩, ⟨⟨certificate_903, certificate_903_valid⟩, ⟨⟨certificate_904, certificate_904_valid⟩, ⟨⟨certificate_905, certificate_905_valid⟩, ⟨⟨certificate_906, certificate_906_valid⟩, ⟨⟨certificate_907, certificate_907_valid⟩, ⟨⟨certificate_908, certificate_908_valid⟩, ⟨⟨certificate_909, certificate_909_valid⟩, ⟨⟨certificate_910, certificate_910_valid⟩, ⟨⟨certificate_911, certificate_911_valid⟩, ⟨⟨certificate_912, certificate_912_valid⟩, ⟨⟨certificate_913, certificate_913_valid⟩, ⟨⟨certificate_914, certificate_914_valid⟩, ⟨⟨certificate_915, certificate_915_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_14_7_4_verified_oai := @OAI.CycleClique.patterns_14_7_4_verified_oai
