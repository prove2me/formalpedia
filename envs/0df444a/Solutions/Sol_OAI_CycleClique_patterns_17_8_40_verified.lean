-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_40_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:46:00.913455+00:00
-- url     : https://prove2.me/submissions/603795d5-d892-4926-bcf5-3c733f5d0477

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

theorem certificate_2860_checked : certificate_2860.Valid 17 8 14 certificate_2860_q certificate_2860_edges 6 4 [] := by decide +kernel
theorem certificate_2860_valid : certificate_2860.Valid 17 8 (patternOrder [[1],[1],[1],[3]]) (patternClique [[1],[1],[1],[3]]) (patternEdges [[1],[1],[1],[3]]) (patternAmount [[1],[1],[1],[3]]) (patternEdgeCount [[1],[1],[1],[3]]) [] := certificate_2860_checked

theorem certificate_2861_checked : certificate_2861.Valid 17 8 15 certificate_2861_q certificate_2861_edges 7 4 [] := by decide +kernel
theorem certificate_2861_valid : certificate_2861.Valid 17 8 (patternOrder [[1],[1],[1],[4]]) (patternClique [[1],[1],[1],[4]]) (patternEdges [[1],[1],[1],[4]]) (patternAmount [[1],[1],[1],[4]]) (patternEdgeCount [[1],[1],[1],[4]]) [] := certificate_2861_checked

theorem certificate_2862_checked : certificate_2862.Valid 17 8 16 certificate_2862_q certificate_2862_edges 8 4 [] := by decide +kernel
theorem certificate_2862_valid : certificate_2862.Valid 17 8 (patternOrder [[1],[1],[1],[5]]) (patternClique [[1],[1],[1],[5]]) (patternEdges [[1],[1],[1],[5]]) (patternAmount [[1],[1],[1],[5]]) (patternEdgeCount [[1],[1],[1],[5]]) [] := certificate_2862_checked

theorem certificate_2863_checked : certificate_2863.Valid 17 8 17 certificate_2863_q certificate_2863_edges 9 4 [] := by decide +kernel
theorem certificate_2863_valid : certificate_2863.Valid 17 8 (patternOrder [[1],[1],[1],[6]]) (patternClique [[1],[1],[1],[6]]) (patternEdges [[1],[1],[1],[6]]) (patternAmount [[1],[1],[1],[6]]) (patternEdgeCount [[1],[1],[1],[6]]) [] := certificate_2863_checked

theorem certificate_2864_checked : certificate_2864.Valid 17 8 13 certificate_2864_q certificate_2864_edges 5 5 [] := by decide +kernel
theorem certificate_2864_valid : certificate_2864.Valid 17 8 (patternOrder [[1],[1],[1,1,1]]) (patternClique [[1],[1],[1,1,1]]) (patternEdges [[1],[1],[1,1,1]]) (patternAmount [[1],[1],[1,1,1]]) (patternEdgeCount [[1],[1],[1,1,1]]) [] := certificate_2864_checked

theorem certificate_2865_checked : certificate_2865.Valid 17 8 14 certificate_2865_q certificate_2865_edges 6 5 [] := by decide +kernel
theorem certificate_2865_valid : certificate_2865.Valid 17 8 (patternOrder [[1],[1],[1,1,2]]) (patternClique [[1],[1],[1,1,2]]) (patternEdges [[1],[1],[1,1,2]]) (patternAmount [[1],[1],[1,1,2]]) (patternEdgeCount [[1],[1],[1,1,2]]) [] := certificate_2865_checked

theorem certificate_2866_checked : certificate_2866.Valid 17 8 15 certificate_2866_q certificate_2866_edges 7 5 [] := by decide +kernel
theorem certificate_2866_valid : certificate_2866.Valid 17 8 (patternOrder [[1],[1],[1,1,3]]) (patternClique [[1],[1],[1,1,3]]) (patternEdges [[1],[1],[1,1,3]]) (patternAmount [[1],[1],[1,1,3]]) (patternEdgeCount [[1],[1],[1,1,3]]) [] := certificate_2866_checked

theorem certificate_2867_checked : certificate_2867.Valid 17 8 16 certificate_2867_q certificate_2867_edges 8 5 [] := by decide +kernel
theorem certificate_2867_valid : certificate_2867.Valid 17 8 (patternOrder [[1],[1],[1,1,4]]) (patternClique [[1],[1],[1,1,4]]) (patternEdges [[1],[1],[1,1,4]]) (patternAmount [[1],[1],[1,1,4]]) (patternEdgeCount [[1],[1],[1,1,4]]) [] := certificate_2867_checked

theorem certificate_2868_checked : certificate_2868.Valid 17 8 17 certificate_2868_q certificate_2868_edges 9 5 [] := by decide +kernel
theorem certificate_2868_valid : certificate_2868.Valid 17 8 (patternOrder [[1],[1],[1,1,5]]) (patternClique [[1],[1],[1,1,5]]) (patternEdges [[1],[1],[1,1,5]]) (patternAmount [[1],[1],[1,1,5]]) (patternEdgeCount [[1],[1],[1,1,5]]) [] := certificate_2868_checked

theorem certificate_2869_checked : certificate_2869.Valid 17 8 14 certificate_2869_q certificate_2869_edges 6 5 [] := by decide +kernel
theorem certificate_2869_valid : certificate_2869.Valid 17 8 (patternOrder [[1],[1],[1,2,1]]) (patternClique [[1],[1],[1,2,1]]) (patternEdges [[1],[1],[1,2,1]]) (patternAmount [[1],[1],[1,2,1]]) (patternEdgeCount [[1],[1],[1,2,1]]) [] := certificate_2869_checked

theorem certificate_2870_checked : certificate_2870.Valid 17 8 15 certificate_2870_q certificate_2870_edges 7 5 [] := by decide +kernel
theorem certificate_2870_valid : certificate_2870.Valid 17 8 (patternOrder [[1],[1],[1,2,2]]) (patternClique [[1],[1],[1,2,2]]) (patternEdges [[1],[1],[1,2,2]]) (patternAmount [[1],[1],[1,2,2]]) (patternEdgeCount [[1],[1],[1,2,2]]) [] := certificate_2870_checked

theorem certificate_2871_checked : certificate_2871.Valid 17 8 16 certificate_2871_q certificate_2871_edges 8 5 [] := by decide +kernel
theorem certificate_2871_valid : certificate_2871.Valid 17 8 (patternOrder [[1],[1],[1,2,3]]) (patternClique [[1],[1],[1,2,3]]) (patternEdges [[1],[1],[1,2,3]]) (patternAmount [[1],[1],[1,2,3]]) (patternEdgeCount [[1],[1],[1,2,3]]) [] := certificate_2871_checked

theorem certificate_2872_checked : certificate_2872.Valid 17 8 17 certificate_2872_q certificate_2872_edges 9 5 [] := by decide +kernel
theorem certificate_2872_valid : certificate_2872.Valid 17 8 (patternOrder [[1],[1],[1,2,4]]) (patternClique [[1],[1],[1,2,4]]) (patternEdges [[1],[1],[1,2,4]]) (patternAmount [[1],[1],[1,2,4]]) (patternEdgeCount [[1],[1],[1,2,4]]) [] := certificate_2872_checked

theorem certificate_2873_checked : certificate_2873.Valid 17 8 15 certificate_2873_q certificate_2873_edges 7 5 [] := by decide +kernel
theorem certificate_2873_valid : certificate_2873.Valid 17 8 (patternOrder [[1],[1],[1,3,1]]) (patternClique [[1],[1],[1,3,1]]) (patternEdges [[1],[1],[1,3,1]]) (patternAmount [[1],[1],[1,3,1]]) (patternEdgeCount [[1],[1],[1,3,1]]) [] := certificate_2873_checked

theorem certificate_2874_checked : certificate_2874.Valid 17 8 16 certificate_2874_q certificate_2874_edges 8 5 [] := by decide +kernel
theorem certificate_2874_valid : certificate_2874.Valid 17 8 (patternOrder [[1],[1],[1,3,2]]) (patternClique [[1],[1],[1,3,2]]) (patternEdges [[1],[1],[1,3,2]]) (patternAmount [[1],[1],[1,3,2]]) (patternEdgeCount [[1],[1],[1,3,2]]) [] := certificate_2874_checked

theorem certificate_2875_checked : certificate_2875.Valid 17 8 17 certificate_2875_q certificate_2875_edges 9 5 [] := by decide +kernel
theorem certificate_2875_valid : certificate_2875.Valid 17 8 (patternOrder [[1],[1],[1,3,3]]) (patternClique [[1],[1],[1,3,3]]) (patternEdges [[1],[1],[1,3,3]]) (patternAmount [[1],[1],[1,3,3]]) (patternEdgeCount [[1],[1],[1,3,3]]) [] := certificate_2875_checked

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

theorem patterns_17_8_40_verified_oai : ∀ D ∈ patterns_17_8_40, PatternVerified 17 8 D := by

  simp only [patterns_17_8_40, List.forall_mem_cons]

  exact ⟨⟨certificate_2860, certificate_2860_valid⟩, ⟨⟨certificate_2861, certificate_2861_valid⟩, ⟨⟨certificate_2862, certificate_2862_valid⟩, ⟨⟨certificate_2863, certificate_2863_valid⟩, ⟨⟨certificate_2864, certificate_2864_valid⟩, ⟨⟨certificate_2865, certificate_2865_valid⟩, ⟨⟨certificate_2866, certificate_2866_valid⟩, ⟨⟨certificate_2867, certificate_2867_valid⟩, ⟨⟨certificate_2868, certificate_2868_valid⟩, ⟨⟨certificate_2869, certificate_2869_valid⟩, ⟨⟨certificate_2870, certificate_2870_valid⟩, ⟨⟨certificate_2871, certificate_2871_valid⟩, ⟨⟨certificate_2872, certificate_2872_valid⟩, ⟨⟨certificate_2873, certificate_2873_valid⟩, ⟨⟨certificate_2874, certificate_2874_valid⟩, ⟨⟨certificate_2875, certificate_2875_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_40_verified_oai := @OAI.CycleClique.patterns_17_8_40_verified_oai
