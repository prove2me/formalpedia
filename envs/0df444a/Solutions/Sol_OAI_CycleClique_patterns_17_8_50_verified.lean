-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_50_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:57:37.971996+00:00
-- url     : https://prove2.me/submissions/a6d68170-e4db-4959-9be5-41b0412a157d

import Mathlib
import Definitions.Def_OAIQ107D005
import Definitions.Def_OAIQ107D102
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates095
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_3020_checked : certificate_3020.Valid 17 8 17 certificate_3020_q certificate_3020_edges 9 6 [] := by decide +kernel
theorem certificate_3020_valid : certificate_3020.Valid 17 8 (patternOrder [[1,1,1,1],[1,4]]) (patternClique [[1,1,1,1],[1,4]]) (patternEdges [[1,1,1,1],[1,4]]) (patternAmount [[1,1,1,1],[1,4]]) (patternEdgeCount [[1,1,1,1],[1,4]]) [] := certificate_3020_checked

theorem certificate_3021_checked : certificate_3021.Valid 17 8 16 certificate_3021_q certificate_3021_edges 8 6 [] := by decide +kernel
theorem certificate_3021_valid : certificate_3021.Valid 17 8 (patternOrder [[1,1,1,1],[2,2]]) (patternClique [[1,1,1,1],[2,2]]) (patternEdges [[1,1,1,1],[2,2]]) (patternAmount [[1,1,1,1],[2,2]]) (patternEdgeCount [[1,1,1,1],[2,2]]) [] := certificate_3021_checked

theorem certificate_3022_checked : certificate_3022.Valid 17 8 17 certificate_3022_q certificate_3022_edges 9 6 [] := by decide +kernel
theorem certificate_3022_valid : certificate_3022.Valid 17 8 (patternOrder [[1,1,1,1],[2,3]]) (patternClique [[1,1,1,1],[2,3]]) (patternEdges [[1,1,1,1],[2,3]]) (patternAmount [[1,1,1,1],[2,3]]) (patternEdgeCount [[1,1,1,1],[2,3]]) [] := certificate_3022_checked

theorem certificate_3023_checked : certificate_3023.Valid 17 8 15 certificate_3023_q certificate_3023_edges 7 6 [] := by decide +kernel
theorem certificate_3023_valid : certificate_3023.Valid 17 8 (patternOrder [[1,1,1,1,1],[2]]) (patternClique [[1,1,1,1,1],[2]]) (patternEdges [[1,1,1,1,1],[2]]) (patternAmount [[1,1,1,1,1],[2]]) (patternEdgeCount [[1,1,1,1,1],[2]]) [] := certificate_3023_checked

theorem certificate_3024_checked : certificate_3024.Valid 17 8 16 certificate_3024_q certificate_3024_edges 8 6 [] := by decide +kernel
theorem certificate_3024_valid : certificate_3024.Valid 17 8 (patternOrder [[1,1,1,1,1],[3]]) (patternClique [[1,1,1,1,1],[3]]) (patternEdges [[1,1,1,1,1],[3]]) (patternAmount [[1,1,1,1,1],[3]]) (patternEdgeCount [[1,1,1,1,1],[3]]) [] := certificate_3024_checked

theorem certificate_3025_checked : certificate_3025.Valid 17 8 17 certificate_3025_q certificate_3025_edges 9 6 [] := by decide +kernel
theorem certificate_3025_valid : certificate_3025.Valid 17 8 (patternOrder [[1,1,1,1,1],[4]]) (patternClique [[1,1,1,1,1],[4]]) (patternEdges [[1,1,1,1,1],[4]]) (patternAmount [[1,1,1,1,1],[4]]) (patternEdgeCount [[1,1,1,1,1],[4]]) [] := certificate_3025_checked

theorem certificate_3026_checked : certificate_3026.Valid 17 8 15 certificate_3026_q certificate_3026_edges 7 7 [] := by decide +kernel
theorem certificate_3026_valid : certificate_3026.Valid 17 8 (patternOrder [[1,1,1,1,1,1,1]]) (patternClique [[1,1,1,1,1,1,1]]) (patternEdges [[1,1,1,1,1,1,1]]) (patternAmount [[1,1,1,1,1,1,1]]) (patternEdgeCount [[1,1,1,1,1,1,1]]) [] := certificate_3026_checked

theorem certificate_3027_checked : certificate_3027.Valid 17 8 16 certificate_3027_q certificate_3027_edges 8 7 [] := by decide +kernel
theorem certificate_3027_valid : certificate_3027.Valid 17 8 (patternOrder [[1,1,1,1,1,1,2]]) (patternClique [[1,1,1,1,1,1,2]]) (patternEdges [[1,1,1,1,1,1,2]]) (patternAmount [[1,1,1,1,1,1,2]]) (patternEdgeCount [[1,1,1,1,1,1,2]]) [] := certificate_3027_checked

theorem certificate_3028_checked : certificate_3028.Valid 17 8 17 certificate_3028_q certificate_3028_edges 9 7 [] := by decide +kernel
theorem certificate_3028_valid : certificate_3028.Valid 17 8 (patternOrder [[1,1,1,1,1,1,3]]) (patternClique [[1,1,1,1,1,1,3]]) (patternEdges [[1,1,1,1,1,1,3]]) (patternAmount [[1,1,1,1,1,1,3]]) (patternEdgeCount [[1,1,1,1,1,1,3]]) [] := certificate_3028_checked

theorem certificate_3029_checked : certificate_3029.Valid 17 8 16 certificate_3029_q certificate_3029_edges 8 7 [] := by decide +kernel
theorem certificate_3029_valid : certificate_3029.Valid 17 8 (patternOrder [[1,1,1,1,1,2,1]]) (patternClique [[1,1,1,1,1,2,1]]) (patternEdges [[1,1,1,1,1,2,1]]) (patternAmount [[1,1,1,1,1,2,1]]) (patternEdgeCount [[1,1,1,1,1,2,1]]) [] := certificate_3029_checked

theorem certificate_3030_checked : certificate_3030.Valid 17 8 17 certificate_3030_q certificate_3030_edges 9 7 [] := by decide +kernel
theorem certificate_3030_valid : certificate_3030.Valid 17 8 (patternOrder [[1,1,1,1,1,2,2]]) (patternClique [[1,1,1,1,1,2,2]]) (patternEdges [[1,1,1,1,1,2,2]]) (patternAmount [[1,1,1,1,1,2,2]]) (patternEdgeCount [[1,1,1,1,1,2,2]]) [] := certificate_3030_checked

theorem certificate_3031_checked : certificate_3031.Valid 17 8 17 certificate_3031_q certificate_3031_edges 9 7 [] := by decide +kernel
theorem certificate_3031_valid : certificate_3031.Valid 17 8 (patternOrder [[1,1,1,1,1,3,1]]) (patternClique [[1,1,1,1,1,3,1]]) (patternEdges [[1,1,1,1,1,3,1]]) (patternAmount [[1,1,1,1,1,3,1]]) (patternEdgeCount [[1,1,1,1,1,3,1]]) [] := certificate_3031_checked

theorem certificate_3032_checked : certificate_3032.Valid 17 8 16 certificate_3032_q certificate_3032_edges 8 6 [] := by decide +kernel
theorem certificate_3032_valid : certificate_3032.Valid 17 8 (patternOrder [[1,1,1,1,2],[2]]) (patternClique [[1,1,1,1,2],[2]]) (patternEdges [[1,1,1,1,2],[2]]) (patternAmount [[1,1,1,1,2],[2]]) (patternEdgeCount [[1,1,1,1,2],[2]]) [] := certificate_3032_checked

theorem certificate_3033_checked : certificate_3033.Valid 17 8 17 certificate_3033_q certificate_3033_edges 9 6 [] := by decide +kernel
theorem certificate_3033_valid : certificate_3033.Valid 17 8 (patternOrder [[1,1,1,1,2],[3]]) (patternClique [[1,1,1,1,2],[3]]) (patternEdges [[1,1,1,1,2],[3]]) (patternAmount [[1,1,1,1,2],[3]]) (patternEdgeCount [[1,1,1,1,2],[3]]) [] := certificate_3033_checked

theorem certificate_3034_checked : certificate_3034.Valid 17 8 16 certificate_3034_q certificate_3034_edges 8 7 [] := by decide +kernel
theorem certificate_3034_valid : certificate_3034.Valid 17 8 (patternOrder [[1,1,1,1,2,1,1]]) (patternClique [[1,1,1,1,2,1,1]]) (patternEdges [[1,1,1,1,2,1,1]]) (patternAmount [[1,1,1,1,2,1,1]]) (patternEdgeCount [[1,1,1,1,2,1,1]]) [] := certificate_3034_checked

theorem certificate_3035_checked : certificate_3035.Valid 17 8 17 certificate_3035_q certificate_3035_edges 9 7 [] := by decide +kernel
theorem certificate_3035_valid : certificate_3035.Valid 17 8 (patternOrder [[1,1,1,1,2,1,2]]) (patternClique [[1,1,1,1,2,1,2]]) (patternEdges [[1,1,1,1,2,1,2]]) (patternAmount [[1,1,1,1,2,1,2]]) (patternEdgeCount [[1,1,1,1,2,1,2]]) [] := certificate_3035_checked

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

theorem patterns_17_8_50_verified_oai : ∀ D ∈ patterns_17_8_50, PatternVerified 17 8 D := by

  simp only [patterns_17_8_50, List.forall_mem_cons]

  exact ⟨⟨certificate_3020, certificate_3020_valid⟩, ⟨⟨certificate_3021, certificate_3021_valid⟩, ⟨⟨certificate_3022, certificate_3022_valid⟩, ⟨⟨certificate_3023, certificate_3023_valid⟩, ⟨⟨certificate_3024, certificate_3024_valid⟩, ⟨⟨certificate_3025, certificate_3025_valid⟩, ⟨⟨certificate_3026, certificate_3026_valid⟩, ⟨⟨certificate_3027, certificate_3027_valid⟩, ⟨⟨certificate_3028, certificate_3028_valid⟩, ⟨⟨certificate_3029, certificate_3029_valid⟩, ⟨⟨certificate_3030, certificate_3030_valid⟩, ⟨⟨certificate_3031, certificate_3031_valid⟩, ⟨⟨certificate_3032, certificate_3032_valid⟩, ⟨⟨certificate_3033, certificate_3033_valid⟩, ⟨⟨certificate_3034, certificate_3034_valid⟩, ⟨⟨certificate_3035, certificate_3035_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_50_verified_oai := @OAI.CycleClique.patterns_17_8_50_verified_oai
