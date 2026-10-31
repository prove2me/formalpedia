-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_51_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:58:00.740842+00:00
-- url     : https://prove2.me/submissions/e8903a61-d3ea-479d-b29b-30410f6d14a2

import Mathlib
import Definitions.Def_OAIQ107D132
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

theorem certificate_3036_checked : certificate_3036.Valid 17 8 17 certificate_3036_q certificate_3036_edges 9 7 [] := by decide +kernel
theorem certificate_3036_valid : certificate_3036.Valid 17 8 (patternOrder [[1,1,1,1,2,2,1]]) (patternClique [[1,1,1,1,2,2,1]]) (patternEdges [[1,1,1,1,2,2,1]]) (patternAmount [[1,1,1,1,2,2,1]]) (patternEdgeCount [[1,1,1,1,2,2,1]]) [] := certificate_3036_checked

theorem certificate_3037_checked : certificate_3037.Valid 17 8 17 certificate_3037_q certificate_3037_edges 9 6 [] := by decide +kernel
theorem certificate_3037_valid : certificate_3037.Valid 17 8 (patternOrder [[1,1,1,1,3],[2]]) (patternClique [[1,1,1,1,3],[2]]) (patternEdges [[1,1,1,1,3],[2]]) (patternAmount [[1,1,1,1,3],[2]]) (patternEdgeCount [[1,1,1,1,3],[2]]) [] := certificate_3037_checked

theorem certificate_3038_checked : certificate_3038.Valid 17 8 17 certificate_3038_q certificate_3038_edges 9 7 [] := by decide +kernel
theorem certificate_3038_valid : certificate_3038.Valid 17 8 (patternOrder [[1,1,1,1,3,1,1]]) (patternClique [[1,1,1,1,3,1,1]]) (patternEdges [[1,1,1,1,3,1,1]]) (patternAmount [[1,1,1,1,3,1,1]]) (patternEdgeCount [[1,1,1,1,3,1,1]]) [] := certificate_3038_checked

theorem certificate_3039_checked : certificate_3039.Valid 17 8 16 certificate_3039_q certificate_3039_edges 8 6 [] := by decide +kernel
theorem certificate_3039_valid : certificate_3039.Valid 17 8 (patternOrder [[1,1,1,2],[1,2]]) (patternClique [[1,1,1,2],[1,2]]) (patternEdges [[1,1,1,2],[1,2]]) (patternAmount [[1,1,1,2],[1,2]]) (patternEdgeCount [[1,1,1,2],[1,2]]) [] := certificate_3039_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates096
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_3040_checked : certificate_3040.Valid 17 8 17 certificate_3040_q certificate_3040_edges 9 6 [] := by decide +kernel
theorem certificate_3040_valid : certificate_3040.Valid 17 8 (patternOrder [[1,1,1,2],[1,3]]) (patternClique [[1,1,1,2],[1,3]]) (patternEdges [[1,1,1,2],[1,3]]) (patternAmount [[1,1,1,2],[1,3]]) (patternEdgeCount [[1,1,1,2],[1,3]]) [] := certificate_3040_checked

theorem certificate_3041_checked : certificate_3041.Valid 17 8 17 certificate_3041_q certificate_3041_edges 9 6 [] := by decide +kernel
theorem certificate_3041_valid : certificate_3041.Valid 17 8 (patternOrder [[1,1,1,2],[2,2]]) (patternClique [[1,1,1,2],[2,2]]) (patternEdges [[1,1,1,2],[2,2]]) (patternAmount [[1,1,1,2],[2,2]]) (patternEdgeCount [[1,1,1,2],[2,2]]) [] := certificate_3041_checked

theorem certificate_3042_checked : certificate_3042.Valid 17 8 16 certificate_3042_q certificate_3042_edges 8 6 [] := by decide +kernel
theorem certificate_3042_valid : certificate_3042.Valid 17 8 (patternOrder [[1,1,1,2,1],[2]]) (patternClique [[1,1,1,2,1],[2]]) (patternEdges [[1,1,1,2,1],[2]]) (patternAmount [[1,1,1,2,1],[2]]) (patternEdgeCount [[1,1,1,2,1],[2]]) [] := certificate_3042_checked

theorem certificate_3043_checked : certificate_3043.Valid 17 8 17 certificate_3043_q certificate_3043_edges 9 6 [] := by decide +kernel
theorem certificate_3043_valid : certificate_3043.Valid 17 8 (patternOrder [[1,1,1,2,1],[3]]) (patternClique [[1,1,1,2,1],[3]]) (patternEdges [[1,1,1,2,1],[3]]) (patternAmount [[1,1,1,2,1],[3]]) (patternEdgeCount [[1,1,1,2,1],[3]]) [] := certificate_3043_checked

theorem certificate_3044_checked : certificate_3044.Valid 17 8 16 certificate_3044_q certificate_3044_edges 8 7 [] := by decide +kernel
theorem certificate_3044_valid : certificate_3044.Valid 17 8 (patternOrder [[1,1,1,2,1,1,1]]) (patternClique [[1,1,1,2,1,1,1]]) (patternEdges [[1,1,1,2,1,1,1]]) (patternAmount [[1,1,1,2,1,1,1]]) (patternEdgeCount [[1,1,1,2,1,1,1]]) [] := certificate_3044_checked

theorem certificate_3045_checked : certificate_3045.Valid 17 8 17 certificate_3045_q certificate_3045_edges 9 7 [] := by decide +kernel
theorem certificate_3045_valid : certificate_3045.Valid 17 8 (patternOrder [[1,1,1,2,1,1,2]]) (patternClique [[1,1,1,2,1,1,2]]) (patternEdges [[1,1,1,2,1,1,2]]) (patternAmount [[1,1,1,2,1,1,2]]) (patternEdgeCount [[1,1,1,2,1,1,2]]) [] := certificate_3045_checked

theorem certificate_3046_checked : certificate_3046.Valid 17 8 17 certificate_3046_q certificate_3046_edges 9 7 [] := by decide +kernel
theorem certificate_3046_valid : certificate_3046.Valid 17 8 (patternOrder [[1,1,1,2,1,2,1]]) (patternClique [[1,1,1,2,1,2,1]]) (patternEdges [[1,1,1,2,1,2,1]]) (patternAmount [[1,1,1,2,1,2,1]]) (patternEdgeCount [[1,1,1,2,1,2,1]]) [] := certificate_3046_checked

theorem certificate_3047_checked : certificate_3047.Valid 17 8 17 certificate_3047_q certificate_3047_edges 9 6 [] := by decide +kernel
theorem certificate_3047_valid : certificate_3047.Valid 17 8 (patternOrder [[1,1,1,2,2],[2]]) (patternClique [[1,1,1,2,2],[2]]) (patternEdges [[1,1,1,2,2],[2]]) (patternAmount [[1,1,1,2,2],[2]]) (patternEdgeCount [[1,1,1,2,2],[2]]) [] := certificate_3047_checked

theorem certificate_3048_checked : certificate_3048.Valid 17 8 17 certificate_3048_q certificate_3048_edges 9 7 [] := by decide +kernel
theorem certificate_3048_valid : certificate_3048.Valid 17 8 (patternOrder [[1,1,1,2,2,1,1]]) (patternClique [[1,1,1,2,2,1,1]]) (patternEdges [[1,1,1,2,2,1,1]]) (patternAmount [[1,1,1,2,2,1,1]]) (patternEdgeCount [[1,1,1,2,2,1,1]]) [] := certificate_3048_checked

theorem certificate_3049_checked : certificate_3049.Valid 17 8 17 certificate_3049_q certificate_3049_edges 9 6 [] := by decide +kernel
theorem certificate_3049_valid : certificate_3049.Valid 17 8 (patternOrder [[1,1,1,3],[1,2]]) (patternClique [[1,1,1,3],[1,2]]) (patternEdges [[1,1,1,3],[1,2]]) (patternAmount [[1,1,1,3],[1,2]]) (patternEdgeCount [[1,1,1,3],[1,2]]) [] := certificate_3049_checked

theorem certificate_3050_checked : certificate_3050.Valid 17 8 17 certificate_3050_q certificate_3050_edges 9 6 [] := by decide +kernel
theorem certificate_3050_valid : certificate_3050.Valid 17 8 (patternOrder [[1,1,1,3,1],[2]]) (patternClique [[1,1,1,3,1],[2]]) (patternEdges [[1,1,1,3,1],[2]]) (patternAmount [[1,1,1,3,1],[2]]) (patternEdgeCount [[1,1,1,3,1],[2]]) [] := certificate_3050_checked

theorem certificate_3051_checked : certificate_3051.Valid 17 8 17 certificate_3051_q certificate_3051_edges 9 7 [] := by decide +kernel
theorem certificate_3051_valid : certificate_3051.Valid 17 8 (patternOrder [[1,1,1,3,1,1,1]]) (patternClique [[1,1,1,3,1,1,1]]) (patternEdges [[1,1,1,3,1,1,1]]) (patternAmount [[1,1,1,3,1,1,1]]) (patternEdgeCount [[1,1,1,3,1,1,1]]) [] := certificate_3051_checked

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

theorem patterns_17_8_51_verified_oai : ∀ D ∈ patterns_17_8_51, PatternVerified 17 8 D := by

  simp only [patterns_17_8_51, List.forall_mem_cons]

  exact ⟨⟨certificate_3036, certificate_3036_valid⟩, ⟨⟨certificate_3037, certificate_3037_valid⟩, ⟨⟨certificate_3038, certificate_3038_valid⟩, ⟨⟨certificate_3039, certificate_3039_valid⟩, ⟨⟨certificate_3040, certificate_3040_valid⟩, ⟨⟨certificate_3041, certificate_3041_valid⟩, ⟨⟨certificate_3042, certificate_3042_valid⟩, ⟨⟨certificate_3043, certificate_3043_valid⟩, ⟨⟨certificate_3044, certificate_3044_valid⟩, ⟨⟨certificate_3045, certificate_3045_valid⟩, ⟨⟨certificate_3046, certificate_3046_valid⟩, ⟨⟨certificate_3047, certificate_3047_valid⟩, ⟨⟨certificate_3048, certificate_3048_valid⟩, ⟨⟨certificate_3049, certificate_3049_valid⟩, ⟨⟨certificate_3050, certificate_3050_valid⟩, ⟨⟨certificate_3051, certificate_3051_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_51_verified_oai := @OAI.CycleClique.patterns_17_8_51_verified_oai
