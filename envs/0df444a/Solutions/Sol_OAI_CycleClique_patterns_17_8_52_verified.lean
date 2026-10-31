-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_52_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:05:17.657865+00:00
-- url     : https://prove2.me/submissions/1f7d6e43-5a23-4964-9a3d-8125eaa263e4

import Mathlib
import Definitions.Def_OAIQ107D132
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates096
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_3052_checked : certificate_3052.Valid 17 8 16 certificate_3052_q certificate_3052_edges 8 6 [] := by decide +kernel
theorem certificate_3052_valid : certificate_3052.Valid 17 8 (patternOrder [[1,1,2],[1,1,2]]) (patternClique [[1,1,2],[1,1,2]]) (patternEdges [[1,1,2],[1,1,2]]) (patternAmount [[1,1,2],[1,1,2]]) (patternEdgeCount [[1,1,2],[1,1,2]]) [] := certificate_3052_checked

theorem certificate_3053_checked : certificate_3053.Valid 17 8 17 certificate_3053_q certificate_3053_edges 9 6 [] := by decide +kernel
theorem certificate_3053_valid : certificate_3053.Valid 17 8 (patternOrder [[1,1,2],[1,1,3]]) (patternClique [[1,1,2],[1,1,3]]) (patternEdges [[1,1,2],[1,1,3]]) (patternAmount [[1,1,2],[1,1,3]]) (patternEdgeCount [[1,1,2],[1,1,3]]) [] := certificate_3053_checked

theorem certificate_3054_checked : certificate_3054.Valid 17 8 16 certificate_3054_q certificate_3054_edges 8 6 [] := by decide +kernel
theorem certificate_3054_valid : certificate_3054.Valid 17 8 (patternOrder [[1,1,2],[1,2,1]]) (patternClique [[1,1,2],[1,2,1]]) (patternEdges [[1,1,2],[1,2,1]]) (patternAmount [[1,1,2],[1,2,1]]) (patternEdgeCount [[1,1,2],[1,2,1]]) [] := certificate_3054_checked

theorem certificate_3055_checked : certificate_3055.Valid 17 8 17 certificate_3055_q certificate_3055_edges 9 6 [] := by decide +kernel
theorem certificate_3055_valid : certificate_3055.Valid 17 8 (patternOrder [[1,1,2],[1,2,2]]) (patternClique [[1,1,2],[1,2,2]]) (patternEdges [[1,1,2],[1,2,2]]) (patternAmount [[1,1,2],[1,2,2]]) (patternEdgeCount [[1,1,2],[1,2,2]]) [] := certificate_3055_checked

theorem certificate_3056_checked : certificate_3056.Valid 17 8 17 certificate_3056_q certificate_3056_edges 9 6 [] := by decide +kernel
theorem certificate_3056_valid : certificate_3056.Valid 17 8 (patternOrder [[1,1,2],[1,3,1]]) (patternClique [[1,1,2],[1,3,1]]) (patternEdges [[1,1,2],[1,3,1]]) (patternAmount [[1,1,2],[1,3,1]]) (patternEdgeCount [[1,1,2],[1,3,1]]) [] := certificate_3056_checked

theorem certificate_3057_checked : certificate_3057.Valid 17 8 16 certificate_3057_q certificate_3057_edges 8 5 [] := by decide +kernel
theorem certificate_3057_valid : certificate_3057.Valid 17 8 (patternOrder [[1,1,2],[2],[2]]) (patternClique [[1,1,2],[2],[2]]) (patternEdges [[1,1,2],[2],[2]]) (patternAmount [[1,1,2],[2],[2]]) (patternEdgeCount [[1,1,2],[2],[2]]) [] := certificate_3057_checked

theorem certificate_3058_checked : certificate_3058.Valid 17 8 17 certificate_3058_q certificate_3058_edges 9 5 [] := by decide +kernel
theorem certificate_3058_valid : certificate_3058.Valid 17 8 (patternOrder [[1,1,2],[2],[3]]) (patternClique [[1,1,2],[2],[3]]) (patternEdges [[1,1,2],[2],[3]]) (patternAmount [[1,1,2],[2],[3]]) (patternEdgeCount [[1,1,2],[2],[3]]) [] := certificate_3058_checked

theorem certificate_3059_checked : certificate_3059.Valid 17 8 17 certificate_3059_q certificate_3059_edges 9 6 [] := by decide +kernel
theorem certificate_3059_valid : certificate_3059.Valid 17 8 (patternOrder [[1,1,2],[2,1,2]]) (patternClique [[1,1,2],[2,1,2]]) (patternEdges [[1,1,2],[2,1,2]]) (patternAmount [[1,1,2],[2,1,2]]) (patternEdgeCount [[1,1,2],[2,1,2]]) [] := certificate_3059_checked

theorem certificate_3060_checked : certificate_3060.Valid 17 8 16 certificate_3060_q certificate_3060_edges 8 6 [] := by decide +kernel
theorem certificate_3060_valid : certificate_3060.Valid 17 8 (patternOrder [[1,1,2,1],[1,2]]) (patternClique [[1,1,2,1],[1,2]]) (patternEdges [[1,1,2,1],[1,2]]) (patternAmount [[1,1,2,1],[1,2]]) (patternEdgeCount [[1,1,2,1],[1,2]]) [] := certificate_3060_checked

theorem certificate_3061_checked : certificate_3061.Valid 17 8 17 certificate_3061_q certificate_3061_edges 9 6 [] := by decide +kernel
theorem certificate_3061_valid : certificate_3061.Valid 17 8 (patternOrder [[1,1,2,1],[1,3]]) (patternClique [[1,1,2,1],[1,3]]) (patternEdges [[1,1,2,1],[1,3]]) (patternAmount [[1,1,2,1],[1,3]]) (patternEdgeCount [[1,1,2,1],[1,3]]) [] := certificate_3061_checked

theorem certificate_3062_checked : certificate_3062.Valid 17 8 17 certificate_3062_q certificate_3062_edges 9 6 [] := by decide +kernel
theorem certificate_3062_valid : certificate_3062.Valid 17 8 (patternOrder [[1,1,2,1],[2,2]]) (patternClique [[1,1,2,1],[2,2]]) (patternEdges [[1,1,2,1],[2,2]]) (patternAmount [[1,1,2,1],[2,2]]) (patternEdgeCount [[1,1,2,1],[2,2]]) [] := certificate_3062_checked

theorem certificate_3063_checked : certificate_3063.Valid 17 8 16 certificate_3063_q certificate_3063_edges 8 6 [] := by decide +kernel
theorem certificate_3063_valid : certificate_3063.Valid 17 8 (patternOrder [[1,1,2,1,1],[2]]) (patternClique [[1,1,2,1,1],[2]]) (patternEdges [[1,1,2,1,1],[2]]) (patternAmount [[1,1,2,1,1],[2]]) (patternEdgeCount [[1,1,2,1,1],[2]]) [] := certificate_3063_checked

theorem certificate_3064_checked : certificate_3064.Valid 17 8 17 certificate_3064_q certificate_3064_edges 9 6 [] := by decide +kernel
theorem certificate_3064_valid : certificate_3064.Valid 17 8 (patternOrder [[1,1,2,1,1],[3]]) (patternClique [[1,1,2,1,1],[3]]) (patternEdges [[1,1,2,1,1],[3]]) (patternAmount [[1,1,2,1,1],[3]]) (patternEdgeCount [[1,1,2,1,1],[3]]) [] := certificate_3064_checked

theorem certificate_3065_checked : certificate_3065.Valid 17 8 17 certificate_3065_q certificate_3065_edges 9 7 [] := by decide +kernel
theorem certificate_3065_valid : certificate_3065.Valid 17 8 (patternOrder [[1,1,2,1,1,1,2]]) (patternClique [[1,1,2,1,1,1,2]]) (patternEdges [[1,1,2,1,1,1,2]]) (patternAmount [[1,1,2,1,1,1,2]]) (patternEdgeCount [[1,1,2,1,1,1,2]]) [] := certificate_3065_checked

theorem certificate_3066_checked : certificate_3066.Valid 17 8 17 certificate_3066_q certificate_3066_edges 9 7 [] := by decide +kernel
theorem certificate_3066_valid : certificate_3066.Valid 17 8 (patternOrder [[1,1,2,1,1,2,1]]) (patternClique [[1,1,2,1,1,2,1]]) (patternEdges [[1,1,2,1,1,2,1]]) (patternAmount [[1,1,2,1,1,2,1]]) (patternEdgeCount [[1,1,2,1,1,2,1]]) [] := certificate_3066_checked

theorem certificate_3067_checked : certificate_3067.Valid 17 8 17 certificate_3067_q certificate_3067_edges 9 6 [] := by decide +kernel
theorem certificate_3067_valid : certificate_3067.Valid 17 8 (patternOrder [[1,1,2,1,2],[2]]) (patternClique [[1,1,2,1,2],[2]]) (patternEdges [[1,1,2,1,2],[2]]) (patternAmount [[1,1,2,1,2],[2]]) (patternEdgeCount [[1,1,2,1,2],[2]]) [] := certificate_3067_checked

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

theorem patterns_17_8_52_verified_oai : ∀ D ∈ patterns_17_8_52, PatternVerified 17 8 D := by

  simp only [patterns_17_8_52, List.forall_mem_cons]

  exact ⟨⟨certificate_3052, certificate_3052_valid⟩, ⟨⟨certificate_3053, certificate_3053_valid⟩, ⟨⟨certificate_3054, certificate_3054_valid⟩, ⟨⟨certificate_3055, certificate_3055_valid⟩, ⟨⟨certificate_3056, certificate_3056_valid⟩, ⟨⟨certificate_3057, certificate_3057_valid⟩, ⟨⟨certificate_3058, certificate_3058_valid⟩, ⟨⟨certificate_3059, certificate_3059_valid⟩, ⟨⟨certificate_3060, certificate_3060_valid⟩, ⟨⟨certificate_3061, certificate_3061_valid⟩, ⟨⟨certificate_3062, certificate_3062_valid⟩, ⟨⟨certificate_3063, certificate_3063_valid⟩, ⟨⟨certificate_3064, certificate_3064_valid⟩, ⟨⟨certificate_3065, certificate_3065_valid⟩, ⟨⟨certificate_3066, certificate_3066_valid⟩, ⟨⟨certificate_3067, certificate_3067_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_52_verified_oai := @OAI.CycleClique.patterns_17_8_52_verified_oai
