-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_19_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:42:38.921777+00:00
-- url     : https://prove2.me/submissions/ea5372b0-488e-4fc2-b911-d1471749e575

import Mathlib
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates065
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2056_checked : certificate_2056.Valid 16 8 15 certificate_2056_q certificate_2056_edges 7 5 [] := by decide +kernel
theorem certificate_2056_valid : certificate_2056.Valid 16 8 (patternOrder [[],[1,1],[1,2,2]]) (patternClique [[],[1,1],[1,2,2]]) (patternEdges [[],[1,1],[1,2,2]]) (patternAmount [[],[1,1],[1,2,2]]) (patternEdgeCount [[],[1,1],[1,2,2]]) [] := certificate_2056_checked

theorem certificate_2057_checked : certificate_2057.Valid 16 8 16 certificate_2057_q certificate_2057_edges 8 5 [] := by decide +kernel
theorem certificate_2057_valid : certificate_2057.Valid 16 8 (patternOrder [[],[1,1],[1,2,3]]) (patternClique [[],[1,1],[1,2,3]]) (patternEdges [[],[1,1],[1,2,3]]) (patternAmount [[],[1,1],[1,2,3]]) (patternEdgeCount [[],[1,1],[1,2,3]]) [] := certificate_2057_checked

theorem certificate_2058_checked : certificate_2058.Valid 16 8 15 certificate_2058_q certificate_2058_edges 7 5 [] := by decide +kernel
theorem certificate_2058_valid : certificate_2058.Valid 16 8 (patternOrder [[],[1,1],[1,3,1]]) (patternClique [[],[1,1],[1,3,1]]) (patternEdges [[],[1,1],[1,3,1]]) (patternAmount [[],[1,1],[1,3,1]]) (patternEdgeCount [[],[1,1],[1,3,1]]) [] := certificate_2058_checked

theorem certificate_2059_checked : certificate_2059.Valid 16 8 16 certificate_2059_q certificate_2059_edges 8 5 [] := by decide +kernel
theorem certificate_2059_valid : certificate_2059.Valid 16 8 (patternOrder [[],[1,1],[1,3,2]]) (patternClique [[],[1,1],[1,3,2]]) (patternEdges [[],[1,1],[1,3,2]]) (patternAmount [[],[1,1],[1,3,2]]) (patternEdgeCount [[],[1,1],[1,3,2]]) [] := certificate_2059_checked

theorem certificate_2060_checked : certificate_2060.Valid 16 8 16 certificate_2060_q certificate_2060_edges 8 5 [] := by decide +kernel
theorem certificate_2060_valid : certificate_2060.Valid 16 8 (patternOrder [[],[1,1],[1,4,1]]) (patternClique [[],[1,1],[1,4,1]]) (patternEdges [[],[1,1],[1,4,1]]) (patternAmount [[],[1,1],[1,4,1]]) (patternEdgeCount [[],[1,1],[1,4,1]]) [] := certificate_2060_checked

theorem certificate_2061_checked : certificate_2061.Valid 16 8 14 certificate_2061_q certificate_2061_edges 6 4 [] := by decide +kernel
theorem certificate_2061_valid : certificate_2061.Valid 16 8 (patternOrder [[],[1,1],[2],[2]]) (patternClique [[],[1,1],[2],[2]]) (patternEdges [[],[1,1],[2],[2]]) (patternAmount [[],[1,1],[2],[2]]) (patternEdgeCount [[],[1,1],[2],[2]]) [] := certificate_2061_checked

theorem certificate_2062_checked : certificate_2062.Valid 16 8 15 certificate_2062_q certificate_2062_edges 7 4 [] := by decide +kernel
theorem certificate_2062_valid : certificate_2062.Valid 16 8 (patternOrder [[],[1,1],[2],[3]]) (patternClique [[],[1,1],[2],[3]]) (patternEdges [[],[1,1],[2],[3]]) (patternAmount [[],[1,1],[2],[3]]) (patternEdgeCount [[],[1,1],[2],[3]]) [] := certificate_2062_checked

theorem certificate_2063_checked : certificate_2063.Valid 16 8 16 certificate_2063_q certificate_2063_edges 8 4 [] := by decide +kernel
theorem certificate_2063_valid : certificate_2063.Valid 16 8 (patternOrder [[],[1,1],[2],[4]]) (patternClique [[],[1,1],[2],[4]]) (patternEdges [[],[1,1],[2],[4]]) (patternAmount [[],[1,1],[2],[4]]) (patternEdgeCount [[],[1,1],[2],[4]]) [] := certificate_2063_checked

theorem certificate_2064_checked : certificate_2064.Valid 16 8 15 certificate_2064_q certificate_2064_edges 7 5 [] := by decide +kernel
theorem certificate_2064_valid : certificate_2064.Valid 16 8 (patternOrder [[],[1,1],[2,1,2]]) (patternClique [[],[1,1],[2,1,2]]) (patternEdges [[],[1,1],[2,1,2]]) (patternAmount [[],[1,1],[2,1,2]]) (patternEdgeCount [[],[1,1],[2,1,2]]) [] := certificate_2064_checked

theorem certificate_2065_checked : certificate_2065.Valid 16 8 16 certificate_2065_q certificate_2065_edges 8 5 [] := by decide +kernel
theorem certificate_2065_valid : certificate_2065.Valid 16 8 (patternOrder [[],[1,1],[2,1,3]]) (patternClique [[],[1,1],[2,1,3]]) (patternEdges [[],[1,1],[2,1,3]]) (patternAmount [[],[1,1],[2,1,3]]) (patternEdgeCount [[],[1,1],[2,1,3]]) [] := certificate_2065_checked

theorem certificate_2066_checked : certificate_2066.Valid 16 8 16 certificate_2066_q certificate_2066_edges 8 5 [] := by decide +kernel
theorem certificate_2066_valid : certificate_2066.Valid 16 8 (patternOrder [[],[1,1],[2,2,2]]) (patternClique [[],[1,1],[2,2,2]]) (patternEdges [[],[1,1],[2,2,2]]) (patternAmount [[],[1,1],[2,2,2]]) (patternEdgeCount [[],[1,1],[2,2,2]]) [] := certificate_2066_checked

theorem certificate_2067_checked : certificate_2067.Valid 16 8 16 certificate_2067_q certificate_2067_edges 8 4 [] := by decide +kernel
theorem certificate_2067_valid : certificate_2067.Valid 16 8 (patternOrder [[],[1,1],[3],[3]]) (patternClique [[],[1,1],[3],[3]]) (patternEdges [[],[1,1],[3],[3]]) (patternAmount [[],[1,1],[3],[3]]) (patternEdgeCount [[],[1,1],[3],[3]]) [] := certificate_2067_checked

theorem certificate_2068_checked : certificate_2068.Valid 16 8 14 certificate_2068_q certificate_2068_edges 6 5 [] := by decide +kernel
theorem certificate_2068_valid : certificate_2068.Valid 16 8 (patternOrder [[],[1,1,1],[1,2]]) (patternClique [[],[1,1,1],[1,2]]) (patternEdges [[],[1,1,1],[1,2]]) (patternAmount [[],[1,1,1],[1,2]]) (patternEdgeCount [[],[1,1,1],[1,2]]) [] := certificate_2068_checked

theorem certificate_2069_checked : certificate_2069.Valid 16 8 15 certificate_2069_q certificate_2069_edges 7 5 [] := by decide +kernel
theorem certificate_2069_valid : certificate_2069.Valid 16 8 (patternOrder [[],[1,1,1],[1,3]]) (patternClique [[],[1,1,1],[1,3]]) (patternEdges [[],[1,1,1],[1,3]]) (patternAmount [[],[1,1,1],[1,3]]) (patternEdgeCount [[],[1,1,1],[1,3]]) [] := certificate_2069_checked

theorem certificate_2070_checked : certificate_2070.Valid 16 8 16 certificate_2070_q certificate_2070_edges 8 5 [] := by decide +kernel
theorem certificate_2070_valid : certificate_2070.Valid 16 8 (patternOrder [[],[1,1,1],[1,4]]) (patternClique [[],[1,1,1],[1,4]]) (patternEdges [[],[1,1,1],[1,4]]) (patternAmount [[],[1,1,1],[1,4]]) (patternEdgeCount [[],[1,1,1],[1,4]]) [] := certificate_2070_checked

theorem certificate_2071_checked : certificate_2071.Valid 16 8 15 certificate_2071_q certificate_2071_edges 7 5 [] := by decide +kernel
theorem certificate_2071_valid : certificate_2071.Valid 16 8 (patternOrder [[],[1,1,1],[2,2]]) (patternClique [[],[1,1,1],[2,2]]) (patternEdges [[],[1,1,1],[2,2]]) (patternAmount [[],[1,1,1],[2,2]]) (patternEdgeCount [[],[1,1,1],[2,2]]) [] := certificate_2071_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns16x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_16_8_19_verified_oai : ∀ D ∈ patterns_16_8_19, PatternVerified 16 8 D := by

  simp only [patterns_16_8_19, List.forall_mem_cons]

  exact ⟨⟨certificate_2056, certificate_2056_valid⟩, ⟨⟨certificate_2057, certificate_2057_valid⟩, ⟨⟨certificate_2058, certificate_2058_valid⟩, ⟨⟨certificate_2059, certificate_2059_valid⟩, ⟨⟨certificate_2060, certificate_2060_valid⟩, ⟨⟨certificate_2061, certificate_2061_valid⟩, ⟨⟨certificate_2062, certificate_2062_valid⟩, ⟨⟨certificate_2063, certificate_2063_valid⟩, ⟨⟨certificate_2064, certificate_2064_valid⟩, ⟨⟨certificate_2065, certificate_2065_valid⟩, ⟨⟨certificate_2066, certificate_2066_valid⟩, ⟨⟨certificate_2067, certificate_2067_valid⟩, ⟨⟨certificate_2068, certificate_2068_valid⟩, ⟨⟨certificate_2069, certificate_2069_valid⟩, ⟨⟨certificate_2070, certificate_2070_valid⟩, ⟨⟨certificate_2071, certificate_2071_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_19_verified_oai := @OAI.CycleClique.patterns_16_8_19_verified_oai
