-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_22_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:45:36.078773+00:00
-- url     : https://prove2.me/submissions/9e9c929d-c9ac-484e-8c05-15456e160048

import Mathlib
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates066
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2104_checked : certificate_2104.Valid 16 8 16 certificate_2104_q certificate_2104_edges 8 4 [] := by decide +kernel
theorem certificate_2104_valid : certificate_2104.Valid 16 8 (patternOrder [[],[1,2],[2],[3]]) (patternClique [[],[1,2],[2],[3]]) (patternEdges [[],[1,2],[2],[3]]) (patternAmount [[],[1,2],[2],[3]]) (patternEdgeCount [[],[1,2],[2],[3]]) [] := certificate_2104_checked

theorem certificate_2105_checked : certificate_2105.Valid 16 8 16 certificate_2105_q certificate_2105_edges 8 5 [] := by decide +kernel
theorem certificate_2105_valid : certificate_2105.Valid 16 8 (patternOrder [[],[1,2],[2,1,2]]) (patternClique [[],[1,2],[2,1,2]]) (patternEdges [[],[1,2],[2,1,2]]) (patternAmount [[],[1,2],[2,1,2]]) (patternEdgeCount [[],[1,2],[2,1,2]]) [] := certificate_2105_checked

theorem certificate_2106_checked : certificate_2106.Valid 16 8 16 certificate_2106_q certificate_2106_edges 8 5 [] := by decide +kernel
theorem certificate_2106_valid : certificate_2106.Valid 16 8 (patternOrder [[],[1,2,1],[1,3]]) (patternClique [[],[1,2,1],[1,3]]) (patternEdges [[],[1,2,1],[1,3]]) (patternAmount [[],[1,2,1],[1,3]]) (patternEdgeCount [[],[1,2,1],[1,3]]) [] := certificate_2106_checked

theorem certificate_2107_checked : certificate_2107.Valid 16 8 16 certificate_2107_q certificate_2107_edges 8 5 [] := by decide +kernel
theorem certificate_2107_valid : certificate_2107.Valid 16 8 (patternOrder [[],[1,2,1],[2,2]]) (patternClique [[],[1,2,1],[2,2]]) (patternEdges [[],[1,2,1],[2,2]]) (patternAmount [[],[1,2,1],[2,2]]) (patternEdgeCount [[],[1,2,1],[2,2]]) [] := certificate_2107_checked

theorem certificate_2108_checked : certificate_2108.Valid 16 8 16 certificate_2108_q certificate_2108_edges 8 6 [] := by decide +kernel
theorem certificate_2108_valid : certificate_2108.Valid 16 8 (patternOrder [[],[1,2,1,1,1,2]]) (patternClique [[],[1,2,1,1,1,2]]) (patternEdges [[],[1,2,1,1,1,2]]) (patternAmount [[],[1,2,1,1,1,2]]) (patternEdgeCount [[],[1,2,1,1,1,2]]) [] := certificate_2108_checked

theorem certificate_2109_checked : certificate_2109.Valid 16 8 16 certificate_2109_q certificate_2109_edges 8 6 [] := by decide +kernel
theorem certificate_2109_valid : certificate_2109.Valid 16 8 (patternOrder [[],[1,2,1,1,2,1]]) (patternClique [[],[1,2,1,1,2,1]]) (patternEdges [[],[1,2,1,1,2,1]]) (patternAmount [[],[1,2,1,1,2,1]]) (patternEdgeCount [[],[1,2,1,1,2,1]]) [] := certificate_2109_checked

theorem certificate_2110_checked : certificate_2110.Valid 16 8 16 certificate_2110_q certificate_2110_edges 8 5 [] := by decide +kernel
theorem certificate_2110_valid : certificate_2110.Valid 16 8 (patternOrder [[],[1,2,1,2],[2]]) (patternClique [[],[1,2,1,2],[2]]) (patternEdges [[],[1,2,1,2],[2]]) (patternAmount [[],[1,2,1,2],[2]]) (patternEdgeCount [[],[1,2,1,2],[2]]) [] := certificate_2110_checked

theorem certificate_2111_checked : certificate_2111.Valid 16 8 16 certificate_2111_q certificate_2111_edges 8 5 [] := by decide +kernel
theorem certificate_2111_valid : certificate_2111.Valid 16 8 (patternOrder [[],[1,2,2,1],[2]]) (patternClique [[],[1,2,2,1],[2]]) (patternEdges [[],[1,2,2,1],[2]]) (patternAmount [[],[1,2,2,1],[2]]) (patternEdgeCount [[],[1,2,2,1],[2]]) [] := certificate_2111_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates067
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2112_checked : certificate_2112.Valid 16 8 16 certificate_2112_q certificate_2112_edges 8 4 [] := by decide +kernel
theorem certificate_2112_valid : certificate_2112.Valid 16 8 (patternOrder [[],[1,3],[2],[2]]) (patternClique [[],[1,3],[2],[2]]) (patternEdges [[],[1,3],[2],[2]]) (patternAmount [[],[1,3],[2],[2]]) (patternEdgeCount [[],[1,3],[2],[2]]) [] := certificate_2112_checked

theorem certificate_2113_checked : certificate_2113.Valid 16 8 16 certificate_2113_q certificate_2113_edges 8 4 [] := by decide +kernel
theorem certificate_2113_valid : certificate_2113.Valid 16 8 (patternOrder [[],[2],[2],[2,2]]) (patternClique [[],[2],[2],[2,2]]) (patternEdges [[],[2],[2],[2,2]]) (patternAmount [[],[2],[2],[2,2]]) (patternEdgeCount [[],[2],[2],[2,2]]) [] := certificate_2113_checked

theorem certificate_2114_checked : certificate_2114.Valid 16 8 16 certificate_2114_q certificate_2114_edges 8 5 [] := by decide +kernel
theorem certificate_2114_valid : certificate_2114.Valid 16 8 (patternOrder [[],[2],[2,1,1,2]]) (patternClique [[],[2],[2,1,1,2]]) (patternEdges [[],[2],[2,1,1,2]]) (patternAmount [[],[2],[2,1,1,2]]) (patternEdgeCount [[],[2],[2,1,1,2]]) [] := certificate_2114_checked

theorem certificate_2115_checked : certificate_2115.Valid 16 8 16 certificate_2115_q certificate_2115_edges 8 6 [] := by decide +kernel
theorem certificate_2115_valid : certificate_2115.Valid 16 8 (patternOrder [[],[2,1,1,1,1,2]]) (patternClique [[],[2,1,1,1,1,2]]) (patternEdges [[],[2,1,1,1,1,2]]) (patternAmount [[],[2,1,1,1,1,2]]) (patternEdgeCount [[],[2,1,1,1,1,2]]) [] := certificate_2115_checked

theorem certificate_2116_checked : certificate_2116.Valid 16 8 12 certificate_2116_q certificate_2116_edges 4 4 [] := by decide +kernel
theorem certificate_2116_valid : certificate_2116.Valid 16 8 (patternOrder [[1],[1],[1],[1]]) (patternClique [[1],[1],[1],[1]]) (patternEdges [[1],[1],[1],[1]]) (patternAmount [[1],[1],[1],[1]]) (patternEdgeCount [[1],[1],[1],[1]]) [] := certificate_2116_checked

theorem certificate_2117_checked : certificate_2117.Valid 16 8 13 certificate_2117_q certificate_2117_edges 5 4 [] := by decide +kernel
theorem certificate_2117_valid : certificate_2117.Valid 16 8 (patternOrder [[1],[1],[1],[2]]) (patternClique [[1],[1],[1],[2]]) (patternEdges [[1],[1],[1],[2]]) (patternAmount [[1],[1],[1],[2]]) (patternEdgeCount [[1],[1],[1],[2]]) [] := certificate_2117_checked

theorem certificate_2118_checked : certificate_2118.Valid 16 8 14 certificate_2118_q certificate_2118_edges 6 4 [] := by decide +kernel
theorem certificate_2118_valid : certificate_2118.Valid 16 8 (patternOrder [[1],[1],[1],[3]]) (patternClique [[1],[1],[1],[3]]) (patternEdges [[1],[1],[1],[3]]) (patternAmount [[1],[1],[1],[3]]) (patternEdgeCount [[1],[1],[1],[3]]) [] := certificate_2118_checked

theorem certificate_2119_checked : certificate_2119.Valid 16 8 15 certificate_2119_q certificate_2119_edges 7 4 [] := by decide +kernel
theorem certificate_2119_valid : certificate_2119.Valid 16 8 (patternOrder [[1],[1],[1],[4]]) (patternClique [[1],[1],[1],[4]]) (patternEdges [[1],[1],[1],[4]]) (patternAmount [[1],[1],[1],[4]]) (patternEdgeCount [[1],[1],[1],[4]]) [] := certificate_2119_checked

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

theorem patterns_16_8_22_verified_oai : ∀ D ∈ patterns_16_8_22, PatternVerified 16 8 D := by

  simp only [patterns_16_8_22, List.forall_mem_cons]

  exact ⟨⟨certificate_2104, certificate_2104_valid⟩, ⟨⟨certificate_2105, certificate_2105_valid⟩, ⟨⟨certificate_2106, certificate_2106_valid⟩, ⟨⟨certificate_2107, certificate_2107_valid⟩, ⟨⟨certificate_2108, certificate_2108_valid⟩, ⟨⟨certificate_2109, certificate_2109_valid⟩, ⟨⟨certificate_2110, certificate_2110_valid⟩, ⟨⟨certificate_2111, certificate_2111_valid⟩, ⟨⟨certificate_2112, certificate_2112_valid⟩, ⟨⟨certificate_2113, certificate_2113_valid⟩, ⟨⟨certificate_2114, certificate_2114_valid⟩, ⟨⟨certificate_2115, certificate_2115_valid⟩, ⟨⟨certificate_2116, certificate_2116_valid⟩, ⟨⟨certificate_2117, certificate_2117_valid⟩, ⟨⟨certificate_2118, certificate_2118_valid⟩, ⟨⟨certificate_2119, certificate_2119_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_22_verified_oai := @OAI.CycleClique.patterns_16_8_22_verified_oai
