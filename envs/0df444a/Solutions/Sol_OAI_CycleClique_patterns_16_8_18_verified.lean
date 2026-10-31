-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_18_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:34:59.675378+00:00
-- url     : https://prove2.me/submissions/ecf9afe2-4aa7-4a2c-b4c3-29fd1c08e309

import Mathlib
import Definitions.Def_OAIQ107D003
import Definitions.Def_OAIQ107D064
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates064
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2040_checked : certificate_2040.Valid 16 8 16 certificate_2040_q certificate_2040_edges 8 5 [] := by decide +kernel
theorem certificate_2040_valid : certificate_2040.Valid 16 8 (patternOrder [[],[1],[1,2,3,1]]) (patternClique [[],[1],[1,2,3,1]]) (patternEdges [[],[1],[1,2,3,1]]) (patternAmount [[],[1],[1,2,3,1]]) (patternEdgeCount [[],[1],[1,2,3,1]]) [] := certificate_2040_checked

theorem certificate_2041_checked : certificate_2041.Valid 16 8 15 certificate_2041_q certificate_2041_edges 7 4 [] := by decide +kernel
theorem certificate_2041_valid : certificate_2041.Valid 16 8 (patternOrder [[],[1],[1,3],[2]]) (patternClique [[],[1],[1,3],[2]]) (patternEdges [[],[1],[1,3],[2]]) (patternAmount [[],[1],[1,3],[2]]) (patternEdgeCount [[],[1],[1,3],[2]]) [] := certificate_2041_checked

theorem certificate_2042_checked : certificate_2042.Valid 16 8 16 certificate_2042_q certificate_2042_edges 8 4 [] := by decide +kernel
theorem certificate_2042_valid : certificate_2042.Valid 16 8 (patternOrder [[],[1],[1,3],[3]]) (patternClique [[],[1],[1,3],[3]]) (patternEdges [[],[1],[1,3],[3]]) (patternAmount [[],[1],[1,3],[3]]) (patternEdgeCount [[],[1],[1,3],[3]]) [] := certificate_2042_checked

theorem certificate_2043_checked : certificate_2043.Valid 16 8 16 certificate_2043_q certificate_2043_edges 8 5 [] := by decide +kernel
theorem certificate_2043_valid : certificate_2043.Valid 16 8 (patternOrder [[],[1],[1,3,1,2]]) (patternClique [[],[1],[1,3,1,2]]) (patternEdges [[],[1],[1,3,1,2]]) (patternAmount [[],[1],[1,3,1,2]]) (patternEdgeCount [[],[1],[1,3,1,2]]) [] := certificate_2043_checked

theorem certificate_2044_checked : certificate_2044.Valid 16 8 16 certificate_2044_q certificate_2044_edges 8 4 [] := by decide +kernel
theorem certificate_2044_valid : certificate_2044.Valid 16 8 (patternOrder [[],[1],[1,4],[2]]) (patternClique [[],[1],[1,4],[2]]) (patternEdges [[],[1],[1,4],[2]]) (patternAmount [[],[1],[1,4],[2]]) (patternEdgeCount [[],[1],[1,4],[2]]) [] := certificate_2044_checked

theorem certificate_2045_checked : certificate_2045.Valid 16 8 15 certificate_2045_q certificate_2045_edges 7 4 [] := by decide +kernel
theorem certificate_2045_valid : certificate_2045.Valid 16 8 (patternOrder [[],[1],[2],[2,2]]) (patternClique [[],[1],[2],[2,2]]) (patternEdges [[],[1],[2],[2,2]]) (patternAmount [[],[1],[2],[2,2]]) (patternEdgeCount [[],[1],[2],[2,2]]) [] := certificate_2045_checked

theorem certificate_2046_checked : certificate_2046.Valid 16 8 16 certificate_2046_q certificate_2046_edges 8 4 [] := by decide +kernel
theorem certificate_2046_valid : certificate_2046.Valid 16 8 (patternOrder [[],[1],[2],[2,3]]) (patternClique [[],[1],[2],[2,3]]) (patternEdges [[],[1],[2],[2,3]]) (patternAmount [[],[1],[2],[2,3]]) (patternEdgeCount [[],[1],[2],[2,3]]) [] := certificate_2046_checked

theorem certificate_2047_checked : certificate_2047.Valid 16 8 15 certificate_2047_q certificate_2047_edges 7 5 [] := by decide +kernel
theorem certificate_2047_valid : certificate_2047.Valid 16 8 (patternOrder [[],[1],[2,1,1,2]]) (patternClique [[],[1],[2,1,1,2]]) (patternEdges [[],[1],[2,1,1,2]]) (patternAmount [[],[1],[2,1,1,2]]) (patternEdgeCount [[],[1],[2,1,1,2]]) [] := certificate_2047_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates065
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2048_checked : certificate_2048.Valid 16 8 16 certificate_2048_q certificate_2048_edges 8 5 [] := by decide +kernel
theorem certificate_2048_valid : certificate_2048.Valid 16 8 (patternOrder [[],[1],[2,1,1,3]]) (patternClique [[],[1],[2,1,1,3]]) (patternEdges [[],[1],[2,1,1,3]]) (patternAmount [[],[1],[2,1,1,3]]) (patternEdgeCount [[],[1],[2,1,1,3]]) [] := certificate_2048_checked

theorem certificate_2049_checked : certificate_2049.Valid 16 8 16 certificate_2049_q certificate_2049_edges 8 5 [] := by decide +kernel
theorem certificate_2049_valid : certificate_2049.Valid 16 8 (patternOrder [[],[1],[2,1,2,2]]) (patternClique [[],[1],[2,1,2,2]]) (patternEdges [[],[1],[2,1,2,2]]) (patternAmount [[],[1],[2,1,2,2]]) (patternEdgeCount [[],[1],[2,1,2,2]]) [] := certificate_2049_checked

theorem certificate_2050_checked : certificate_2050.Valid 16 8 16 certificate_2050_q certificate_2050_edges 8 4 [] := by decide +kernel
theorem certificate_2050_valid : certificate_2050.Valid 16 8 (patternOrder [[],[1],[2,2],[3]]) (patternClique [[],[1],[2,2],[3]]) (patternEdges [[],[1],[2,2],[3]]) (patternAmount [[],[1],[2,2],[3]]) (patternEdgeCount [[],[1],[2,2],[3]]) [] := certificate_2050_checked

theorem certificate_2051_checked : certificate_2051.Valid 16 8 13 certificate_2051_q certificate_2051_edges 5 5 [] := by decide +kernel
theorem certificate_2051_valid : certificate_2051.Valid 16 8 (patternOrder [[],[1,1],[1,1,1]]) (patternClique [[],[1,1],[1,1,1]]) (patternEdges [[],[1,1],[1,1,1]]) (patternAmount [[],[1,1],[1,1,1]]) (patternEdgeCount [[],[1,1],[1,1,1]]) [] := certificate_2051_checked

theorem certificate_2052_checked : certificate_2052.Valid 16 8 14 certificate_2052_q certificate_2052_edges 6 5 [] := by decide +kernel
theorem certificate_2052_valid : certificate_2052.Valid 16 8 (patternOrder [[],[1,1],[1,1,2]]) (patternClique [[],[1,1],[1,1,2]]) (patternEdges [[],[1,1],[1,1,2]]) (patternAmount [[],[1,1],[1,1,2]]) (patternEdgeCount [[],[1,1],[1,1,2]]) [] := certificate_2052_checked

theorem certificate_2053_checked : certificate_2053.Valid 16 8 15 certificate_2053_q certificate_2053_edges 7 5 [] := by decide +kernel
theorem certificate_2053_valid : certificate_2053.Valid 16 8 (patternOrder [[],[1,1],[1,1,3]]) (patternClique [[],[1,1],[1,1,3]]) (patternEdges [[],[1,1],[1,1,3]]) (patternAmount [[],[1,1],[1,1,3]]) (patternEdgeCount [[],[1,1],[1,1,3]]) [] := certificate_2053_checked

theorem certificate_2054_checked : certificate_2054.Valid 16 8 16 certificate_2054_q certificate_2054_edges 8 5 [] := by decide +kernel
theorem certificate_2054_valid : certificate_2054.Valid 16 8 (patternOrder [[],[1,1],[1,1,4]]) (patternClique [[],[1,1],[1,1,4]]) (patternEdges [[],[1,1],[1,1,4]]) (patternAmount [[],[1,1],[1,1,4]]) (patternEdgeCount [[],[1,1],[1,1,4]]) [] := certificate_2054_checked

theorem certificate_2055_checked : certificate_2055.Valid 16 8 14 certificate_2055_q certificate_2055_edges 6 5 [] := by decide +kernel
theorem certificate_2055_valid : certificate_2055.Valid 16 8 (patternOrder [[],[1,1],[1,2,1]]) (patternClique [[],[1,1],[1,2,1]]) (patternEdges [[],[1,1],[1,2,1]]) (patternAmount [[],[1,1],[1,2,1]]) (patternEdgeCount [[],[1,1],[1,2,1]]) [] := certificate_2055_checked

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

theorem patterns_16_8_18_verified_oai : ∀ D ∈ patterns_16_8_18, PatternVerified 16 8 D := by

  simp only [patterns_16_8_18, List.forall_mem_cons]

  exact ⟨⟨certificate_2040, certificate_2040_valid⟩, ⟨⟨certificate_2041, certificate_2041_valid⟩, ⟨⟨certificate_2042, certificate_2042_valid⟩, ⟨⟨certificate_2043, certificate_2043_valid⟩, ⟨⟨certificate_2044, certificate_2044_valid⟩, ⟨⟨certificate_2045, certificate_2045_valid⟩, ⟨⟨certificate_2046, certificate_2046_valid⟩, ⟨⟨certificate_2047, certificate_2047_valid⟩, ⟨⟨certificate_2048, certificate_2048_valid⟩, ⟨⟨certificate_2049, certificate_2049_valid⟩, ⟨⟨certificate_2050, certificate_2050_valid⟩, ⟨⟨certificate_2051, certificate_2051_valid⟩, ⟨⟨certificate_2052, certificate_2052_valid⟩, ⟨⟨certificate_2053, certificate_2053_valid⟩, ⟨⟨certificate_2054, certificate_2054_valid⟩, ⟨⟨certificate_2055, certificate_2055_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_18_verified_oai := @OAI.CycleClique.patterns_16_8_18_verified_oai
