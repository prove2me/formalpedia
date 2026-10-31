-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_17_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:41:11.550002+00:00
-- url     : https://prove2.me/submissions/eff66267-ec24-4691-bdab-22858068af4a

import Mathlib
import Definitions.Def_OAIQ107D130
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

theorem certificate_2024_checked : certificate_2024.Valid 16 8 14 certificate_2024_q certificate_2024_edges 6 5 [] := by decide +kernel
theorem certificate_2024_valid : certificate_2024.Valid 16 8 (patternOrder [[],[1],[1,1,1,2]]) (patternClique [[],[1],[1,1,1,2]]) (patternEdges [[],[1],[1,1,1,2]]) (patternAmount [[],[1],[1,1,1,2]]) (patternEdgeCount [[],[1],[1,1,1,2]]) [] := certificate_2024_checked

theorem certificate_2025_checked : certificate_2025.Valid 16 8 15 certificate_2025_q certificate_2025_edges 7 5 [] := by decide +kernel
theorem certificate_2025_valid : certificate_2025.Valid 16 8 (patternOrder [[],[1],[1,1,1,3]]) (patternClique [[],[1],[1,1,1,3]]) (patternEdges [[],[1],[1,1,1,3]]) (patternAmount [[],[1],[1,1,1,3]]) (patternEdgeCount [[],[1],[1,1,1,3]]) [] := certificate_2025_checked

theorem certificate_2026_checked : certificate_2026.Valid 16 8 16 certificate_2026_q certificate_2026_edges 8 5 [] := by decide +kernel
theorem certificate_2026_valid : certificate_2026.Valid 16 8 (patternOrder [[],[1],[1,1,1,4]]) (patternClique [[],[1],[1,1,1,4]]) (patternEdges [[],[1],[1,1,1,4]]) (patternAmount [[],[1],[1,1,1,4]]) (patternEdgeCount [[],[1],[1,1,1,4]]) [] := certificate_2026_checked

theorem certificate_2027_checked : certificate_2027.Valid 16 8 14 certificate_2027_q certificate_2027_edges 6 5 [] := by decide +kernel
theorem certificate_2027_valid : certificate_2027.Valid 16 8 (patternOrder [[],[1],[1,1,2,1]]) (patternClique [[],[1],[1,1,2,1]]) (patternEdges [[],[1],[1,1,2,1]]) (patternAmount [[],[1],[1,1,2,1]]) (patternEdgeCount [[],[1],[1,1,2,1]]) [] := certificate_2027_checked

theorem certificate_2028_checked : certificate_2028.Valid 16 8 15 certificate_2028_q certificate_2028_edges 7 5 [] := by decide +kernel
theorem certificate_2028_valid : certificate_2028.Valid 16 8 (patternOrder [[],[1],[1,1,2,2]]) (patternClique [[],[1],[1,1,2,2]]) (patternEdges [[],[1],[1,1,2,2]]) (patternAmount [[],[1],[1,1,2,2]]) (patternEdgeCount [[],[1],[1,1,2,2]]) [] := certificate_2028_checked

theorem certificate_2029_checked : certificate_2029.Valid 16 8 16 certificate_2029_q certificate_2029_edges 8 5 [] := by decide +kernel
theorem certificate_2029_valid : certificate_2029.Valid 16 8 (patternOrder [[],[1],[1,1,2,3]]) (patternClique [[],[1],[1,1,2,3]]) (patternEdges [[],[1],[1,1,2,3]]) (patternAmount [[],[1],[1,1,2,3]]) (patternEdgeCount [[],[1],[1,1,2,3]]) [] := certificate_2029_checked

theorem certificate_2030_checked : certificate_2030.Valid 16 8 15 certificate_2030_q certificate_2030_edges 7 5 [] := by decide +kernel
theorem certificate_2030_valid : certificate_2030.Valid 16 8 (patternOrder [[],[1],[1,1,3,1]]) (patternClique [[],[1],[1,1,3,1]]) (patternEdges [[],[1],[1,1,3,1]]) (patternAmount [[],[1],[1,1,3,1]]) (patternEdgeCount [[],[1],[1,1,3,1]]) [] := certificate_2030_checked

theorem certificate_2031_checked : certificate_2031.Valid 16 8 16 certificate_2031_q certificate_2031_edges 8 5 [] := by decide +kernel
theorem certificate_2031_valid : certificate_2031.Valid 16 8 (patternOrder [[],[1],[1,1,3,2]]) (patternClique [[],[1],[1,1,3,2]]) (patternEdges [[],[1],[1,1,3,2]]) (patternAmount [[],[1],[1,1,3,2]]) (patternEdgeCount [[],[1],[1,1,3,2]]) [] := certificate_2031_checked

theorem certificate_2032_checked : certificate_2032.Valid 16 8 16 certificate_2032_q certificate_2032_edges 8 5 [] := by decide +kernel
theorem certificate_2032_valid : certificate_2032.Valid 16 8 (patternOrder [[],[1],[1,1,4,1]]) (patternClique [[],[1],[1,1,4,1]]) (patternEdges [[],[1],[1,1,4,1]]) (patternAmount [[],[1],[1,1,4,1]]) (patternEdgeCount [[],[1],[1,1,4,1]]) [] := certificate_2032_checked

theorem certificate_2033_checked : certificate_2033.Valid 16 8 14 certificate_2033_q certificate_2033_edges 6 4 [] := by decide +kernel
theorem certificate_2033_valid : certificate_2033.Valid 16 8 (patternOrder [[],[1],[1,2],[2]]) (patternClique [[],[1],[1,2],[2]]) (patternEdges [[],[1],[1,2],[2]]) (patternAmount [[],[1],[1,2],[2]]) (patternEdgeCount [[],[1],[1,2],[2]]) [] := certificate_2033_checked

theorem certificate_2034_checked : certificate_2034.Valid 16 8 15 certificate_2034_q certificate_2034_edges 7 4 [] := by decide +kernel
theorem certificate_2034_valid : certificate_2034.Valid 16 8 (patternOrder [[],[1],[1,2],[3]]) (patternClique [[],[1],[1,2],[3]]) (patternEdges [[],[1],[1,2],[3]]) (patternAmount [[],[1],[1,2],[3]]) (patternEdgeCount [[],[1],[1,2],[3]]) [] := certificate_2034_checked

theorem certificate_2035_checked : certificate_2035.Valid 16 8 16 certificate_2035_q certificate_2035_edges 8 4 [] := by decide +kernel
theorem certificate_2035_valid : certificate_2035.Valid 16 8 (patternOrder [[],[1],[1,2],[4]]) (patternClique [[],[1],[1,2],[4]]) (patternEdges [[],[1],[1,2],[4]]) (patternAmount [[],[1],[1,2],[4]]) (patternEdgeCount [[],[1],[1,2],[4]]) [] := certificate_2035_checked

theorem certificate_2036_checked : certificate_2036.Valid 16 8 15 certificate_2036_q certificate_2036_edges 7 5 [] := by decide +kernel
theorem certificate_2036_valid : certificate_2036.Valid 16 8 (patternOrder [[],[1],[1,2,1,2]]) (patternClique [[],[1],[1,2,1,2]]) (patternEdges [[],[1],[1,2,1,2]]) (patternAmount [[],[1],[1,2,1,2]]) (patternEdgeCount [[],[1],[1,2,1,2]]) [] := certificate_2036_checked

theorem certificate_2037_checked : certificate_2037.Valid 16 8 16 certificate_2037_q certificate_2037_edges 8 5 [] := by decide +kernel
theorem certificate_2037_valid : certificate_2037.Valid 16 8 (patternOrder [[],[1],[1,2,1,3]]) (patternClique [[],[1],[1,2,1,3]]) (patternEdges [[],[1],[1,2,1,3]]) (patternAmount [[],[1],[1,2,1,3]]) (patternEdgeCount [[],[1],[1,2,1,3]]) [] := certificate_2037_checked

theorem certificate_2038_checked : certificate_2038.Valid 16 8 15 certificate_2038_q certificate_2038_edges 7 5 [] := by decide +kernel
theorem certificate_2038_valid : certificate_2038.Valid 16 8 (patternOrder [[],[1],[1,2,2,1]]) (patternClique [[],[1],[1,2,2,1]]) (patternEdges [[],[1],[1,2,2,1]]) (patternAmount [[],[1],[1,2,2,1]]) (patternEdgeCount [[],[1],[1,2,2,1]]) [] := certificate_2038_checked

theorem certificate_2039_checked : certificate_2039.Valid 16 8 16 certificate_2039_q certificate_2039_edges 8 5 [] := by decide +kernel
theorem certificate_2039_valid : certificate_2039.Valid 16 8 (patternOrder [[],[1],[1,2,2,2]]) (patternClique [[],[1],[1,2,2,2]]) (patternEdges [[],[1],[1,2,2,2]]) (patternAmount [[],[1],[1,2,2,2]]) (patternEdgeCount [[],[1],[1,2,2,2]]) [] := certificate_2039_checked

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

theorem patterns_16_8_17_verified_oai : ∀ D ∈ patterns_16_8_17, PatternVerified 16 8 D := by

  simp only [patterns_16_8_17, List.forall_mem_cons]

  exact ⟨⟨certificate_2024, certificate_2024_valid⟩, ⟨⟨certificate_2025, certificate_2025_valid⟩, ⟨⟨certificate_2026, certificate_2026_valid⟩, ⟨⟨certificate_2027, certificate_2027_valid⟩, ⟨⟨certificate_2028, certificate_2028_valid⟩, ⟨⟨certificate_2029, certificate_2029_valid⟩, ⟨⟨certificate_2030, certificate_2030_valid⟩, ⟨⟨certificate_2031, certificate_2031_valid⟩, ⟨⟨certificate_2032, certificate_2032_valid⟩, ⟨⟨certificate_2033, certificate_2033_valid⟩, ⟨⟨certificate_2034, certificate_2034_valid⟩, ⟨⟨certificate_2035, certificate_2035_valid⟩, ⟨⟨certificate_2036, certificate_2036_valid⟩, ⟨⟨certificate_2037, certificate_2037_valid⟩, ⟨⟨certificate_2038, certificate_2038_valid⟩, ⟨⟨certificate_2039, certificate_2039_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_17_verified_oai := @OAI.CycleClique.patterns_16_8_17_verified_oai
