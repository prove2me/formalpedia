-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_18_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:09:28.141916+00:00
-- url     : https://prove2.me/submissions/23c65dd8-7370-4552-a47d-51e9bd231eb6

import Mathlib
import Definitions.Def_OAIQ107D082
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates079
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2508_checked : certificate_2508.Valid 17 8 14 certificate_2508_q certificate_2508_edges 6 5 [] := by decide +kernel
theorem certificate_2508_valid : certificate_2508.Valid 17 8 (patternOrder [[],[],[1,1,1,2,1]]) (patternClique [[],[],[1,1,1,2,1]]) (patternEdges [[],[],[1,1,1,2,1]]) (patternAmount [[],[],[1,1,1,2,1]]) (patternEdgeCount [[],[],[1,1,1,2,1]]) [] := certificate_2508_checked

theorem certificate_2509_checked : certificate_2509.Valid 17 8 15 certificate_2509_q certificate_2509_edges 7 5 [] := by decide +kernel
theorem certificate_2509_valid : certificate_2509.Valid 17 8 (patternOrder [[],[],[1,1,1,2,2]]) (patternClique [[],[],[1,1,1,2,2]]) (patternEdges [[],[],[1,1,1,2,2]]) (patternAmount [[],[],[1,1,1,2,2]]) (patternEdgeCount [[],[],[1,1,1,2,2]]) [] := certificate_2509_checked

theorem certificate_2510_checked : certificate_2510.Valid 17 8 16 certificate_2510_q certificate_2510_edges 8 5 [] := by decide +kernel
theorem certificate_2510_valid : certificate_2510.Valid 17 8 (patternOrder [[],[],[1,1,1,2,3]]) (patternClique [[],[],[1,1,1,2,3]]) (patternEdges [[],[],[1,1,1,2,3]]) (patternAmount [[],[],[1,1,1,2,3]]) (patternEdgeCount [[],[],[1,1,1,2,3]]) [] := certificate_2510_checked

theorem certificate_2511_checked : certificate_2511.Valid 17 8 17 certificate_2511_q certificate_2511_edges 9 5 [] := by decide +kernel
theorem certificate_2511_valid : certificate_2511.Valid 17 8 (patternOrder [[],[],[1,1,1,2,4]]) (patternClique [[],[],[1,1,1,2,4]]) (patternEdges [[],[],[1,1,1,2,4]]) (patternAmount [[],[],[1,1,1,2,4]]) (patternEdgeCount [[],[],[1,1,1,2,4]]) [] := certificate_2511_checked

theorem certificate_2512_checked : certificate_2512.Valid 17 8 15 certificate_2512_q certificate_2512_edges 7 5 [] := by decide +kernel
theorem certificate_2512_valid : certificate_2512.Valid 17 8 (patternOrder [[],[],[1,1,1,3,1]]) (patternClique [[],[],[1,1,1,3,1]]) (patternEdges [[],[],[1,1,1,3,1]]) (patternAmount [[],[],[1,1,1,3,1]]) (patternEdgeCount [[],[],[1,1,1,3,1]]) [] := certificate_2512_checked

theorem certificate_2513_checked : certificate_2513.Valid 17 8 16 certificate_2513_q certificate_2513_edges 8 5 [] := by decide +kernel
theorem certificate_2513_valid : certificate_2513.Valid 17 8 (patternOrder [[],[],[1,1,1,3,2]]) (patternClique [[],[],[1,1,1,3,2]]) (patternEdges [[],[],[1,1,1,3,2]]) (patternAmount [[],[],[1,1,1,3,2]]) (patternEdgeCount [[],[],[1,1,1,3,2]]) [] := certificate_2513_checked

theorem certificate_2514_checked : certificate_2514.Valid 17 8 17 certificate_2514_q certificate_2514_edges 9 5 [] := by decide +kernel
theorem certificate_2514_valid : certificate_2514.Valid 17 8 (patternOrder [[],[],[1,1,1,3,3]]) (patternClique [[],[],[1,1,1,3,3]]) (patternEdges [[],[],[1,1,1,3,3]]) (patternAmount [[],[],[1,1,1,3,3]]) (patternEdgeCount [[],[],[1,1,1,3,3]]) [] := certificate_2514_checked

theorem certificate_2515_checked : certificate_2515.Valid 17 8 16 certificate_2515_q certificate_2515_edges 8 5 [] := by decide +kernel
theorem certificate_2515_valid : certificate_2515.Valid 17 8 (patternOrder [[],[],[1,1,1,4,1]]) (patternClique [[],[],[1,1,1,4,1]]) (patternEdges [[],[],[1,1,1,4,1]]) (patternAmount [[],[],[1,1,1,4,1]]) (patternEdgeCount [[],[],[1,1,1,4,1]]) [] := certificate_2515_checked

theorem certificate_2516_checked : certificate_2516.Valid 17 8 17 certificate_2516_q certificate_2516_edges 9 5 [] := by decide +kernel
theorem certificate_2516_valid : certificate_2516.Valid 17 8 (patternOrder [[],[],[1,1,1,4,2]]) (patternClique [[],[],[1,1,1,4,2]]) (patternEdges [[],[],[1,1,1,4,2]]) (patternAmount [[],[],[1,1,1,4,2]]) (patternEdgeCount [[],[],[1,1,1,4,2]]) [] := certificate_2516_checked

theorem certificate_2517_checked : certificate_2517.Valid 17 8 17 certificate_2517_q certificate_2517_edges 9 5 [] := by decide +kernel
theorem certificate_2517_valid : certificate_2517.Valid 17 8 (patternOrder [[],[],[1,1,1,5,1]]) (patternClique [[],[],[1,1,1,5,1]]) (patternEdges [[],[],[1,1,1,5,1]]) (patternAmount [[],[],[1,1,1,5,1]]) (patternEdgeCount [[],[],[1,1,1,5,1]]) [] := certificate_2517_checked

theorem certificate_2518_checked : certificate_2518.Valid 17 8 14 certificate_2518_q certificate_2518_edges 6 4 [] := by decide +kernel
theorem certificate_2518_valid : certificate_2518.Valid 17 8 (patternOrder [[],[],[1,1,2],[2]]) (patternClique [[],[],[1,1,2],[2]]) (patternEdges [[],[],[1,1,2],[2]]) (patternAmount [[],[],[1,1,2],[2]]) (patternEdgeCount [[],[],[1,1,2],[2]]) [] := certificate_2518_checked

theorem certificate_2519_checked : certificate_2519.Valid 17 8 15 certificate_2519_q certificate_2519_edges 7 4 [] := by decide +kernel
theorem certificate_2519_valid : certificate_2519.Valid 17 8 (patternOrder [[],[],[1,1,2],[3]]) (patternClique [[],[],[1,1,2],[3]]) (patternEdges [[],[],[1,1,2],[3]]) (patternAmount [[],[],[1,1,2],[3]]) (patternEdgeCount [[],[],[1,1,2],[3]]) [] := certificate_2519_checked

theorem certificate_2520_checked : certificate_2520.Valid 17 8 16 certificate_2520_q certificate_2520_edges 8 4 [] := by decide +kernel
theorem certificate_2520_valid : certificate_2520.Valid 17 8 (patternOrder [[],[],[1,1,2],[4]]) (patternClique [[],[],[1,1,2],[4]]) (patternEdges [[],[],[1,1,2],[4]]) (patternAmount [[],[],[1,1,2],[4]]) (patternEdgeCount [[],[],[1,1,2],[4]]) [] := certificate_2520_checked

theorem certificate_2521_checked : certificate_2521.Valid 17 8 17 certificate_2521_q certificate_2521_edges 9 4 [] := by decide +kernel
theorem certificate_2521_valid : certificate_2521.Valid 17 8 (patternOrder [[],[],[1,1,2],[5]]) (patternClique [[],[],[1,1,2],[5]]) (patternEdges [[],[],[1,1,2],[5]]) (patternAmount [[],[],[1,1,2],[5]]) (patternEdgeCount [[],[],[1,1,2],[5]]) [] := certificate_2521_checked

theorem certificate_2522_checked : certificate_2522.Valid 17 8 14 certificate_2522_q certificate_2522_edges 6 5 [] := by decide +kernel
theorem certificate_2522_valid : certificate_2522.Valid 17 8 (patternOrder [[],[],[1,1,2,1,1]]) (patternClique [[],[],[1,1,2,1,1]]) (patternEdges [[],[],[1,1,2,1,1]]) (patternAmount [[],[],[1,1,2,1,1]]) (patternEdgeCount [[],[],[1,1,2,1,1]]) [] := certificate_2522_checked

theorem certificate_2523_checked : certificate_2523.Valid 17 8 15 certificate_2523_q certificate_2523_edges 7 5 [] := by decide +kernel
theorem certificate_2523_valid : certificate_2523.Valid 17 8 (patternOrder [[],[],[1,1,2,1,2]]) (patternClique [[],[],[1,1,2,1,2]]) (patternEdges [[],[],[1,1,2,1,2]]) (patternAmount [[],[],[1,1,2,1,2]]) (patternEdgeCount [[],[],[1,1,2,1,2]]) [] := certificate_2523_checked

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

theorem patterns_17_8_18_verified_oai : ∀ D ∈ patterns_17_8_18, PatternVerified 17 8 D := by

  simp only [patterns_17_8_18, List.forall_mem_cons]

  exact ⟨⟨certificate_2508, certificate_2508_valid⟩, ⟨⟨certificate_2509, certificate_2509_valid⟩, ⟨⟨certificate_2510, certificate_2510_valid⟩, ⟨⟨certificate_2511, certificate_2511_valid⟩, ⟨⟨certificate_2512, certificate_2512_valid⟩, ⟨⟨certificate_2513, certificate_2513_valid⟩, ⟨⟨certificate_2514, certificate_2514_valid⟩, ⟨⟨certificate_2515, certificate_2515_valid⟩, ⟨⟨certificate_2516, certificate_2516_valid⟩, ⟨⟨certificate_2517, certificate_2517_valid⟩, ⟨⟨certificate_2518, certificate_2518_valid⟩, ⟨⟨certificate_2519, certificate_2519_valid⟩, ⟨⟨certificate_2520, certificate_2520_valid⟩, ⟨⟨certificate_2521, certificate_2521_valid⟩, ⟨⟨certificate_2522, certificate_2522_valid⟩, ⟨⟨certificate_2523, certificate_2523_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_18_verified_oai := @OAI.CycleClique.patterns_17_8_18_verified_oai
