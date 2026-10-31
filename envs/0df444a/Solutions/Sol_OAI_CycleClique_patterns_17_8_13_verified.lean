-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_13_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:03:14.486468+00:00
-- url     : https://prove2.me/submissions/66db8baf-6658-4d1a-91b5-90bcbe45202b

import Mathlib
import Definitions.Def_OAIQ107D079
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates076
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2428_checked : certificate_2428.Valid 17 8 16 certificate_2428_q certificate_2428_edges 8 3 [] := by decide +kernel
theorem certificate_2428_valid : certificate_2428.Valid 17 8 (patternOrder [[],[],[],[2,3],[3]]) (patternClique [[],[],[],[2,3],[3]]) (patternEdges [[],[],[],[2,3],[3]]) (patternAmount [[],[],[],[2,3],[3]]) (patternEdgeCount [[],[],[],[2,3],[3]]) [] := certificate_2428_checked

theorem certificate_2429_checked : certificate_2429.Valid 17 8 17 certificate_2429_q certificate_2429_edges 9 3 [] := by decide +kernel
theorem certificate_2429_valid : certificate_2429.Valid 17 8 (patternOrder [[],[],[],[2,3],[4]]) (patternClique [[],[],[],[2,3],[4]]) (patternEdges [[],[],[],[2,3],[4]]) (patternAmount [[],[],[],[2,3],[4]]) (patternEdgeCount [[],[],[],[2,3],[4]]) [] := certificate_2429_checked

theorem certificate_2430_checked : certificate_2430.Valid 17 8 17 certificate_2430_q certificate_2430_edges 9 4 [] := by decide +kernel
theorem certificate_2430_valid : certificate_2430.Valid 17 8 (patternOrder [[],[],[],[2,3,1,3]]) (patternClique [[],[],[],[2,3,1,3]]) (patternEdges [[],[],[],[2,3,1,3]]) (patternAmount [[],[],[],[2,3,1,3]]) (patternEdgeCount [[],[],[],[2,3,1,3]]) [] := certificate_2430_checked

theorem certificate_2431_checked : certificate_2431.Valid 17 8 17 certificate_2431_q certificate_2431_edges 9 3 [] := by decide +kernel
theorem certificate_2431_valid : certificate_2431.Valid 17 8 (patternOrder [[],[],[],[2,4],[3]]) (patternClique [[],[],[],[2,4],[3]]) (patternEdges [[],[],[],[2,4],[3]]) (patternAmount [[],[],[],[2,4],[3]]) (patternEdgeCount [[],[],[],[2,4],[3]]) [] := certificate_2431_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates077
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2432_checked : certificate_2432.Valid 17 8 17 certificate_2432_q certificate_2432_edges 9 3 [] := by decide +kernel
theorem certificate_2432_valid : certificate_2432.Valid 17 8 (patternOrder [[],[],[],[3],[3,3]]) (patternClique [[],[],[],[3],[3,3]]) (patternEdges [[],[],[],[3],[3,3]]) (patternAmount [[],[],[],[3],[3,3]]) (patternEdgeCount [[],[],[],[3],[3,3]]) [] := certificate_2432_checked

theorem certificate_2433_checked : certificate_2433.Valid 17 8 16 certificate_2433_q certificate_2433_edges 8 4 [] := by decide +kernel
theorem certificate_2433_valid : certificate_2433.Valid 17 8 (patternOrder [[],[],[],[3,1,1,3]]) (patternClique [[],[],[],[3,1,1,3]]) (patternEdges [[],[],[],[3,1,1,3]]) (patternAmount [[],[],[],[3,1,1,3]]) (patternEdgeCount [[],[],[],[3,1,1,3]]) [] := certificate_2433_checked

theorem certificate_2434_checked : certificate_2434.Valid 17 8 17 certificate_2434_q certificate_2434_edges 9 4 [] := by decide +kernel
theorem certificate_2434_valid : certificate_2434.Valid 17 8 (patternOrder [[],[],[],[3,1,1,4]]) (patternClique [[],[],[],[3,1,1,4]]) (patternEdges [[],[],[],[3,1,1,4]]) (patternAmount [[],[],[],[3,1,1,4]]) (patternEdgeCount [[],[],[],[3,1,1,4]]) [] := certificate_2434_checked

theorem certificate_2435_checked : certificate_2435.Valid 17 8 17 certificate_2435_q certificate_2435_edges 9 4 [] := by decide +kernel
theorem certificate_2435_valid : certificate_2435.Valid 17 8 (patternOrder [[],[],[],[3,1,2,3]]) (patternClique [[],[],[],[3,1,2,3]]) (patternEdges [[],[],[],[3,1,2,3]]) (patternAmount [[],[],[],[3,1,2,3]]) (patternEdgeCount [[],[],[],[3,1,2,3]]) [] := certificate_2435_checked

theorem certificate_2436_checked : certificate_2436.Valid 17 8 11 certificate_2436_q certificate_2436_edges 3 3 [] := by decide +kernel
theorem certificate_2436_valid : certificate_2436.Valid 17 8 (patternOrder [[],[],[1],[1],[1]]) (patternClique [[],[],[1],[1],[1]]) (patternEdges [[],[],[1],[1],[1]]) (patternAmount [[],[],[1],[1],[1]]) (patternEdgeCount [[],[],[1],[1],[1]]) [] := certificate_2436_checked

theorem certificate_2437_checked : certificate_2437.Valid 17 8 12 certificate_2437_q certificate_2437_edges 4 3 [] := by decide +kernel
theorem certificate_2437_valid : certificate_2437.Valid 17 8 (patternOrder [[],[],[1],[1],[2]]) (patternClique [[],[],[1],[1],[2]]) (patternEdges [[],[],[1],[1],[2]]) (patternAmount [[],[],[1],[1],[2]]) (patternEdgeCount [[],[],[1],[1],[2]]) [] := certificate_2437_checked

theorem certificate_2438_checked : certificate_2438.Valid 17 8 13 certificate_2438_q certificate_2438_edges 5 3 [] := by decide +kernel
theorem certificate_2438_valid : certificate_2438.Valid 17 8 (patternOrder [[],[],[1],[1],[3]]) (patternClique [[],[],[1],[1],[3]]) (patternEdges [[],[],[1],[1],[3]]) (patternAmount [[],[],[1],[1],[3]]) (patternEdgeCount [[],[],[1],[1],[3]]) [] := certificate_2438_checked

theorem certificate_2439_checked : certificate_2439.Valid 17 8 14 certificate_2439_q certificate_2439_edges 6 3 [] := by decide +kernel
theorem certificate_2439_valid : certificate_2439.Valid 17 8 (patternOrder [[],[],[1],[1],[4]]) (patternClique [[],[],[1],[1],[4]]) (patternEdges [[],[],[1],[1],[4]]) (patternAmount [[],[],[1],[1],[4]]) (patternEdgeCount [[],[],[1],[1],[4]]) [] := certificate_2439_checked

theorem certificate_2440_checked : certificate_2440.Valid 17 8 15 certificate_2440_q certificate_2440_edges 7 3 [] := by decide +kernel
theorem certificate_2440_valid : certificate_2440.Valid 17 8 (patternOrder [[],[],[1],[1],[5]]) (patternClique [[],[],[1],[1],[5]]) (patternEdges [[],[],[1],[1],[5]]) (patternAmount [[],[],[1],[1],[5]]) (patternEdgeCount [[],[],[1],[1],[5]]) [] := certificate_2440_checked

theorem certificate_2441_checked : certificate_2441.Valid 17 8 16 certificate_2441_q certificate_2441_edges 8 3 [] := by decide +kernel
theorem certificate_2441_valid : certificate_2441.Valid 17 8 (patternOrder [[],[],[1],[1],[6]]) (patternClique [[],[],[1],[1],[6]]) (patternEdges [[],[],[1],[1],[6]]) (patternAmount [[],[],[1],[1],[6]]) (patternEdgeCount [[],[],[1],[1],[6]]) [] := certificate_2441_checked

theorem certificate_2442_checked : certificate_2442.Valid 17 8 17 certificate_2442_q certificate_2442_edges 9 3 [] := by decide +kernel
theorem certificate_2442_valid : certificate_2442.Valid 17 8 (patternOrder [[],[],[1],[1],[7]]) (patternClique [[],[],[1],[1],[7]]) (patternEdges [[],[],[1],[1],[7]]) (patternAmount [[],[],[1],[1],[7]]) (patternEdgeCount [[],[],[1],[1],[7]]) [] := certificate_2442_checked

theorem certificate_2443_checked : certificate_2443.Valid 17 8 12 certificate_2443_q certificate_2443_edges 4 4 [] := by decide +kernel
theorem certificate_2443_valid : certificate_2443.Valid 17 8 (patternOrder [[],[],[1],[1,1,1]]) (patternClique [[],[],[1],[1,1,1]]) (patternEdges [[],[],[1],[1,1,1]]) (patternAmount [[],[],[1],[1,1,1]]) (patternEdgeCount [[],[],[1],[1,1,1]]) [] := certificate_2443_checked

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

theorem patterns_17_8_13_verified_oai : ∀ D ∈ patterns_17_8_13, PatternVerified 17 8 D := by

  simp only [patterns_17_8_13, List.forall_mem_cons]

  exact ⟨⟨certificate_2428, certificate_2428_valid⟩, ⟨⟨certificate_2429, certificate_2429_valid⟩, ⟨⟨certificate_2430, certificate_2430_valid⟩, ⟨⟨certificate_2431, certificate_2431_valid⟩, ⟨⟨certificate_2432, certificate_2432_valid⟩, ⟨⟨certificate_2433, certificate_2433_valid⟩, ⟨⟨certificate_2434, certificate_2434_valid⟩, ⟨⟨certificate_2435, certificate_2435_valid⟩, ⟨⟨certificate_2436, certificate_2436_valid⟩, ⟨⟨certificate_2437, certificate_2437_valid⟩, ⟨⟨certificate_2438, certificate_2438_valid⟩, ⟨⟨certificate_2439, certificate_2439_valid⟩, ⟨⟨certificate_2440, certificate_2440_valid⟩, ⟨⟨certificate_2441, certificate_2441_valid⟩, ⟨⟨certificate_2442, certificate_2442_valid⟩, ⟨⟨certificate_2443, certificate_2443_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_13_verified_oai := @OAI.CycleClique.patterns_17_8_13_verified_oai
