-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_3_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:36:56.318723+00:00
-- url     : https://prove2.me/submissions/36e00dda-6296-4b8a-9f8a-6529f4daf8a7

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates071
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2268_checked : certificate_2268.Valid 17 8 15 certificate_2268_q certificate_2268_edges 7 3 [] := by decide +kernel
theorem certificate_2268_valid : certificate_2268.Valid 17 8 (patternOrder [[],[],[],[],[1,2,4]]) (patternClique [[],[],[],[],[1,2,4]]) (patternEdges [[],[],[],[],[1,2,4]]) (patternAmount [[],[],[],[],[1,2,4]]) (patternEdgeCount [[],[],[],[],[1,2,4]]) [] := certificate_2268_checked

theorem certificate_2269_checked : certificate_2269.Valid 17 8 16 certificate_2269_q certificate_2269_edges 8 3 [] := by decide +kernel
theorem certificate_2269_valid : certificate_2269.Valid 17 8 (patternOrder [[],[],[],[],[1,2,5]]) (patternClique [[],[],[],[],[1,2,5]]) (patternEdges [[],[],[],[],[1,2,5]]) (patternAmount [[],[],[],[],[1,2,5]]) (patternEdgeCount [[],[],[],[],[1,2,5]]) [] := certificate_2269_checked

theorem certificate_2270_checked : certificate_2270.Valid 17 8 17 certificate_2270_q certificate_2270_edges 9 3 [] := by decide +kernel
theorem certificate_2270_valid : certificate_2270.Valid 17 8 (patternOrder [[],[],[],[],[1,2,6]]) (patternClique [[],[],[],[],[1,2,6]]) (patternEdges [[],[],[],[],[1,2,6]]) (patternAmount [[],[],[],[],[1,2,6]]) (patternEdgeCount [[],[],[],[],[1,2,6]]) [] := certificate_2270_checked

theorem certificate_2271_checked : certificate_2271.Valid 17 8 13 certificate_2271_q certificate_2271_edges 5 3 [] := by decide +kernel
theorem certificate_2271_valid : certificate_2271.Valid 17 8 (patternOrder [[],[],[],[],[1,3,1]]) (patternClique [[],[],[],[],[1,3,1]]) (patternEdges [[],[],[],[],[1,3,1]]) (patternAmount [[],[],[],[],[1,3,1]]) (patternEdgeCount [[],[],[],[],[1,3,1]]) [] := certificate_2271_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates072
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2272_checked : certificate_2272.Valid 17 8 14 certificate_2272_q certificate_2272_edges 6 3 [] := by decide +kernel
theorem certificate_2272_valid : certificate_2272.Valid 17 8 (patternOrder [[],[],[],[],[1,3,2]]) (patternClique [[],[],[],[],[1,3,2]]) (patternEdges [[],[],[],[],[1,3,2]]) (patternAmount [[],[],[],[],[1,3,2]]) (patternEdgeCount [[],[],[],[],[1,3,2]]) [] := certificate_2272_checked

theorem certificate_2273_checked : certificate_2273.Valid 17 8 15 certificate_2273_q certificate_2273_edges 7 3 [] := by decide +kernel
theorem certificate_2273_valid : certificate_2273.Valid 17 8 (patternOrder [[],[],[],[],[1,3,3]]) (patternClique [[],[],[],[],[1,3,3]]) (patternEdges [[],[],[],[],[1,3,3]]) (patternAmount [[],[],[],[],[1,3,3]]) (patternEdgeCount [[],[],[],[],[1,3,3]]) [] := certificate_2273_checked

theorem certificate_2274_checked : certificate_2274.Valid 17 8 16 certificate_2274_q certificate_2274_edges 8 3 [] := by decide +kernel
theorem certificate_2274_valid : certificate_2274.Valid 17 8 (patternOrder [[],[],[],[],[1,3,4]]) (patternClique [[],[],[],[],[1,3,4]]) (patternEdges [[],[],[],[],[1,3,4]]) (patternAmount [[],[],[],[],[1,3,4]]) (patternEdgeCount [[],[],[],[],[1,3,4]]) [] := certificate_2274_checked

theorem certificate_2275_checked : certificate_2275.Valid 17 8 17 certificate_2275_q certificate_2275_edges 9 3 [] := by decide +kernel
theorem certificate_2275_valid : certificate_2275.Valid 17 8 (patternOrder [[],[],[],[],[1,3,5]]) (patternClique [[],[],[],[],[1,3,5]]) (patternEdges [[],[],[],[],[1,3,5]]) (patternAmount [[],[],[],[],[1,3,5]]) (patternEdgeCount [[],[],[],[],[1,3,5]]) [] := certificate_2275_checked

theorem certificate_2276_checked : certificate_2276.Valid 17 8 14 certificate_2276_q certificate_2276_edges 6 3 [] := by decide +kernel
theorem certificate_2276_valid : certificate_2276.Valid 17 8 (patternOrder [[],[],[],[],[1,4,1]]) (patternClique [[],[],[],[],[1,4,1]]) (patternEdges [[],[],[],[],[1,4,1]]) (patternAmount [[],[],[],[],[1,4,1]]) (patternEdgeCount [[],[],[],[],[1,4,1]]) [] := certificate_2276_checked

theorem certificate_2277_checked : certificate_2277.Valid 17 8 15 certificate_2277_q certificate_2277_edges 7 3 [] := by decide +kernel
theorem certificate_2277_valid : certificate_2277.Valid 17 8 (patternOrder [[],[],[],[],[1,4,2]]) (patternClique [[],[],[],[],[1,4,2]]) (patternEdges [[],[],[],[],[1,4,2]]) (patternAmount [[],[],[],[],[1,4,2]]) (patternEdgeCount [[],[],[],[],[1,4,2]]) [] := certificate_2277_checked

theorem certificate_2278_checked : certificate_2278.Valid 17 8 16 certificate_2278_q certificate_2278_edges 8 3 [] := by decide +kernel
theorem certificate_2278_valid : certificate_2278.Valid 17 8 (patternOrder [[],[],[],[],[1,4,3]]) (patternClique [[],[],[],[],[1,4,3]]) (patternEdges [[],[],[],[],[1,4,3]]) (patternAmount [[],[],[],[],[1,4,3]]) (patternEdgeCount [[],[],[],[],[1,4,3]]) [] := certificate_2278_checked

theorem certificate_2279_checked : certificate_2279.Valid 17 8 17 certificate_2279_q certificate_2279_edges 9 3 [] := by decide +kernel
theorem certificate_2279_valid : certificate_2279.Valid 17 8 (patternOrder [[],[],[],[],[1,4,4]]) (patternClique [[],[],[],[],[1,4,4]]) (patternEdges [[],[],[],[],[1,4,4]]) (patternAmount [[],[],[],[],[1,4,4]]) (patternEdgeCount [[],[],[],[],[1,4,4]]) [] := certificate_2279_checked

theorem certificate_2280_checked : certificate_2280.Valid 17 8 15 certificate_2280_q certificate_2280_edges 7 3 [] := by decide +kernel
theorem certificate_2280_valid : certificate_2280.Valid 17 8 (patternOrder [[],[],[],[],[1,5,1]]) (patternClique [[],[],[],[],[1,5,1]]) (patternEdges [[],[],[],[],[1,5,1]]) (patternAmount [[],[],[],[],[1,5,1]]) (patternEdgeCount [[],[],[],[],[1,5,1]]) [] := certificate_2280_checked

theorem certificate_2281_checked : certificate_2281.Valid 17 8 16 certificate_2281_q certificate_2281_edges 8 3 [] := by decide +kernel
theorem certificate_2281_valid : certificate_2281.Valid 17 8 (patternOrder [[],[],[],[],[1,5,2]]) (patternClique [[],[],[],[],[1,5,2]]) (patternEdges [[],[],[],[],[1,5,2]]) (patternAmount [[],[],[],[],[1,5,2]]) (patternEdgeCount [[],[],[],[],[1,5,2]]) [] := certificate_2281_checked

theorem certificate_2282_checked : certificate_2282.Valid 17 8 17 certificate_2282_q certificate_2282_edges 9 3 [] := by decide +kernel
theorem certificate_2282_valid : certificate_2282.Valid 17 8 (patternOrder [[],[],[],[],[1,5,3]]) (patternClique [[],[],[],[],[1,5,3]]) (patternEdges [[],[],[],[],[1,5,3]]) (patternAmount [[],[],[],[],[1,5,3]]) (patternEdgeCount [[],[],[],[],[1,5,3]]) [] := certificate_2282_checked

theorem certificate_2283_checked : certificate_2283.Valid 17 8 16 certificate_2283_q certificate_2283_edges 8 3 [] := by decide +kernel
theorem certificate_2283_valid : certificate_2283.Valid 17 8 (patternOrder [[],[],[],[],[1,6,1]]) (patternClique [[],[],[],[],[1,6,1]]) (patternEdges [[],[],[],[],[1,6,1]]) (patternAmount [[],[],[],[],[1,6,1]]) (patternEdgeCount [[],[],[],[],[1,6,1]]) [] := certificate_2283_checked

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

theorem patterns_17_8_3_verified_oai : ∀ D ∈ patterns_17_8_3, PatternVerified 17 8 D := by

  simp only [patterns_17_8_3, List.forall_mem_cons]

  exact ⟨⟨certificate_2268, certificate_2268_valid⟩, ⟨⟨certificate_2269, certificate_2269_valid⟩, ⟨⟨certificate_2270, certificate_2270_valid⟩, ⟨⟨certificate_2271, certificate_2271_valid⟩, ⟨⟨certificate_2272, certificate_2272_valid⟩, ⟨⟨certificate_2273, certificate_2273_valid⟩, ⟨⟨certificate_2274, certificate_2274_valid⟩, ⟨⟨certificate_2275, certificate_2275_valid⟩, ⟨⟨certificate_2276, certificate_2276_valid⟩, ⟨⟨certificate_2277, certificate_2277_valid⟩, ⟨⟨certificate_2278, certificate_2278_valid⟩, ⟨⟨certificate_2279, certificate_2279_valid⟩, ⟨⟨certificate_2280, certificate_2280_valid⟩, ⟨⟨certificate_2281, certificate_2281_valid⟩, ⟨⟨certificate_2282, certificate_2282_valid⟩, ⟨⟨certificate_2283, certificate_2283_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_3_verified_oai := @OAI.CycleClique.patterns_17_8_3_verified_oai
