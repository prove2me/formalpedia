-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_5_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:00:55.62283+00:00
-- url     : https://prove2.me/submissions/012cd696-f37d-40b3-b6e1-afe230e8297e

import Mathlib
import Definitions.Def_OAIQ107D074
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates072
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2300_checked : certificate_2300.Valid 17 8 17 certificate_2300_q certificate_2300_edges 9 3 [] := by decide +kernel
theorem certificate_2300_valid : certificate_2300.Valid 17 8 (patternOrder [[],[],[],[],[2,2,5]]) (patternClique [[],[],[],[],[2,2,5]]) (patternEdges [[],[],[],[],[2,2,5]]) (patternAmount [[],[],[],[],[2,2,5]]) (patternEdgeCount [[],[],[],[],[2,2,5]]) [] := certificate_2300_checked

theorem certificate_2301_checked : certificate_2301.Valid 17 8 15 certificate_2301_q certificate_2301_edges 7 3 [] := by decide +kernel
theorem certificate_2301_valid : certificate_2301.Valid 17 8 (patternOrder [[],[],[],[],[2,3,2]]) (patternClique [[],[],[],[],[2,3,2]]) (patternEdges [[],[],[],[],[2,3,2]]) (patternAmount [[],[],[],[],[2,3,2]]) (patternEdgeCount [[],[],[],[],[2,3,2]]) [] := certificate_2301_checked

theorem certificate_2302_checked : certificate_2302.Valid 17 8 16 certificate_2302_q certificate_2302_edges 8 3 [] := by decide +kernel
theorem certificate_2302_valid : certificate_2302.Valid 17 8 (patternOrder [[],[],[],[],[2,3,3]]) (patternClique [[],[],[],[],[2,3,3]]) (patternEdges [[],[],[],[],[2,3,3]]) (patternAmount [[],[],[],[],[2,3,3]]) (patternEdgeCount [[],[],[],[],[2,3,3]]) [] := certificate_2302_checked

theorem certificate_2303_checked : certificate_2303.Valid 17 8 17 certificate_2303_q certificate_2303_edges 9 3 [] := by decide +kernel
theorem certificate_2303_valid : certificate_2303.Valid 17 8 (patternOrder [[],[],[],[],[2,3,4]]) (patternClique [[],[],[],[],[2,3,4]]) (patternEdges [[],[],[],[],[2,3,4]]) (patternAmount [[],[],[],[],[2,3,4]]) (patternEdgeCount [[],[],[],[],[2,3,4]]) [] := certificate_2303_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates073
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2304_checked : certificate_2304.Valid 17 8 16 certificate_2304_q certificate_2304_edges 8 3 [] := by decide +kernel
theorem certificate_2304_valid : certificate_2304.Valid 17 8 (patternOrder [[],[],[],[],[2,4,2]]) (patternClique [[],[],[],[],[2,4,2]]) (patternEdges [[],[],[],[],[2,4,2]]) (patternAmount [[],[],[],[],[2,4,2]]) (patternEdgeCount [[],[],[],[],[2,4,2]]) [] := certificate_2304_checked

theorem certificate_2305_checked : certificate_2305.Valid 17 8 17 certificate_2305_q certificate_2305_edges 9 3 [] := by decide +kernel
theorem certificate_2305_valid : certificate_2305.Valid 17 8 (patternOrder [[],[],[],[],[2,4,3]]) (patternClique [[],[],[],[],[2,4,3]]) (patternEdges [[],[],[],[],[2,4,3]]) (patternAmount [[],[],[],[],[2,4,3]]) (patternEdgeCount [[],[],[],[],[2,4,3]]) [] := certificate_2305_checked

theorem certificate_2306_checked : certificate_2306.Valid 17 8 17 certificate_2306_q certificate_2306_edges 9 3 [] := by decide +kernel
theorem certificate_2306_valid : certificate_2306.Valid 17 8 (patternOrder [[],[],[],[],[2,5,2]]) (patternClique [[],[],[],[],[2,5,2]]) (patternEdges [[],[],[],[],[2,5,2]]) (patternAmount [[],[],[],[],[2,5,2]]) (patternEdgeCount [[],[],[],[],[2,5,2]]) [] := certificate_2306_checked

theorem certificate_2307_checked : certificate_2307.Valid 17 8 14 certificate_2307_q certificate_2307_edges 6 2 [] := by decide +kernel
theorem certificate_2307_valid : certificate_2307.Valid 17 8 (patternOrder [[],[],[],[],[3],[3]]) (patternClique [[],[],[],[],[3],[3]]) (patternEdges [[],[],[],[],[3],[3]]) (patternAmount [[],[],[],[],[3],[3]]) (patternEdgeCount [[],[],[],[],[3],[3]]) [] := certificate_2307_checked

theorem certificate_2308_checked : certificate_2308.Valid 17 8 15 certificate_2308_q certificate_2308_edges 7 2 [] := by decide +kernel
theorem certificate_2308_valid : certificate_2308.Valid 17 8 (patternOrder [[],[],[],[],[3],[4]]) (patternClique [[],[],[],[],[3],[4]]) (patternEdges [[],[],[],[],[3],[4]]) (patternAmount [[],[],[],[],[3],[4]]) (patternEdgeCount [[],[],[],[],[3],[4]]) [] := certificate_2308_checked

theorem certificate_2309_checked : certificate_2309.Valid 17 8 16 certificate_2309_q certificate_2309_edges 8 2 [] := by decide +kernel
theorem certificate_2309_valid : certificate_2309.Valid 17 8 (patternOrder [[],[],[],[],[3],[5]]) (patternClique [[],[],[],[],[3],[5]]) (patternEdges [[],[],[],[],[3],[5]]) (patternAmount [[],[],[],[],[3],[5]]) (patternEdgeCount [[],[],[],[],[3],[5]]) [] := certificate_2309_checked

theorem certificate_2310_checked : certificate_2310.Valid 17 8 17 certificate_2310_q certificate_2310_edges 9 2 [] := by decide +kernel
theorem certificate_2310_valid : certificate_2310.Valid 17 8 (patternOrder [[],[],[],[],[3],[6]]) (patternClique [[],[],[],[],[3],[6]]) (patternEdges [[],[],[],[],[3],[6]]) (patternAmount [[],[],[],[],[3],[6]]) (patternEdgeCount [[],[],[],[],[3],[6]]) [] := certificate_2310_checked

theorem certificate_2311_checked : certificate_2311.Valid 17 8 15 certificate_2311_q certificate_2311_edges 7 3 [] := by decide +kernel
theorem certificate_2311_valid : certificate_2311.Valid 17 8 (patternOrder [[],[],[],[],[3,1,3]]) (patternClique [[],[],[],[],[3,1,3]]) (patternEdges [[],[],[],[],[3,1,3]]) (patternAmount [[],[],[],[],[3,1,3]]) (patternEdgeCount [[],[],[],[],[3,1,3]]) [] := certificate_2311_checked

theorem certificate_2312_checked : certificate_2312.Valid 17 8 16 certificate_2312_q certificate_2312_edges 8 3 [] := by decide +kernel
theorem certificate_2312_valid : certificate_2312.Valid 17 8 (patternOrder [[],[],[],[],[3,1,4]]) (patternClique [[],[],[],[],[3,1,4]]) (patternEdges [[],[],[],[],[3,1,4]]) (patternAmount [[],[],[],[],[3,1,4]]) (patternEdgeCount [[],[],[],[],[3,1,4]]) [] := certificate_2312_checked

theorem certificate_2313_checked : certificate_2313.Valid 17 8 17 certificate_2313_q certificate_2313_edges 9 3 [] := by decide +kernel
theorem certificate_2313_valid : certificate_2313.Valid 17 8 (patternOrder [[],[],[],[],[3,1,5]]) (patternClique [[],[],[],[],[3,1,5]]) (patternEdges [[],[],[],[],[3,1,5]]) (patternAmount [[],[],[],[],[3,1,5]]) (patternEdgeCount [[],[],[],[],[3,1,5]]) [] := certificate_2313_checked

theorem certificate_2314_checked : certificate_2314.Valid 17 8 16 certificate_2314_q certificate_2314_edges 8 3 [] := by decide +kernel
theorem certificate_2314_valid : certificate_2314.Valid 17 8 (patternOrder [[],[],[],[],[3,2,3]]) (patternClique [[],[],[],[],[3,2,3]]) (patternEdges [[],[],[],[],[3,2,3]]) (patternAmount [[],[],[],[],[3,2,3]]) (patternEdgeCount [[],[],[],[],[3,2,3]]) [] := certificate_2314_checked

theorem certificate_2315_checked : certificate_2315.Valid 17 8 17 certificate_2315_q certificate_2315_edges 9 3 [] := by decide +kernel
theorem certificate_2315_valid : certificate_2315.Valid 17 8 (patternOrder [[],[],[],[],[3,2,4]]) (patternClique [[],[],[],[],[3,2,4]]) (patternEdges [[],[],[],[],[3,2,4]]) (patternAmount [[],[],[],[],[3,2,4]]) (patternEdgeCount [[],[],[],[],[3,2,4]]) [] := certificate_2315_checked

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

theorem patterns_17_8_5_verified_oai : ∀ D ∈ patterns_17_8_5, PatternVerified 17 8 D := by

  simp only [patterns_17_8_5, List.forall_mem_cons]

  exact ⟨⟨certificate_2300, certificate_2300_valid⟩, ⟨⟨certificate_2301, certificate_2301_valid⟩, ⟨⟨certificate_2302, certificate_2302_valid⟩, ⟨⟨certificate_2303, certificate_2303_valid⟩, ⟨⟨certificate_2304, certificate_2304_valid⟩, ⟨⟨certificate_2305, certificate_2305_valid⟩, ⟨⟨certificate_2306, certificate_2306_valid⟩, ⟨⟨certificate_2307, certificate_2307_valid⟩, ⟨⟨certificate_2308, certificate_2308_valid⟩, ⟨⟨certificate_2309, certificate_2309_valid⟩, ⟨⟨certificate_2310, certificate_2310_valid⟩, ⟨⟨certificate_2311, certificate_2311_valid⟩, ⟨⟨certificate_2312, certificate_2312_valid⟩, ⟨⟨certificate_2313, certificate_2313_valid⟩, ⟨⟨certificate_2314, certificate_2314_valid⟩, ⟨⟨certificate_2315, certificate_2315_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_5_verified_oai := @OAI.CycleClique.patterns_17_8_5_verified_oai
