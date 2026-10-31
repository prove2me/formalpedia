-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_11_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:01:45.672456+00:00
-- url     : https://prove2.me/submissions/4f5c3cd0-3474-476c-8ca4-22665a3758ba

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates075
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2396_checked : certificate_2396.Valid 17 8 17 certificate_2396_q certificate_2396_edges 9 3 [] := by decide +kernel
theorem certificate_2396_valid : certificate_2396.Valid 17 8 (patternOrder [[],[],[],[1,4],[4]]) (patternClique [[],[],[],[1,4],[4]]) (patternEdges [[],[],[],[1,4],[4]]) (patternAmount [[],[],[],[1,4],[4]]) (patternEdgeCount [[],[],[],[1,4],[4]]) [] := certificate_2396_checked

theorem certificate_2397_checked : certificate_2397.Valid 17 8 16 certificate_2397_q certificate_2397_edges 8 4 [] := by decide +kernel
theorem certificate_2397_valid : certificate_2397.Valid 17 8 (patternOrder [[],[],[],[1,4,1,2]]) (patternClique [[],[],[],[1,4,1,2]]) (patternEdges [[],[],[],[1,4,1,2]]) (patternAmount [[],[],[],[1,4,1,2]]) (patternEdgeCount [[],[],[],[1,4,1,2]]) [] := certificate_2397_checked

theorem certificate_2398_checked : certificate_2398.Valid 17 8 17 certificate_2398_q certificate_2398_edges 9 4 [] := by decide +kernel
theorem certificate_2398_valid : certificate_2398.Valid 17 8 (patternOrder [[],[],[],[1,4,1,3]]) (patternClique [[],[],[],[1,4,1,3]]) (patternEdges [[],[],[],[1,4,1,3]]) (patternAmount [[],[],[],[1,4,1,3]]) (patternEdgeCount [[],[],[],[1,4,1,3]]) [] := certificate_2398_checked

theorem certificate_2399_checked : certificate_2399.Valid 17 8 17 certificate_2399_q certificate_2399_edges 9 4 [] := by decide +kernel
theorem certificate_2399_valid : certificate_2399.Valid 17 8 (patternOrder [[],[],[],[1,4,2,2]]) (patternClique [[],[],[],[1,4,2,2]]) (patternEdges [[],[],[],[1,4,2,2]]) (patternAmount [[],[],[],[1,4,2,2]]) (patternEdgeCount [[],[],[],[1,4,2,2]]) [] := certificate_2399_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates076
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2400_checked : certificate_2400.Valid 17 8 16 certificate_2400_q certificate_2400_edges 8 3 [] := by decide +kernel
theorem certificate_2400_valid : certificate_2400.Valid 17 8 (patternOrder [[],[],[],[1,5],[2]]) (patternClique [[],[],[],[1,5],[2]]) (patternEdges [[],[],[],[1,5],[2]]) (patternAmount [[],[],[],[1,5],[2]]) (patternEdgeCount [[],[],[],[1,5],[2]]) [] := certificate_2400_checked

theorem certificate_2401_checked : certificate_2401.Valid 17 8 17 certificate_2401_q certificate_2401_edges 9 3 [] := by decide +kernel
theorem certificate_2401_valid : certificate_2401.Valid 17 8 (patternOrder [[],[],[],[1,5],[3]]) (patternClique [[],[],[],[1,5],[3]]) (patternEdges [[],[],[],[1,5],[3]]) (patternAmount [[],[],[],[1,5],[3]]) (patternEdgeCount [[],[],[],[1,5],[3]]) [] := certificate_2401_checked

theorem certificate_2402_checked : certificate_2402.Valid 17 8 17 certificate_2402_q certificate_2402_edges 9 4 [] := by decide +kernel
theorem certificate_2402_valid : certificate_2402.Valid 17 8 (patternOrder [[],[],[],[1,5,1,2]]) (patternClique [[],[],[],[1,5,1,2]]) (patternEdges [[],[],[],[1,5,1,2]]) (patternAmount [[],[],[],[1,5,1,2]]) (patternEdgeCount [[],[],[],[1,5,1,2]]) [] := certificate_2402_checked

theorem certificate_2403_checked : certificate_2403.Valid 17 8 17 certificate_2403_q certificate_2403_edges 9 3 [] := by decide +kernel
theorem certificate_2403_valid : certificate_2403.Valid 17 8 (patternOrder [[],[],[],[1,6],[2]]) (patternClique [[],[],[],[1,6],[2]]) (patternEdges [[],[],[],[1,6],[2]]) (patternAmount [[],[],[],[1,6],[2]]) (patternEdgeCount [[],[],[],[1,6],[2]]) [] := certificate_2403_checked

theorem certificate_2404_checked : certificate_2404.Valid 17 8 14 certificate_2404_q certificate_2404_edges 6 3 [] := by decide +kernel
theorem certificate_2404_valid : certificate_2404.Valid 17 8 (patternOrder [[],[],[],[2],[2,2]]) (patternClique [[],[],[],[2],[2,2]]) (patternEdges [[],[],[],[2],[2,2]]) (patternAmount [[],[],[],[2],[2,2]]) (patternEdgeCount [[],[],[],[2],[2,2]]) [] := certificate_2404_checked

theorem certificate_2405_checked : certificate_2405.Valid 17 8 15 certificate_2405_q certificate_2405_edges 7 3 [] := by decide +kernel
theorem certificate_2405_valid : certificate_2405.Valid 17 8 (patternOrder [[],[],[],[2],[2,3]]) (patternClique [[],[],[],[2],[2,3]]) (patternEdges [[],[],[],[2],[2,3]]) (patternAmount [[],[],[],[2],[2,3]]) (patternEdgeCount [[],[],[],[2],[2,3]]) [] := certificate_2405_checked

theorem certificate_2406_checked : certificate_2406.Valid 17 8 16 certificate_2406_q certificate_2406_edges 8 3 [] := by decide +kernel
theorem certificate_2406_valid : certificate_2406.Valid 17 8 (patternOrder [[],[],[],[2],[2,4]]) (patternClique [[],[],[],[2],[2,4]]) (patternEdges [[],[],[],[2],[2,4]]) (patternAmount [[],[],[],[2],[2,4]]) (patternEdgeCount [[],[],[],[2],[2,4]]) [] := certificate_2406_checked

theorem certificate_2407_checked : certificate_2407.Valid 17 8 17 certificate_2407_q certificate_2407_edges 9 3 [] := by decide +kernel
theorem certificate_2407_valid : certificate_2407.Valid 17 8 (patternOrder [[],[],[],[2],[2,5]]) (patternClique [[],[],[],[2],[2,5]]) (patternEdges [[],[],[],[2],[2,5]]) (patternAmount [[],[],[],[2],[2,5]]) (patternEdgeCount [[],[],[],[2],[2,5]]) [] := certificate_2407_checked

theorem certificate_2408_checked : certificate_2408.Valid 17 8 16 certificate_2408_q certificate_2408_edges 8 3 [] := by decide +kernel
theorem certificate_2408_valid : certificate_2408.Valid 17 8 (patternOrder [[],[],[],[2],[3,3]]) (patternClique [[],[],[],[2],[3,3]]) (patternEdges [[],[],[],[2],[3,3]]) (patternAmount [[],[],[],[2],[3,3]]) (patternEdgeCount [[],[],[],[2],[3,3]]) [] := certificate_2408_checked

theorem certificate_2409_checked : certificate_2409.Valid 17 8 17 certificate_2409_q certificate_2409_edges 9 3 [] := by decide +kernel
theorem certificate_2409_valid : certificate_2409.Valid 17 8 (patternOrder [[],[],[],[2],[3,4]]) (patternClique [[],[],[],[2],[3,4]]) (patternEdges [[],[],[],[2],[3,4]]) (patternAmount [[],[],[],[2],[3,4]]) (patternEdgeCount [[],[],[],[2],[3,4]]) [] := certificate_2409_checked

theorem certificate_2410_checked : certificate_2410.Valid 17 8 14 certificate_2410_q certificate_2410_edges 6 4 [] := by decide +kernel
theorem certificate_2410_valid : certificate_2410.Valid 17 8 (patternOrder [[],[],[],[2,1,1,2]]) (patternClique [[],[],[],[2,1,1,2]]) (patternEdges [[],[],[],[2,1,1,2]]) (patternAmount [[],[],[],[2,1,1,2]]) (patternEdgeCount [[],[],[],[2,1,1,2]]) [] := certificate_2410_checked

theorem certificate_2411_checked : certificate_2411.Valid 17 8 15 certificate_2411_q certificate_2411_edges 7 4 [] := by decide +kernel
theorem certificate_2411_valid : certificate_2411.Valid 17 8 (patternOrder [[],[],[],[2,1,1,3]]) (patternClique [[],[],[],[2,1,1,3]]) (patternEdges [[],[],[],[2,1,1,3]]) (patternAmount [[],[],[],[2,1,1,3]]) (patternEdgeCount [[],[],[],[2,1,1,3]]) [] := certificate_2411_checked

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

theorem patterns_17_8_11_verified_oai : ∀ D ∈ patterns_17_8_11, PatternVerified 17 8 D := by

  simp only [patterns_17_8_11, List.forall_mem_cons]

  exact ⟨⟨certificate_2396, certificate_2396_valid⟩, ⟨⟨certificate_2397, certificate_2397_valid⟩, ⟨⟨certificate_2398, certificate_2398_valid⟩, ⟨⟨certificate_2399, certificate_2399_valid⟩, ⟨⟨certificate_2400, certificate_2400_valid⟩, ⟨⟨certificate_2401, certificate_2401_valid⟩, ⟨⟨certificate_2402, certificate_2402_valid⟩, ⟨⟨certificate_2403, certificate_2403_valid⟩, ⟨⟨certificate_2404, certificate_2404_valid⟩, ⟨⟨certificate_2405, certificate_2405_valid⟩, ⟨⟨certificate_2406, certificate_2406_valid⟩, ⟨⟨certificate_2407, certificate_2407_valid⟩, ⟨⟨certificate_2408, certificate_2408_valid⟩, ⟨⟨certificate_2409, certificate_2409_valid⟩, ⟨⟨certificate_2410, certificate_2410_valid⟩, ⟨⟨certificate_2411, certificate_2411_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_11_verified_oai := @OAI.CycleClique.patterns_17_8_11_verified_oai
