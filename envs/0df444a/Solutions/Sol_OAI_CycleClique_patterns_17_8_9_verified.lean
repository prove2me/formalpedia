-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_9_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:06:47.364222+00:00
-- url     : https://prove2.me/submissions/01649496-71e4-4b29-a65f-b6588ace8447

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates074
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2364_checked : certificate_2364.Valid 17 8 14 certificate_2364_q certificate_2364_edges 6 3 [] := by decide +kernel
theorem certificate_2364_valid : certificate_2364.Valid 17 8 (patternOrder [[],[],[],[1,2],[3]]) (patternClique [[],[],[],[1,2],[3]]) (patternEdges [[],[],[],[1,2],[3]]) (patternAmount [[],[],[],[1,2],[3]]) (patternEdgeCount [[],[],[],[1,2],[3]]) [] := certificate_2364_checked

theorem certificate_2365_checked : certificate_2365.Valid 17 8 15 certificate_2365_q certificate_2365_edges 7 3 [] := by decide +kernel
theorem certificate_2365_valid : certificate_2365.Valid 17 8 (patternOrder [[],[],[],[1,2],[4]]) (patternClique [[],[],[],[1,2],[4]]) (patternEdges [[],[],[],[1,2],[4]]) (patternAmount [[],[],[],[1,2],[4]]) (patternEdgeCount [[],[],[],[1,2],[4]]) [] := certificate_2365_checked

theorem certificate_2366_checked : certificate_2366.Valid 17 8 16 certificate_2366_q certificate_2366_edges 8 3 [] := by decide +kernel
theorem certificate_2366_valid : certificate_2366.Valid 17 8 (patternOrder [[],[],[],[1,2],[5]]) (patternClique [[],[],[],[1,2],[5]]) (patternEdges [[],[],[],[1,2],[5]]) (patternAmount [[],[],[],[1,2],[5]]) (patternEdgeCount [[],[],[],[1,2],[5]]) [] := certificate_2366_checked

theorem certificate_2367_checked : certificate_2367.Valid 17 8 17 certificate_2367_q certificate_2367_edges 9 3 [] := by decide +kernel
theorem certificate_2367_valid : certificate_2367.Valid 17 8 (patternOrder [[],[],[],[1,2],[6]]) (patternClique [[],[],[],[1,2],[6]]) (patternEdges [[],[],[],[1,2],[6]]) (patternAmount [[],[],[],[1,2],[6]]) (patternEdgeCount [[],[],[],[1,2],[6]]) [] := certificate_2367_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates075
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2368_checked : certificate_2368.Valid 17 8 14 certificate_2368_q certificate_2368_edges 6 4 [] := by decide +kernel
theorem certificate_2368_valid : certificate_2368.Valid 17 8 (patternOrder [[],[],[],[1,2,1,2]]) (patternClique [[],[],[],[1,2,1,2]]) (patternEdges [[],[],[],[1,2,1,2]]) (patternAmount [[],[],[],[1,2,1,2]]) (patternEdgeCount [[],[],[],[1,2,1,2]]) [] := certificate_2368_checked

theorem certificate_2369_checked : certificate_2369.Valid 17 8 15 certificate_2369_q certificate_2369_edges 7 4 [] := by decide +kernel
theorem certificate_2369_valid : certificate_2369.Valid 17 8 (patternOrder [[],[],[],[1,2,1,3]]) (patternClique [[],[],[],[1,2,1,3]]) (patternEdges [[],[],[],[1,2,1,3]]) (patternAmount [[],[],[],[1,2,1,3]]) (patternEdgeCount [[],[],[],[1,2,1,3]]) [] := certificate_2369_checked

theorem certificate_2370_checked : certificate_2370.Valid 17 8 16 certificate_2370_q certificate_2370_edges 8 4 [] := by decide +kernel
theorem certificate_2370_valid : certificate_2370.Valid 17 8 (patternOrder [[],[],[],[1,2,1,4]]) (patternClique [[],[],[],[1,2,1,4]]) (patternEdges [[],[],[],[1,2,1,4]]) (patternAmount [[],[],[],[1,2,1,4]]) (patternEdgeCount [[],[],[],[1,2,1,4]]) [] := certificate_2370_checked

theorem certificate_2371_checked : certificate_2371.Valid 17 8 17 certificate_2371_q certificate_2371_edges 9 4 [] := by decide +kernel
theorem certificate_2371_valid : certificate_2371.Valid 17 8 (patternOrder [[],[],[],[1,2,1,5]]) (patternClique [[],[],[],[1,2,1,5]]) (patternEdges [[],[],[],[1,2,1,5]]) (patternAmount [[],[],[],[1,2,1,5]]) (patternEdgeCount [[],[],[],[1,2,1,5]]) [] := certificate_2371_checked

theorem certificate_2372_checked : certificate_2372.Valid 17 8 14 certificate_2372_q certificate_2372_edges 6 4 [] := by decide +kernel
theorem certificate_2372_valid : certificate_2372.Valid 17 8 (patternOrder [[],[],[],[1,2,2,1]]) (patternClique [[],[],[],[1,2,2,1]]) (patternEdges [[],[],[],[1,2,2,1]]) (patternAmount [[],[],[],[1,2,2,1]]) (patternEdgeCount [[],[],[],[1,2,2,1]]) [] := certificate_2372_checked

theorem certificate_2373_checked : certificate_2373.Valid 17 8 15 certificate_2373_q certificate_2373_edges 7 4 [] := by decide +kernel
theorem certificate_2373_valid : certificate_2373.Valid 17 8 (patternOrder [[],[],[],[1,2,2,2]]) (patternClique [[],[],[],[1,2,2,2]]) (patternEdges [[],[],[],[1,2,2,2]]) (patternAmount [[],[],[],[1,2,2,2]]) (patternEdgeCount [[],[],[],[1,2,2,2]]) [] := certificate_2373_checked

theorem certificate_2374_checked : certificate_2374.Valid 17 8 16 certificate_2374_q certificate_2374_edges 8 4 [] := by decide +kernel
theorem certificate_2374_valid : certificate_2374.Valid 17 8 (patternOrder [[],[],[],[1,2,2,3]]) (patternClique [[],[],[],[1,2,2,3]]) (patternEdges [[],[],[],[1,2,2,3]]) (patternAmount [[],[],[],[1,2,2,3]]) (patternEdgeCount [[],[],[],[1,2,2,3]]) [] := certificate_2374_checked

theorem certificate_2375_checked : certificate_2375.Valid 17 8 17 certificate_2375_q certificate_2375_edges 9 4 [] := by decide +kernel
theorem certificate_2375_valid : certificate_2375.Valid 17 8 (patternOrder [[],[],[],[1,2,2,4]]) (patternClique [[],[],[],[1,2,2,4]]) (patternEdges [[],[],[],[1,2,2,4]]) (patternAmount [[],[],[],[1,2,2,4]]) (patternEdgeCount [[],[],[],[1,2,2,4]]) [] := certificate_2375_checked

theorem certificate_2376_checked : certificate_2376.Valid 17 8 15 certificate_2376_q certificate_2376_edges 7 4 [] := by decide +kernel
theorem certificate_2376_valid : certificate_2376.Valid 17 8 (patternOrder [[],[],[],[1,2,3,1]]) (patternClique [[],[],[],[1,2,3,1]]) (patternEdges [[],[],[],[1,2,3,1]]) (patternAmount [[],[],[],[1,2,3,1]]) (patternEdgeCount [[],[],[],[1,2,3,1]]) [] := certificate_2376_checked

theorem certificate_2377_checked : certificate_2377.Valid 17 8 16 certificate_2377_q certificate_2377_edges 8 4 [] := by decide +kernel
theorem certificate_2377_valid : certificate_2377.Valid 17 8 (patternOrder [[],[],[],[1,2,3,2]]) (patternClique [[],[],[],[1,2,3,2]]) (patternEdges [[],[],[],[1,2,3,2]]) (patternAmount [[],[],[],[1,2,3,2]]) (patternEdgeCount [[],[],[],[1,2,3,2]]) [] := certificate_2377_checked

theorem certificate_2378_checked : certificate_2378.Valid 17 8 17 certificate_2378_q certificate_2378_edges 9 4 [] := by decide +kernel
theorem certificate_2378_valid : certificate_2378.Valid 17 8 (patternOrder [[],[],[],[1,2,3,3]]) (patternClique [[],[],[],[1,2,3,3]]) (patternEdges [[],[],[],[1,2,3,3]]) (patternAmount [[],[],[],[1,2,3,3]]) (patternEdgeCount [[],[],[],[1,2,3,3]]) [] := certificate_2378_checked

theorem certificate_2379_checked : certificate_2379.Valid 17 8 16 certificate_2379_q certificate_2379_edges 8 4 [] := by decide +kernel
theorem certificate_2379_valid : certificate_2379.Valid 17 8 (patternOrder [[],[],[],[1,2,4,1]]) (patternClique [[],[],[],[1,2,4,1]]) (patternEdges [[],[],[],[1,2,4,1]]) (patternAmount [[],[],[],[1,2,4,1]]) (patternEdgeCount [[],[],[],[1,2,4,1]]) [] := certificate_2379_checked

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

theorem patterns_17_8_9_verified_oai : ∀ D ∈ patterns_17_8_9, PatternVerified 17 8 D := by

  simp only [patterns_17_8_9, List.forall_mem_cons]

  exact ⟨⟨certificate_2364, certificate_2364_valid⟩, ⟨⟨certificate_2365, certificate_2365_valid⟩, ⟨⟨certificate_2366, certificate_2366_valid⟩, ⟨⟨certificate_2367, certificate_2367_valid⟩, ⟨⟨certificate_2368, certificate_2368_valid⟩, ⟨⟨certificate_2369, certificate_2369_valid⟩, ⟨⟨certificate_2370, certificate_2370_valid⟩, ⟨⟨certificate_2371, certificate_2371_valid⟩, ⟨⟨certificate_2372, certificate_2372_valid⟩, ⟨⟨certificate_2373, certificate_2373_valid⟩, ⟨⟨certificate_2374, certificate_2374_valid⟩, ⟨⟨certificate_2375, certificate_2375_valid⟩, ⟨⟨certificate_2376, certificate_2376_valid⟩, ⟨⟨certificate_2377, certificate_2377_valid⟩, ⟨⟨certificate_2378, certificate_2378_valid⟩, ⟨⟨certificate_2379, certificate_2379_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_9_verified_oai := @OAI.CycleClique.patterns_17_8_9_verified_oai
