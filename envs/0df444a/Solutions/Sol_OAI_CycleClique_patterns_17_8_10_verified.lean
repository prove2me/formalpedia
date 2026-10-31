-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_10_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:59:55.961426+00:00
-- url     : https://prove2.me/submissions/cbc65a49-8d75-4938-95ac-49051ee79c97

import Mathlib
import Definitions.Def_OAIQ107D077
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

theorem certificate_2380_checked : certificate_2380.Valid 17 8 17 certificate_2380_q certificate_2380_edges 9 4 [] := by decide +kernel
theorem certificate_2380_valid : certificate_2380.Valid 17 8 (patternOrder [[],[],[],[1,2,4,2]]) (patternClique [[],[],[],[1,2,4,2]]) (patternEdges [[],[],[],[1,2,4,2]]) (patternAmount [[],[],[],[1,2,4,2]]) (patternEdgeCount [[],[],[],[1,2,4,2]]) [] := certificate_2380_checked

theorem certificate_2381_checked : certificate_2381.Valid 17 8 17 certificate_2381_q certificate_2381_edges 9 4 [] := by decide +kernel
theorem certificate_2381_valid : certificate_2381.Valid 17 8 (patternOrder [[],[],[],[1,2,5,1]]) (patternClique [[],[],[],[1,2,5,1]]) (patternEdges [[],[],[],[1,2,5,1]]) (patternAmount [[],[],[],[1,2,5,1]]) (patternEdgeCount [[],[],[],[1,2,5,1]]) [] := certificate_2381_checked

theorem certificate_2382_checked : certificate_2382.Valid 17 8 14 certificate_2382_q certificate_2382_edges 6 3 [] := by decide +kernel
theorem certificate_2382_valid : certificate_2382.Valid 17 8 (patternOrder [[],[],[],[1,3],[2]]) (patternClique [[],[],[],[1,3],[2]]) (patternEdges [[],[],[],[1,3],[2]]) (patternAmount [[],[],[],[1,3],[2]]) (patternEdgeCount [[],[],[],[1,3],[2]]) [] := certificate_2382_checked

theorem certificate_2383_checked : certificate_2383.Valid 17 8 15 certificate_2383_q certificate_2383_edges 7 3 [] := by decide +kernel
theorem certificate_2383_valid : certificate_2383.Valid 17 8 (patternOrder [[],[],[],[1,3],[3]]) (patternClique [[],[],[],[1,3],[3]]) (patternEdges [[],[],[],[1,3],[3]]) (patternAmount [[],[],[],[1,3],[3]]) (patternEdgeCount [[],[],[],[1,3],[3]]) [] := certificate_2383_checked

theorem certificate_2384_checked : certificate_2384.Valid 17 8 16 certificate_2384_q certificate_2384_edges 8 3 [] := by decide +kernel
theorem certificate_2384_valid : certificate_2384.Valid 17 8 (patternOrder [[],[],[],[1,3],[4]]) (patternClique [[],[],[],[1,3],[4]]) (patternEdges [[],[],[],[1,3],[4]]) (patternAmount [[],[],[],[1,3],[4]]) (patternEdgeCount [[],[],[],[1,3],[4]]) [] := certificate_2384_checked

theorem certificate_2385_checked : certificate_2385.Valid 17 8 17 certificate_2385_q certificate_2385_edges 9 3 [] := by decide +kernel
theorem certificate_2385_valid : certificate_2385.Valid 17 8 (patternOrder [[],[],[],[1,3],[5]]) (patternClique [[],[],[],[1,3],[5]]) (patternEdges [[],[],[],[1,3],[5]]) (patternAmount [[],[],[],[1,3],[5]]) (patternEdgeCount [[],[],[],[1,3],[5]]) [] := certificate_2385_checked

theorem certificate_2386_checked : certificate_2386.Valid 17 8 15 certificate_2386_q certificate_2386_edges 7 4 [] := by decide +kernel
theorem certificate_2386_valid : certificate_2386.Valid 17 8 (patternOrder [[],[],[],[1,3,1,2]]) (patternClique [[],[],[],[1,3,1,2]]) (patternEdges [[],[],[],[1,3,1,2]]) (patternAmount [[],[],[],[1,3,1,2]]) (patternEdgeCount [[],[],[],[1,3,1,2]]) [] := certificate_2386_checked

theorem certificate_2387_checked : certificate_2387.Valid 17 8 16 certificate_2387_q certificate_2387_edges 8 4 [] := by decide +kernel
theorem certificate_2387_valid : certificate_2387.Valid 17 8 (patternOrder [[],[],[],[1,3,1,3]]) (patternClique [[],[],[],[1,3,1,3]]) (patternEdges [[],[],[],[1,3,1,3]]) (patternAmount [[],[],[],[1,3,1,3]]) (patternEdgeCount [[],[],[],[1,3,1,3]]) [] := certificate_2387_checked

theorem certificate_2388_checked : certificate_2388.Valid 17 8 17 certificate_2388_q certificate_2388_edges 9 4 [] := by decide +kernel
theorem certificate_2388_valid : certificate_2388.Valid 17 8 (patternOrder [[],[],[],[1,3,1,4]]) (patternClique [[],[],[],[1,3,1,4]]) (patternEdges [[],[],[],[1,3,1,4]]) (patternAmount [[],[],[],[1,3,1,4]]) (patternEdgeCount [[],[],[],[1,3,1,4]]) [] := certificate_2388_checked

theorem certificate_2389_checked : certificate_2389.Valid 17 8 16 certificate_2389_q certificate_2389_edges 8 4 [] := by decide +kernel
theorem certificate_2389_valid : certificate_2389.Valid 17 8 (patternOrder [[],[],[],[1,3,2,2]]) (patternClique [[],[],[],[1,3,2,2]]) (patternEdges [[],[],[],[1,3,2,2]]) (patternAmount [[],[],[],[1,3,2,2]]) (patternEdgeCount [[],[],[],[1,3,2,2]]) [] := certificate_2389_checked

theorem certificate_2390_checked : certificate_2390.Valid 17 8 17 certificate_2390_q certificate_2390_edges 9 4 [] := by decide +kernel
theorem certificate_2390_valid : certificate_2390.Valid 17 8 (patternOrder [[],[],[],[1,3,2,3]]) (patternClique [[],[],[],[1,3,2,3]]) (patternEdges [[],[],[],[1,3,2,3]]) (patternAmount [[],[],[],[1,3,2,3]]) (patternEdgeCount [[],[],[],[1,3,2,3]]) [] := certificate_2390_checked

theorem certificate_2391_checked : certificate_2391.Valid 17 8 16 certificate_2391_q certificate_2391_edges 8 4 [] := by decide +kernel
theorem certificate_2391_valid : certificate_2391.Valid 17 8 (patternOrder [[],[],[],[1,3,3,1]]) (patternClique [[],[],[],[1,3,3,1]]) (patternEdges [[],[],[],[1,3,3,1]]) (patternAmount [[],[],[],[1,3,3,1]]) (patternEdgeCount [[],[],[],[1,3,3,1]]) [] := certificate_2391_checked

theorem certificate_2392_checked : certificate_2392.Valid 17 8 17 certificate_2392_q certificate_2392_edges 9 4 [] := by decide +kernel
theorem certificate_2392_valid : certificate_2392.Valid 17 8 (patternOrder [[],[],[],[1,3,3,2]]) (patternClique [[],[],[],[1,3,3,2]]) (patternEdges [[],[],[],[1,3,3,2]]) (patternAmount [[],[],[],[1,3,3,2]]) (patternEdgeCount [[],[],[],[1,3,3,2]]) [] := certificate_2392_checked

theorem certificate_2393_checked : certificate_2393.Valid 17 8 17 certificate_2393_q certificate_2393_edges 9 4 [] := by decide +kernel
theorem certificate_2393_valid : certificate_2393.Valid 17 8 (patternOrder [[],[],[],[1,3,4,1]]) (patternClique [[],[],[],[1,3,4,1]]) (patternEdges [[],[],[],[1,3,4,1]]) (patternAmount [[],[],[],[1,3,4,1]]) (patternEdgeCount [[],[],[],[1,3,4,1]]) [] := certificate_2393_checked

theorem certificate_2394_checked : certificate_2394.Valid 17 8 15 certificate_2394_q certificate_2394_edges 7 3 [] := by decide +kernel
theorem certificate_2394_valid : certificate_2394.Valid 17 8 (patternOrder [[],[],[],[1,4],[2]]) (patternClique [[],[],[],[1,4],[2]]) (patternEdges [[],[],[],[1,4],[2]]) (patternAmount [[],[],[],[1,4],[2]]) (patternEdgeCount [[],[],[],[1,4],[2]]) [] := certificate_2394_checked

theorem certificate_2395_checked : certificate_2395.Valid 17 8 16 certificate_2395_q certificate_2395_edges 8 3 [] := by decide +kernel
theorem certificate_2395_valid : certificate_2395.Valid 17 8 (patternOrder [[],[],[],[1,4],[3]]) (patternClique [[],[],[],[1,4],[3]]) (patternEdges [[],[],[],[1,4],[3]]) (patternAmount [[],[],[],[1,4],[3]]) (patternEdgeCount [[],[],[],[1,4],[3]]) [] := certificate_2395_checked

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

theorem patterns_17_8_10_verified_oai : ∀ D ∈ patterns_17_8_10, PatternVerified 17 8 D := by

  simp only [patterns_17_8_10, List.forall_mem_cons]

  exact ⟨⟨certificate_2380, certificate_2380_valid⟩, ⟨⟨certificate_2381, certificate_2381_valid⟩, ⟨⟨certificate_2382, certificate_2382_valid⟩, ⟨⟨certificate_2383, certificate_2383_valid⟩, ⟨⟨certificate_2384, certificate_2384_valid⟩, ⟨⟨certificate_2385, certificate_2385_valid⟩, ⟨⟨certificate_2386, certificate_2386_valid⟩, ⟨⟨certificate_2387, certificate_2387_valid⟩, ⟨⟨certificate_2388, certificate_2388_valid⟩, ⟨⟨certificate_2389, certificate_2389_valid⟩, ⟨⟨certificate_2390, certificate_2390_valid⟩, ⟨⟨certificate_2391, certificate_2391_valid⟩, ⟨⟨certificate_2392, certificate_2392_valid⟩, ⟨⟨certificate_2393, certificate_2393_valid⟩, ⟨⟨certificate_2394, certificate_2394_valid⟩, ⟨⟨certificate_2395, certificate_2395_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_10_verified_oai := @OAI.CycleClique.patterns_17_8_10_verified_oai
