-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_7_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:03:50.751847+00:00
-- url     : https://prove2.me/submissions/bdf6c5c7-fad9-4645-abdb-1c9d2ab17085

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates073
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2332_checked : certificate_2332.Valid 17 8 15 certificate_2332_q certificate_2332_edges 7 3 [] := by decide +kernel
theorem certificate_2332_valid : certificate_2332.Valid 17 8 (patternOrder [[],[],[],[1],[3,3]]) (patternClique [[],[],[],[1],[3,3]]) (patternEdges [[],[],[],[1],[3,3]]) (patternAmount [[],[],[],[1],[3,3]]) (patternEdgeCount [[],[],[],[1],[3,3]]) [] := certificate_2332_checked

theorem certificate_2333_checked : certificate_2333.Valid 17 8 16 certificate_2333_q certificate_2333_edges 8 3 [] := by decide +kernel
theorem certificate_2333_valid : certificate_2333.Valid 17 8 (patternOrder [[],[],[],[1],[3,4]]) (patternClique [[],[],[],[1],[3,4]]) (patternEdges [[],[],[],[1],[3,4]]) (patternAmount [[],[],[],[1],[3,4]]) (patternEdgeCount [[],[],[],[1],[3,4]]) [] := certificate_2333_checked

theorem certificate_2334_checked : certificate_2334.Valid 17 8 17 certificate_2334_q certificate_2334_edges 9 3 [] := by decide +kernel
theorem certificate_2334_valid : certificate_2334.Valid 17 8 (patternOrder [[],[],[],[1],[3,5]]) (patternClique [[],[],[],[1],[3,5]]) (patternEdges [[],[],[],[1],[3,5]]) (patternAmount [[],[],[],[1],[3,5]]) (patternEdgeCount [[],[],[],[1],[3,5]]) [] := certificate_2334_checked

theorem certificate_2335_checked : certificate_2335.Valid 17 8 17 certificate_2335_q certificate_2335_edges 9 3 [] := by decide +kernel
theorem certificate_2335_valid : certificate_2335.Valid 17 8 (patternOrder [[],[],[],[1],[4,4]]) (patternClique [[],[],[],[1],[4,4]]) (patternEdges [[],[],[],[1],[4,4]]) (patternAmount [[],[],[],[1],[4,4]]) (patternEdgeCount [[],[],[],[1],[4,4]]) [] := certificate_2335_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates074
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2336_checked : certificate_2336.Valid 17 8 12 certificate_2336_q certificate_2336_edges 4 3 [] := by decide +kernel
theorem certificate_2336_valid : certificate_2336.Valid 17 8 (patternOrder [[],[],[],[1,1],[2]]) (patternClique [[],[],[],[1,1],[2]]) (patternEdges [[],[],[],[1,1],[2]]) (patternAmount [[],[],[],[1,1],[2]]) (patternEdgeCount [[],[],[],[1,1],[2]]) [] := certificate_2336_checked

theorem certificate_2337_checked : certificate_2337.Valid 17 8 13 certificate_2337_q certificate_2337_edges 5 3 [] := by decide +kernel
theorem certificate_2337_valid : certificate_2337.Valid 17 8 (patternOrder [[],[],[],[1,1],[3]]) (patternClique [[],[],[],[1,1],[3]]) (patternEdges [[],[],[],[1,1],[3]]) (patternAmount [[],[],[],[1,1],[3]]) (patternEdgeCount [[],[],[],[1,1],[3]]) [] := certificate_2337_checked

theorem certificate_2338_checked : certificate_2338.Valid 17 8 14 certificate_2338_q certificate_2338_edges 6 3 [] := by decide +kernel
theorem certificate_2338_valid : certificate_2338.Valid 17 8 (patternOrder [[],[],[],[1,1],[4]]) (patternClique [[],[],[],[1,1],[4]]) (patternEdges [[],[],[],[1,1],[4]]) (patternAmount [[],[],[],[1,1],[4]]) (patternEdgeCount [[],[],[],[1,1],[4]]) [] := certificate_2338_checked

theorem certificate_2339_checked : certificate_2339.Valid 17 8 15 certificate_2339_q certificate_2339_edges 7 3 [] := by decide +kernel
theorem certificate_2339_valid : certificate_2339.Valid 17 8 (patternOrder [[],[],[],[1,1],[5]]) (patternClique [[],[],[],[1,1],[5]]) (patternEdges [[],[],[],[1,1],[5]]) (patternAmount [[],[],[],[1,1],[5]]) (patternEdgeCount [[],[],[],[1,1],[5]]) [] := certificate_2339_checked

theorem certificate_2340_checked : certificate_2340.Valid 17 8 16 certificate_2340_q certificate_2340_edges 8 3 [] := by decide +kernel
theorem certificate_2340_valid : certificate_2340.Valid 17 8 (patternOrder [[],[],[],[1,1],[6]]) (patternClique [[],[],[],[1,1],[6]]) (patternEdges [[],[],[],[1,1],[6]]) (patternAmount [[],[],[],[1,1],[6]]) (patternEdgeCount [[],[],[],[1,1],[6]]) [] := certificate_2340_checked

theorem certificate_2341_checked : certificate_2341.Valid 17 8 17 certificate_2341_q certificate_2341_edges 9 3 [] := by decide +kernel
theorem certificate_2341_valid : certificate_2341.Valid 17 8 (patternOrder [[],[],[],[1,1],[7]]) (patternClique [[],[],[],[1,1],[7]]) (patternEdges [[],[],[],[1,1],[7]]) (patternAmount [[],[],[],[1,1],[7]]) (patternEdgeCount [[],[],[],[1,1],[7]]) [] := certificate_2341_checked

theorem certificate_2342_checked : certificate_2342.Valid 17 8 12 certificate_2342_q certificate_2342_edges 4 4 [] := by decide +kernel
theorem certificate_2342_valid : certificate_2342.Valid 17 8 (patternOrder [[],[],[],[1,1,1,1]]) (patternClique [[],[],[],[1,1,1,1]]) (patternEdges [[],[],[],[1,1,1,1]]) (patternAmount [[],[],[],[1,1,1,1]]) (patternEdgeCount [[],[],[],[1,1,1,1]]) [] := certificate_2342_checked

theorem certificate_2343_checked : certificate_2343.Valid 17 8 13 certificate_2343_q certificate_2343_edges 5 4 [] := by decide +kernel
theorem certificate_2343_valid : certificate_2343.Valid 17 8 (patternOrder [[],[],[],[1,1,1,2]]) (patternClique [[],[],[],[1,1,1,2]]) (patternEdges [[],[],[],[1,1,1,2]]) (patternAmount [[],[],[],[1,1,1,2]]) (patternEdgeCount [[],[],[],[1,1,1,2]]) [] := certificate_2343_checked

theorem certificate_2344_checked : certificate_2344.Valid 17 8 14 certificate_2344_q certificate_2344_edges 6 4 [] := by decide +kernel
theorem certificate_2344_valid : certificate_2344.Valid 17 8 (patternOrder [[],[],[],[1,1,1,3]]) (patternClique [[],[],[],[1,1,1,3]]) (patternEdges [[],[],[],[1,1,1,3]]) (patternAmount [[],[],[],[1,1,1,3]]) (patternEdgeCount [[],[],[],[1,1,1,3]]) [] := certificate_2344_checked

theorem certificate_2345_checked : certificate_2345.Valid 17 8 15 certificate_2345_q certificate_2345_edges 7 4 [] := by decide +kernel
theorem certificate_2345_valid : certificate_2345.Valid 17 8 (patternOrder [[],[],[],[1,1,1,4]]) (patternClique [[],[],[],[1,1,1,4]]) (patternEdges [[],[],[],[1,1,1,4]]) (patternAmount [[],[],[],[1,1,1,4]]) (patternEdgeCount [[],[],[],[1,1,1,4]]) [] := certificate_2345_checked

theorem certificate_2346_checked : certificate_2346.Valid 17 8 16 certificate_2346_q certificate_2346_edges 8 4 [] := by decide +kernel
theorem certificate_2346_valid : certificate_2346.Valid 17 8 (patternOrder [[],[],[],[1,1,1,5]]) (patternClique [[],[],[],[1,1,1,5]]) (patternEdges [[],[],[],[1,1,1,5]]) (patternAmount [[],[],[],[1,1,1,5]]) (patternEdgeCount [[],[],[],[1,1,1,5]]) [] := certificate_2346_checked

theorem certificate_2347_checked : certificate_2347.Valid 17 8 17 certificate_2347_q certificate_2347_edges 9 4 [] := by decide +kernel
theorem certificate_2347_valid : certificate_2347.Valid 17 8 (patternOrder [[],[],[],[1,1,1,6]]) (patternClique [[],[],[],[1,1,1,6]]) (patternEdges [[],[],[],[1,1,1,6]]) (patternAmount [[],[],[],[1,1,1,6]]) (patternEdgeCount [[],[],[],[1,1,1,6]]) [] := certificate_2347_checked

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

theorem patterns_17_8_7_verified_oai : ∀ D ∈ patterns_17_8_7, PatternVerified 17 8 D := by

  simp only [patterns_17_8_7, List.forall_mem_cons]

  exact ⟨⟨certificate_2332, certificate_2332_valid⟩, ⟨⟨certificate_2333, certificate_2333_valid⟩, ⟨⟨certificate_2334, certificate_2334_valid⟩, ⟨⟨certificate_2335, certificate_2335_valid⟩, ⟨⟨certificate_2336, certificate_2336_valid⟩, ⟨⟨certificate_2337, certificate_2337_valid⟩, ⟨⟨certificate_2338, certificate_2338_valid⟩, ⟨⟨certificate_2339, certificate_2339_valid⟩, ⟨⟨certificate_2340, certificate_2340_valid⟩, ⟨⟨certificate_2341, certificate_2341_valid⟩, ⟨⟨certificate_2342, certificate_2342_valid⟩, ⟨⟨certificate_2343, certificate_2343_valid⟩, ⟨⟨certificate_2344, certificate_2344_valid⟩, ⟨⟨certificate_2345, certificate_2345_valid⟩, ⟨⟨certificate_2346, certificate_2346_valid⟩, ⟨⟨certificate_2347, certificate_2347_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_7_verified_oai := @OAI.CycleClique.patterns_17_8_7_verified_oai
