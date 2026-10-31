-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_19_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:13:06.866497+00:00
-- url     : https://prove2.me/submissions/25c1eb0a-1e96-422e-8e00-da4eb0777994

import Mathlib
import Definitions.Def_OAIQ107D131
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

theorem certificate_2524_checked : certificate_2524.Valid 17 8 16 certificate_2524_q certificate_2524_edges 8 5 [] := by decide +kernel
theorem certificate_2524_valid : certificate_2524.Valid 17 8 (patternOrder [[],[],[1,1,2,1,3]]) (patternClique [[],[],[1,1,2,1,3]]) (patternEdges [[],[],[1,1,2,1,3]]) (patternAmount [[],[],[1,1,2,1,3]]) (patternEdgeCount [[],[],[1,1,2,1,3]]) [] := certificate_2524_checked

theorem certificate_2525_checked : certificate_2525.Valid 17 8 17 certificate_2525_q certificate_2525_edges 9 5 [] := by decide +kernel
theorem certificate_2525_valid : certificate_2525.Valid 17 8 (patternOrder [[],[],[1,1,2,1,4]]) (patternClique [[],[],[1,1,2,1,4]]) (patternEdges [[],[],[1,1,2,1,4]]) (patternAmount [[],[],[1,1,2,1,4]]) (patternEdgeCount [[],[],[1,1,2,1,4]]) [] := certificate_2525_checked

theorem certificate_2526_checked : certificate_2526.Valid 17 8 15 certificate_2526_q certificate_2526_edges 7 5 [] := by decide +kernel
theorem certificate_2526_valid : certificate_2526.Valid 17 8 (patternOrder [[],[],[1,1,2,2,1]]) (patternClique [[],[],[1,1,2,2,1]]) (patternEdges [[],[],[1,1,2,2,1]]) (patternAmount [[],[],[1,1,2,2,1]]) (patternEdgeCount [[],[],[1,1,2,2,1]]) [] := certificate_2526_checked

theorem certificate_2527_checked : certificate_2527.Valid 17 8 16 certificate_2527_q certificate_2527_edges 8 5 [] := by decide +kernel
theorem certificate_2527_valid : certificate_2527.Valid 17 8 (patternOrder [[],[],[1,1,2,2,2]]) (patternClique [[],[],[1,1,2,2,2]]) (patternEdges [[],[],[1,1,2,2,2]]) (patternAmount [[],[],[1,1,2,2,2]]) (patternEdgeCount [[],[],[1,1,2,2,2]]) [] := certificate_2527_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates080
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2528_checked : certificate_2528.Valid 17 8 17 certificate_2528_q certificate_2528_edges 9 5 [] := by decide +kernel
theorem certificate_2528_valid : certificate_2528.Valid 17 8 (patternOrder [[],[],[1,1,2,2,3]]) (patternClique [[],[],[1,1,2,2,3]]) (patternEdges [[],[],[1,1,2,2,3]]) (patternAmount [[],[],[1,1,2,2,3]]) (patternEdgeCount [[],[],[1,1,2,2,3]]) [] := certificate_2528_checked

theorem certificate_2529_checked : certificate_2529.Valid 17 8 16 certificate_2529_q certificate_2529_edges 8 5 [] := by decide +kernel
theorem certificate_2529_valid : certificate_2529.Valid 17 8 (patternOrder [[],[],[1,1,2,3,1]]) (patternClique [[],[],[1,1,2,3,1]]) (patternEdges [[],[],[1,1,2,3,1]]) (patternAmount [[],[],[1,1,2,3,1]]) (patternEdgeCount [[],[],[1,1,2,3,1]]) [] := certificate_2529_checked

theorem certificate_2530_checked : certificate_2530.Valid 17 8 17 certificate_2530_q certificate_2530_edges 9 5 [] := by decide +kernel
theorem certificate_2530_valid : certificate_2530.Valid 17 8 (patternOrder [[],[],[1,1,2,3,2]]) (patternClique [[],[],[1,1,2,3,2]]) (patternEdges [[],[],[1,1,2,3,2]]) (patternAmount [[],[],[1,1,2,3,2]]) (patternEdgeCount [[],[],[1,1,2,3,2]]) [] := certificate_2530_checked

theorem certificate_2531_checked : certificate_2531.Valid 17 8 17 certificate_2531_q certificate_2531_edges 9 5 [] := by decide +kernel
theorem certificate_2531_valid : certificate_2531.Valid 17 8 (patternOrder [[],[],[1,1,2,4,1]]) (patternClique [[],[],[1,1,2,4,1]]) (patternEdges [[],[],[1,1,2,4,1]]) (patternAmount [[],[],[1,1,2,4,1]]) (patternEdgeCount [[],[],[1,1,2,4,1]]) [] := certificate_2531_checked

theorem certificate_2532_checked : certificate_2532.Valid 17 8 15 certificate_2532_q certificate_2532_edges 7 4 [] := by decide +kernel
theorem certificate_2532_valid : certificate_2532.Valid 17 8 (patternOrder [[],[],[1,1,3],[2]]) (patternClique [[],[],[1,1,3],[2]]) (patternEdges [[],[],[1,1,3],[2]]) (patternAmount [[],[],[1,1,3],[2]]) (patternEdgeCount [[],[],[1,1,3],[2]]) [] := certificate_2532_checked

theorem certificate_2533_checked : certificate_2533.Valid 17 8 16 certificate_2533_q certificate_2533_edges 8 4 [] := by decide +kernel
theorem certificate_2533_valid : certificate_2533.Valid 17 8 (patternOrder [[],[],[1,1,3],[3]]) (patternClique [[],[],[1,1,3],[3]]) (patternEdges [[],[],[1,1,3],[3]]) (patternAmount [[],[],[1,1,3],[3]]) (patternEdgeCount [[],[],[1,1,3],[3]]) [] := certificate_2533_checked

theorem certificate_2534_checked : certificate_2534.Valid 17 8 17 certificate_2534_q certificate_2534_edges 9 4 [] := by decide +kernel
theorem certificate_2534_valid : certificate_2534.Valid 17 8 (patternOrder [[],[],[1,1,3],[4]]) (patternClique [[],[],[1,1,3],[4]]) (patternEdges [[],[],[1,1,3],[4]]) (patternAmount [[],[],[1,1,3],[4]]) (patternEdgeCount [[],[],[1,1,3],[4]]) [] := certificate_2534_checked

theorem certificate_2535_checked : certificate_2535.Valid 17 8 15 certificate_2535_q certificate_2535_edges 7 5 [] := by decide +kernel
theorem certificate_2535_valid : certificate_2535.Valid 17 8 (patternOrder [[],[],[1,1,3,1,1]]) (patternClique [[],[],[1,1,3,1,1]]) (patternEdges [[],[],[1,1,3,1,1]]) (patternAmount [[],[],[1,1,3,1,1]]) (patternEdgeCount [[],[],[1,1,3,1,1]]) [] := certificate_2535_checked

theorem certificate_2536_checked : certificate_2536.Valid 17 8 16 certificate_2536_q certificate_2536_edges 8 5 [] := by decide +kernel
theorem certificate_2536_valid : certificate_2536.Valid 17 8 (patternOrder [[],[],[1,1,3,1,2]]) (patternClique [[],[],[1,1,3,1,2]]) (patternEdges [[],[],[1,1,3,1,2]]) (patternAmount [[],[],[1,1,3,1,2]]) (patternEdgeCount [[],[],[1,1,3,1,2]]) [] := certificate_2536_checked

theorem certificate_2537_checked : certificate_2537.Valid 17 8 17 certificate_2537_q certificate_2537_edges 9 5 [] := by decide +kernel
theorem certificate_2537_valid : certificate_2537.Valid 17 8 (patternOrder [[],[],[1,1,3,1,3]]) (patternClique [[],[],[1,1,3,1,3]]) (patternEdges [[],[],[1,1,3,1,3]]) (patternAmount [[],[],[1,1,3,1,3]]) (patternEdgeCount [[],[],[1,1,3,1,3]]) [] := certificate_2537_checked

theorem certificate_2538_checked : certificate_2538.Valid 17 8 16 certificate_2538_q certificate_2538_edges 8 5 [] := by decide +kernel
theorem certificate_2538_valid : certificate_2538.Valid 17 8 (patternOrder [[],[],[1,1,3,2,1]]) (patternClique [[],[],[1,1,3,2,1]]) (patternEdges [[],[],[1,1,3,2,1]]) (patternAmount [[],[],[1,1,3,2,1]]) (patternEdgeCount [[],[],[1,1,3,2,1]]) [] := certificate_2538_checked

theorem certificate_2539_checked : certificate_2539.Valid 17 8 17 certificate_2539_q certificate_2539_edges 9 5 [] := by decide +kernel
theorem certificate_2539_valid : certificate_2539.Valid 17 8 (patternOrder [[],[],[1,1,3,2,2]]) (patternClique [[],[],[1,1,3,2,2]]) (patternEdges [[],[],[1,1,3,2,2]]) (patternAmount [[],[],[1,1,3,2,2]]) (patternEdgeCount [[],[],[1,1,3,2,2]]) [] := certificate_2539_checked

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

theorem patterns_17_8_19_verified_oai : ∀ D ∈ patterns_17_8_19, PatternVerified 17 8 D := by

  simp only [patterns_17_8_19, List.forall_mem_cons]

  exact ⟨⟨certificate_2524, certificate_2524_valid⟩, ⟨⟨certificate_2525, certificate_2525_valid⟩, ⟨⟨certificate_2526, certificate_2526_valid⟩, ⟨⟨certificate_2527, certificate_2527_valid⟩, ⟨⟨certificate_2528, certificate_2528_valid⟩, ⟨⟨certificate_2529, certificate_2529_valid⟩, ⟨⟨certificate_2530, certificate_2530_valid⟩, ⟨⟨certificate_2531, certificate_2531_valid⟩, ⟨⟨certificate_2532, certificate_2532_valid⟩, ⟨⟨certificate_2533, certificate_2533_valid⟩, ⟨⟨certificate_2534, certificate_2534_valid⟩, ⟨⟨certificate_2535, certificate_2535_valid⟩, ⟨⟨certificate_2536, certificate_2536_valid⟩, ⟨⟨certificate_2537, certificate_2537_valid⟩, ⟨⟨certificate_2538, certificate_2538_valid⟩, ⟨⟨certificate_2539, certificate_2539_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_19_verified_oai := @OAI.CycleClique.patterns_17_8_19_verified_oai
