-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_12_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:01:46.79539+00:00
-- url     : https://prove2.me/submissions/d5253795-ab5c-47ad-99f5-66ab42f11b52

import Mathlib
import Definitions.Def_OAIQ107D131
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

theorem certificate_2412_checked : certificate_2412.Valid 17 8 16 certificate_2412_q certificate_2412_edges 8 4 [] := by decide +kernel
theorem certificate_2412_valid : certificate_2412.Valid 17 8 (patternOrder [[],[],[],[2,1,1,4]]) (patternClique [[],[],[],[2,1,1,4]]) (patternEdges [[],[],[],[2,1,1,4]]) (patternAmount [[],[],[],[2,1,1,4]]) (patternEdgeCount [[],[],[],[2,1,1,4]]) [] := certificate_2412_checked

theorem certificate_2413_checked : certificate_2413.Valid 17 8 17 certificate_2413_q certificate_2413_edges 9 4 [] := by decide +kernel
theorem certificate_2413_valid : certificate_2413.Valid 17 8 (patternOrder [[],[],[],[2,1,1,5]]) (patternClique [[],[],[],[2,1,1,5]]) (patternEdges [[],[],[],[2,1,1,5]]) (patternAmount [[],[],[],[2,1,1,5]]) (patternEdgeCount [[],[],[],[2,1,1,5]]) [] := certificate_2413_checked

theorem certificate_2414_checked : certificate_2414.Valid 17 8 15 certificate_2414_q certificate_2414_edges 7 4 [] := by decide +kernel
theorem certificate_2414_valid : certificate_2414.Valid 17 8 (patternOrder [[],[],[],[2,1,2,2]]) (patternClique [[],[],[],[2,1,2,2]]) (patternEdges [[],[],[],[2,1,2,2]]) (patternAmount [[],[],[],[2,1,2,2]]) (patternEdgeCount [[],[],[],[2,1,2,2]]) [] := certificate_2414_checked

theorem certificate_2415_checked : certificate_2415.Valid 17 8 16 certificate_2415_q certificate_2415_edges 8 4 [] := by decide +kernel
theorem certificate_2415_valid : certificate_2415.Valid 17 8 (patternOrder [[],[],[],[2,1,2,3]]) (patternClique [[],[],[],[2,1,2,3]]) (patternEdges [[],[],[],[2,1,2,3]]) (patternAmount [[],[],[],[2,1,2,3]]) (patternEdgeCount [[],[],[],[2,1,2,3]]) [] := certificate_2415_checked

theorem certificate_2416_checked : certificate_2416.Valid 17 8 17 certificate_2416_q certificate_2416_edges 9 4 [] := by decide +kernel
theorem certificate_2416_valid : certificate_2416.Valid 17 8 (patternOrder [[],[],[],[2,1,2,4]]) (patternClique [[],[],[],[2,1,2,4]]) (patternEdges [[],[],[],[2,1,2,4]]) (patternAmount [[],[],[],[2,1,2,4]]) (patternEdgeCount [[],[],[],[2,1,2,4]]) [] := certificate_2416_checked

theorem certificate_2417_checked : certificate_2417.Valid 17 8 16 certificate_2417_q certificate_2417_edges 8 4 [] := by decide +kernel
theorem certificate_2417_valid : certificate_2417.Valid 17 8 (patternOrder [[],[],[],[2,1,3,2]]) (patternClique [[],[],[],[2,1,3,2]]) (patternEdges [[],[],[],[2,1,3,2]]) (patternAmount [[],[],[],[2,1,3,2]]) (patternEdgeCount [[],[],[],[2,1,3,2]]) [] := certificate_2417_checked

theorem certificate_2418_checked : certificate_2418.Valid 17 8 17 certificate_2418_q certificate_2418_edges 9 4 [] := by decide +kernel
theorem certificate_2418_valid : certificate_2418.Valid 17 8 (patternOrder [[],[],[],[2,1,3,3]]) (patternClique [[],[],[],[2,1,3,3]]) (patternEdges [[],[],[],[2,1,3,3]]) (patternAmount [[],[],[],[2,1,3,3]]) (patternEdgeCount [[],[],[],[2,1,3,3]]) [] := certificate_2418_checked

theorem certificate_2419_checked : certificate_2419.Valid 17 8 17 certificate_2419_q certificate_2419_edges 9 4 [] := by decide +kernel
theorem certificate_2419_valid : certificate_2419.Valid 17 8 (patternOrder [[],[],[],[2,1,4,2]]) (patternClique [[],[],[],[2,1,4,2]]) (patternEdges [[],[],[],[2,1,4,2]]) (patternAmount [[],[],[],[2,1,4,2]]) (patternEdgeCount [[],[],[],[2,1,4,2]]) [] := certificate_2419_checked

theorem certificate_2420_checked : certificate_2420.Valid 17 8 15 certificate_2420_q certificate_2420_edges 7 3 [] := by decide +kernel
theorem certificate_2420_valid : certificate_2420.Valid 17 8 (patternOrder [[],[],[],[2,2],[3]]) (patternClique [[],[],[],[2,2],[3]]) (patternEdges [[],[],[],[2,2],[3]]) (patternAmount [[],[],[],[2,2],[3]]) (patternEdgeCount [[],[],[],[2,2],[3]]) [] := certificate_2420_checked

theorem certificate_2421_checked : certificate_2421.Valid 17 8 16 certificate_2421_q certificate_2421_edges 8 3 [] := by decide +kernel
theorem certificate_2421_valid : certificate_2421.Valid 17 8 (patternOrder [[],[],[],[2,2],[4]]) (patternClique [[],[],[],[2,2],[4]]) (patternEdges [[],[],[],[2,2],[4]]) (patternAmount [[],[],[],[2,2],[4]]) (patternEdgeCount [[],[],[],[2,2],[4]]) [] := certificate_2421_checked

theorem certificate_2422_checked : certificate_2422.Valid 17 8 17 certificate_2422_q certificate_2422_edges 9 3 [] := by decide +kernel
theorem certificate_2422_valid : certificate_2422.Valid 17 8 (patternOrder [[],[],[],[2,2],[5]]) (patternClique [[],[],[],[2,2],[5]]) (patternEdges [[],[],[],[2,2],[5]]) (patternAmount [[],[],[],[2,2],[5]]) (patternEdgeCount [[],[],[],[2,2],[5]]) [] := certificate_2422_checked

theorem certificate_2423_checked : certificate_2423.Valid 17 8 16 certificate_2423_q certificate_2423_edges 8 4 [] := by decide +kernel
theorem certificate_2423_valid : certificate_2423.Valid 17 8 (patternOrder [[],[],[],[2,2,1,3]]) (patternClique [[],[],[],[2,2,1,3]]) (patternEdges [[],[],[],[2,2,1,3]]) (patternAmount [[],[],[],[2,2,1,3]]) (patternEdgeCount [[],[],[],[2,2,1,3]]) [] := certificate_2423_checked

theorem certificate_2424_checked : certificate_2424.Valid 17 8 17 certificate_2424_q certificate_2424_edges 9 4 [] := by decide +kernel
theorem certificate_2424_valid : certificate_2424.Valid 17 8 (patternOrder [[],[],[],[2,2,1,4]]) (patternClique [[],[],[],[2,2,1,4]]) (patternEdges [[],[],[],[2,2,1,4]]) (patternAmount [[],[],[],[2,2,1,4]]) (patternEdgeCount [[],[],[],[2,2,1,4]]) [] := certificate_2424_checked

theorem certificate_2425_checked : certificate_2425.Valid 17 8 16 certificate_2425_q certificate_2425_edges 8 4 [] := by decide +kernel
theorem certificate_2425_valid : certificate_2425.Valid 17 8 (patternOrder [[],[],[],[2,2,2,2]]) (patternClique [[],[],[],[2,2,2,2]]) (patternEdges [[],[],[],[2,2,2,2]]) (patternAmount [[],[],[],[2,2,2,2]]) (patternEdgeCount [[],[],[],[2,2,2,2]]) [] := certificate_2425_checked

theorem certificate_2426_checked : certificate_2426.Valid 17 8 17 certificate_2426_q certificate_2426_edges 9 4 [] := by decide +kernel
theorem certificate_2426_valid : certificate_2426.Valid 17 8 (patternOrder [[],[],[],[2,2,2,3]]) (patternClique [[],[],[],[2,2,2,3]]) (patternEdges [[],[],[],[2,2,2,3]]) (patternAmount [[],[],[],[2,2,2,3]]) (patternEdgeCount [[],[],[],[2,2,2,3]]) [] := certificate_2426_checked

theorem certificate_2427_checked : certificate_2427.Valid 17 8 17 certificate_2427_q certificate_2427_edges 9 4 [] := by decide +kernel
theorem certificate_2427_valid : certificate_2427.Valid 17 8 (patternOrder [[],[],[],[2,2,3,2]]) (patternClique [[],[],[],[2,2,3,2]]) (patternEdges [[],[],[],[2,2,3,2]]) (patternAmount [[],[],[],[2,2,3,2]]) (patternEdgeCount [[],[],[],[2,2,3,2]]) [] := certificate_2427_checked

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

theorem patterns_17_8_12_verified_oai : ∀ D ∈ patterns_17_8_12, PatternVerified 17 8 D := by

  simp only [patterns_17_8_12, List.forall_mem_cons]

  exact ⟨⟨certificate_2412, certificate_2412_valid⟩, ⟨⟨certificate_2413, certificate_2413_valid⟩, ⟨⟨certificate_2414, certificate_2414_valid⟩, ⟨⟨certificate_2415, certificate_2415_valid⟩, ⟨⟨certificate_2416, certificate_2416_valid⟩, ⟨⟨certificate_2417, certificate_2417_valid⟩, ⟨⟨certificate_2418, certificate_2418_valid⟩, ⟨⟨certificate_2419, certificate_2419_valid⟩, ⟨⟨certificate_2420, certificate_2420_valid⟩, ⟨⟨certificate_2421, certificate_2421_valid⟩, ⟨⟨certificate_2422, certificate_2422_valid⟩, ⟨⟨certificate_2423, certificate_2423_valid⟩, ⟨⟨certificate_2424, certificate_2424_valid⟩, ⟨⟨certificate_2425, certificate_2425_valid⟩, ⟨⟨certificate_2426, certificate_2426_valid⟩, ⟨⟨certificate_2427, certificate_2427_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_12_verified_oai := @OAI.CycleClique.patterns_17_8_12_verified_oai
