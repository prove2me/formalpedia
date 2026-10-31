-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_14_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:11:39.172651+00:00
-- url     : https://prove2.me/submissions/104ee9f1-0649-48f4-ad98-57966ce4abc5

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates077
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2444_checked : certificate_2444.Valid 17 8 13 certificate_2444_q certificate_2444_edges 5 4 [] := by decide +kernel
theorem certificate_2444_valid : certificate_2444.Valid 17 8 (patternOrder [[],[],[1],[1,1,2]]) (patternClique [[],[],[1],[1,1,2]]) (patternEdges [[],[],[1],[1,1,2]]) (patternAmount [[],[],[1],[1,1,2]]) (patternEdgeCount [[],[],[1],[1,1,2]]) [] := certificate_2444_checked

theorem certificate_2445_checked : certificate_2445.Valid 17 8 14 certificate_2445_q certificate_2445_edges 6 4 [] := by decide +kernel
theorem certificate_2445_valid : certificate_2445.Valid 17 8 (patternOrder [[],[],[1],[1,1,3]]) (patternClique [[],[],[1],[1,1,3]]) (patternEdges [[],[],[1],[1,1,3]]) (patternAmount [[],[],[1],[1,1,3]]) (patternEdgeCount [[],[],[1],[1,1,3]]) [] := certificate_2445_checked

theorem certificate_2446_checked : certificate_2446.Valid 17 8 15 certificate_2446_q certificate_2446_edges 7 4 [] := by decide +kernel
theorem certificate_2446_valid : certificate_2446.Valid 17 8 (patternOrder [[],[],[1],[1,1,4]]) (patternClique [[],[],[1],[1,1,4]]) (patternEdges [[],[],[1],[1,1,4]]) (patternAmount [[],[],[1],[1,1,4]]) (patternEdgeCount [[],[],[1],[1,1,4]]) [] := certificate_2446_checked

theorem certificate_2447_checked : certificate_2447.Valid 17 8 16 certificate_2447_q certificate_2447_edges 8 4 [] := by decide +kernel
theorem certificate_2447_valid : certificate_2447.Valid 17 8 (patternOrder [[],[],[1],[1,1,5]]) (patternClique [[],[],[1],[1,1,5]]) (patternEdges [[],[],[1],[1,1,5]]) (patternAmount [[],[],[1],[1,1,5]]) (patternEdgeCount [[],[],[1],[1,1,5]]) [] := certificate_2447_checked

theorem certificate_2448_checked : certificate_2448.Valid 17 8 17 certificate_2448_q certificate_2448_edges 9 4 [] := by decide +kernel
theorem certificate_2448_valid : certificate_2448.Valid 17 8 (patternOrder [[],[],[1],[1,1,6]]) (patternClique [[],[],[1],[1,1,6]]) (patternEdges [[],[],[1],[1,1,6]]) (patternAmount [[],[],[1],[1,1,6]]) (patternEdgeCount [[],[],[1],[1,1,6]]) [] := certificate_2448_checked

theorem certificate_2449_checked : certificate_2449.Valid 17 8 13 certificate_2449_q certificate_2449_edges 5 4 [] := by decide +kernel
theorem certificate_2449_valid : certificate_2449.Valid 17 8 (patternOrder [[],[],[1],[1,2,1]]) (patternClique [[],[],[1],[1,2,1]]) (patternEdges [[],[],[1],[1,2,1]]) (patternAmount [[],[],[1],[1,2,1]]) (patternEdgeCount [[],[],[1],[1,2,1]]) [] := certificate_2449_checked

theorem certificate_2450_checked : certificate_2450.Valid 17 8 14 certificate_2450_q certificate_2450_edges 6 4 [] := by decide +kernel
theorem certificate_2450_valid : certificate_2450.Valid 17 8 (patternOrder [[],[],[1],[1,2,2]]) (patternClique [[],[],[1],[1,2,2]]) (patternEdges [[],[],[1],[1,2,2]]) (patternAmount [[],[],[1],[1,2,2]]) (patternEdgeCount [[],[],[1],[1,2,2]]) [] := certificate_2450_checked

theorem certificate_2451_checked : certificate_2451.Valid 17 8 15 certificate_2451_q certificate_2451_edges 7 4 [] := by decide +kernel
theorem certificate_2451_valid : certificate_2451.Valid 17 8 (patternOrder [[],[],[1],[1,2,3]]) (patternClique [[],[],[1],[1,2,3]]) (patternEdges [[],[],[1],[1,2,3]]) (patternAmount [[],[],[1],[1,2,3]]) (patternEdgeCount [[],[],[1],[1,2,3]]) [] := certificate_2451_checked

theorem certificate_2452_checked : certificate_2452.Valid 17 8 16 certificate_2452_q certificate_2452_edges 8 4 [] := by decide +kernel
theorem certificate_2452_valid : certificate_2452.Valid 17 8 (patternOrder [[],[],[1],[1,2,4]]) (patternClique [[],[],[1],[1,2,4]]) (patternEdges [[],[],[1],[1,2,4]]) (patternAmount [[],[],[1],[1,2,4]]) (patternEdgeCount [[],[],[1],[1,2,4]]) [] := certificate_2452_checked

theorem certificate_2453_checked : certificate_2453.Valid 17 8 17 certificate_2453_q certificate_2453_edges 9 4 [] := by decide +kernel
theorem certificate_2453_valid : certificate_2453.Valid 17 8 (patternOrder [[],[],[1],[1,2,5]]) (patternClique [[],[],[1],[1,2,5]]) (patternEdges [[],[],[1],[1,2,5]]) (patternAmount [[],[],[1],[1,2,5]]) (patternEdgeCount [[],[],[1],[1,2,5]]) [] := certificate_2453_checked

theorem certificate_2454_checked : certificate_2454.Valid 17 8 14 certificate_2454_q certificate_2454_edges 6 4 [] := by decide +kernel
theorem certificate_2454_valid : certificate_2454.Valid 17 8 (patternOrder [[],[],[1],[1,3,1]]) (patternClique [[],[],[1],[1,3,1]]) (patternEdges [[],[],[1],[1,3,1]]) (patternAmount [[],[],[1],[1,3,1]]) (patternEdgeCount [[],[],[1],[1,3,1]]) [] := certificate_2454_checked

theorem certificate_2455_checked : certificate_2455.Valid 17 8 15 certificate_2455_q certificate_2455_edges 7 4 [] := by decide +kernel
theorem certificate_2455_valid : certificate_2455.Valid 17 8 (patternOrder [[],[],[1],[1,3,2]]) (patternClique [[],[],[1],[1,3,2]]) (patternEdges [[],[],[1],[1,3,2]]) (patternAmount [[],[],[1],[1,3,2]]) (patternEdgeCount [[],[],[1],[1,3,2]]) [] := certificate_2455_checked

theorem certificate_2456_checked : certificate_2456.Valid 17 8 16 certificate_2456_q certificate_2456_edges 8 4 [] := by decide +kernel
theorem certificate_2456_valid : certificate_2456.Valid 17 8 (patternOrder [[],[],[1],[1,3,3]]) (patternClique [[],[],[1],[1,3,3]]) (patternEdges [[],[],[1],[1,3,3]]) (patternAmount [[],[],[1],[1,3,3]]) (patternEdgeCount [[],[],[1],[1,3,3]]) [] := certificate_2456_checked

theorem certificate_2457_checked : certificate_2457.Valid 17 8 17 certificate_2457_q certificate_2457_edges 9 4 [] := by decide +kernel
theorem certificate_2457_valid : certificate_2457.Valid 17 8 (patternOrder [[],[],[1],[1,3,4]]) (patternClique [[],[],[1],[1,3,4]]) (patternEdges [[],[],[1],[1,3,4]]) (patternAmount [[],[],[1],[1,3,4]]) (patternEdgeCount [[],[],[1],[1,3,4]]) [] := certificate_2457_checked

theorem certificate_2458_checked : certificate_2458.Valid 17 8 15 certificate_2458_q certificate_2458_edges 7 4 [] := by decide +kernel
theorem certificate_2458_valid : certificate_2458.Valid 17 8 (patternOrder [[],[],[1],[1,4,1]]) (patternClique [[],[],[1],[1,4,1]]) (patternEdges [[],[],[1],[1,4,1]]) (patternAmount [[],[],[1],[1,4,1]]) (patternEdgeCount [[],[],[1],[1,4,1]]) [] := certificate_2458_checked

theorem certificate_2459_checked : certificate_2459.Valid 17 8 16 certificate_2459_q certificate_2459_edges 8 4 [] := by decide +kernel
theorem certificate_2459_valid : certificate_2459.Valid 17 8 (patternOrder [[],[],[1],[1,4,2]]) (patternClique [[],[],[1],[1,4,2]]) (patternEdges [[],[],[1],[1,4,2]]) (patternAmount [[],[],[1],[1,4,2]]) (patternEdgeCount [[],[],[1],[1,4,2]]) [] := certificate_2459_checked

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

theorem patterns_17_8_14_verified_oai : ∀ D ∈ patterns_17_8_14, PatternVerified 17 8 D := by

  simp only [patterns_17_8_14, List.forall_mem_cons]

  exact ⟨⟨certificate_2444, certificate_2444_valid⟩, ⟨⟨certificate_2445, certificate_2445_valid⟩, ⟨⟨certificate_2446, certificate_2446_valid⟩, ⟨⟨certificate_2447, certificate_2447_valid⟩, ⟨⟨certificate_2448, certificate_2448_valid⟩, ⟨⟨certificate_2449, certificate_2449_valid⟩, ⟨⟨certificate_2450, certificate_2450_valid⟩, ⟨⟨certificate_2451, certificate_2451_valid⟩, ⟨⟨certificate_2452, certificate_2452_valid⟩, ⟨⟨certificate_2453, certificate_2453_valid⟩, ⟨⟨certificate_2454, certificate_2454_valid⟩, ⟨⟨certificate_2455, certificate_2455_valid⟩, ⟨⟨certificate_2456, certificate_2456_valid⟩, ⟨⟨certificate_2457, certificate_2457_valid⟩, ⟨⟨certificate_2458, certificate_2458_valid⟩, ⟨⟨certificate_2459, certificate_2459_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_14_verified_oai := @OAI.CycleClique.patterns_17_8_14_verified_oai
