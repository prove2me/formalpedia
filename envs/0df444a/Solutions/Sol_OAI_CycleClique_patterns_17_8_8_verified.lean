-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_8_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:06:02.074975+00:00
-- url     : https://prove2.me/submissions/bbdab15a-ab3e-4c64-baa0-97b88877acd1

import Mathlib
import Definitions.Def_OAIQ107D076
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

theorem certificate_2348_checked : certificate_2348.Valid 17 8 13 certificate_2348_q certificate_2348_edges 5 4 [] := by decide +kernel
theorem certificate_2348_valid : certificate_2348.Valid 17 8 (patternOrder [[],[],[],[1,1,2,1]]) (patternClique [[],[],[],[1,1,2,1]]) (patternEdges [[],[],[],[1,1,2,1]]) (patternAmount [[],[],[],[1,1,2,1]]) (patternEdgeCount [[],[],[],[1,1,2,1]]) [] := certificate_2348_checked

theorem certificate_2349_checked : certificate_2349.Valid 17 8 14 certificate_2349_q certificate_2349_edges 6 4 [] := by decide +kernel
theorem certificate_2349_valid : certificate_2349.Valid 17 8 (patternOrder [[],[],[],[1,1,2,2]]) (patternClique [[],[],[],[1,1,2,2]]) (patternEdges [[],[],[],[1,1,2,2]]) (patternAmount [[],[],[],[1,1,2,2]]) (patternEdgeCount [[],[],[],[1,1,2,2]]) [] := certificate_2349_checked

theorem certificate_2350_checked : certificate_2350.Valid 17 8 15 certificate_2350_q certificate_2350_edges 7 4 [] := by decide +kernel
theorem certificate_2350_valid : certificate_2350.Valid 17 8 (patternOrder [[],[],[],[1,1,2,3]]) (patternClique [[],[],[],[1,1,2,3]]) (patternEdges [[],[],[],[1,1,2,3]]) (patternAmount [[],[],[],[1,1,2,3]]) (patternEdgeCount [[],[],[],[1,1,2,3]]) [] := certificate_2350_checked

theorem certificate_2351_checked : certificate_2351.Valid 17 8 16 certificate_2351_q certificate_2351_edges 8 4 [] := by decide +kernel
theorem certificate_2351_valid : certificate_2351.Valid 17 8 (patternOrder [[],[],[],[1,1,2,4]]) (patternClique [[],[],[],[1,1,2,4]]) (patternEdges [[],[],[],[1,1,2,4]]) (patternAmount [[],[],[],[1,1,2,4]]) (patternEdgeCount [[],[],[],[1,1,2,4]]) [] := certificate_2351_checked

theorem certificate_2352_checked : certificate_2352.Valid 17 8 17 certificate_2352_q certificate_2352_edges 9 4 [] := by decide +kernel
theorem certificate_2352_valid : certificate_2352.Valid 17 8 (patternOrder [[],[],[],[1,1,2,5]]) (patternClique [[],[],[],[1,1,2,5]]) (patternEdges [[],[],[],[1,1,2,5]]) (patternAmount [[],[],[],[1,1,2,5]]) (patternEdgeCount [[],[],[],[1,1,2,5]]) [] := certificate_2352_checked

theorem certificate_2353_checked : certificate_2353.Valid 17 8 14 certificate_2353_q certificate_2353_edges 6 4 [] := by decide +kernel
theorem certificate_2353_valid : certificate_2353.Valid 17 8 (patternOrder [[],[],[],[1,1,3,1]]) (patternClique [[],[],[],[1,1,3,1]]) (patternEdges [[],[],[],[1,1,3,1]]) (patternAmount [[],[],[],[1,1,3,1]]) (patternEdgeCount [[],[],[],[1,1,3,1]]) [] := certificate_2353_checked

theorem certificate_2354_checked : certificate_2354.Valid 17 8 15 certificate_2354_q certificate_2354_edges 7 4 [] := by decide +kernel
theorem certificate_2354_valid : certificate_2354.Valid 17 8 (patternOrder [[],[],[],[1,1,3,2]]) (patternClique [[],[],[],[1,1,3,2]]) (patternEdges [[],[],[],[1,1,3,2]]) (patternAmount [[],[],[],[1,1,3,2]]) (patternEdgeCount [[],[],[],[1,1,3,2]]) [] := certificate_2354_checked

theorem certificate_2355_checked : certificate_2355.Valid 17 8 16 certificate_2355_q certificate_2355_edges 8 4 [] := by decide +kernel
theorem certificate_2355_valid : certificate_2355.Valid 17 8 (patternOrder [[],[],[],[1,1,3,3]]) (patternClique [[],[],[],[1,1,3,3]]) (patternEdges [[],[],[],[1,1,3,3]]) (patternAmount [[],[],[],[1,1,3,3]]) (patternEdgeCount [[],[],[],[1,1,3,3]]) [] := certificate_2355_checked

theorem certificate_2356_checked : certificate_2356.Valid 17 8 17 certificate_2356_q certificate_2356_edges 9 4 [] := by decide +kernel
theorem certificate_2356_valid : certificate_2356.Valid 17 8 (patternOrder [[],[],[],[1,1,3,4]]) (patternClique [[],[],[],[1,1,3,4]]) (patternEdges [[],[],[],[1,1,3,4]]) (patternAmount [[],[],[],[1,1,3,4]]) (patternEdgeCount [[],[],[],[1,1,3,4]]) [] := certificate_2356_checked

theorem certificate_2357_checked : certificate_2357.Valid 17 8 15 certificate_2357_q certificate_2357_edges 7 4 [] := by decide +kernel
theorem certificate_2357_valid : certificate_2357.Valid 17 8 (patternOrder [[],[],[],[1,1,4,1]]) (patternClique [[],[],[],[1,1,4,1]]) (patternEdges [[],[],[],[1,1,4,1]]) (patternAmount [[],[],[],[1,1,4,1]]) (patternEdgeCount [[],[],[],[1,1,4,1]]) [] := certificate_2357_checked

theorem certificate_2358_checked : certificate_2358.Valid 17 8 16 certificate_2358_q certificate_2358_edges 8 4 [] := by decide +kernel
theorem certificate_2358_valid : certificate_2358.Valid 17 8 (patternOrder [[],[],[],[1,1,4,2]]) (patternClique [[],[],[],[1,1,4,2]]) (patternEdges [[],[],[],[1,1,4,2]]) (patternAmount [[],[],[],[1,1,4,2]]) (patternEdgeCount [[],[],[],[1,1,4,2]]) [] := certificate_2358_checked

theorem certificate_2359_checked : certificate_2359.Valid 17 8 17 certificate_2359_q certificate_2359_edges 9 4 [] := by decide +kernel
theorem certificate_2359_valid : certificate_2359.Valid 17 8 (patternOrder [[],[],[],[1,1,4,3]]) (patternClique [[],[],[],[1,1,4,3]]) (patternEdges [[],[],[],[1,1,4,3]]) (patternAmount [[],[],[],[1,1,4,3]]) (patternEdgeCount [[],[],[],[1,1,4,3]]) [] := certificate_2359_checked

theorem certificate_2360_checked : certificate_2360.Valid 17 8 16 certificate_2360_q certificate_2360_edges 8 4 [] := by decide +kernel
theorem certificate_2360_valid : certificate_2360.Valid 17 8 (patternOrder [[],[],[],[1,1,5,1]]) (patternClique [[],[],[],[1,1,5,1]]) (patternEdges [[],[],[],[1,1,5,1]]) (patternAmount [[],[],[],[1,1,5,1]]) (patternEdgeCount [[],[],[],[1,1,5,1]]) [] := certificate_2360_checked

theorem certificate_2361_checked : certificate_2361.Valid 17 8 17 certificate_2361_q certificate_2361_edges 9 4 [] := by decide +kernel
theorem certificate_2361_valid : certificate_2361.Valid 17 8 (patternOrder [[],[],[],[1,1,5,2]]) (patternClique [[],[],[],[1,1,5,2]]) (patternEdges [[],[],[],[1,1,5,2]]) (patternAmount [[],[],[],[1,1,5,2]]) (patternEdgeCount [[],[],[],[1,1,5,2]]) [] := certificate_2361_checked

theorem certificate_2362_checked : certificate_2362.Valid 17 8 17 certificate_2362_q certificate_2362_edges 9 4 [] := by decide +kernel
theorem certificate_2362_valid : certificate_2362.Valid 17 8 (patternOrder [[],[],[],[1,1,6,1]]) (patternClique [[],[],[],[1,1,6,1]]) (patternEdges [[],[],[],[1,1,6,1]]) (patternAmount [[],[],[],[1,1,6,1]]) (patternEdgeCount [[],[],[],[1,1,6,1]]) [] := certificate_2362_checked

theorem certificate_2363_checked : certificate_2363.Valid 17 8 13 certificate_2363_q certificate_2363_edges 5 3 [] := by decide +kernel
theorem certificate_2363_valid : certificate_2363.Valid 17 8 (patternOrder [[],[],[],[1,2],[2]]) (patternClique [[],[],[],[1,2],[2]]) (patternEdges [[],[],[],[1,2],[2]]) (patternAmount [[],[],[],[1,2],[2]]) (patternEdgeCount [[],[],[],[1,2],[2]]) [] := certificate_2363_checked

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

theorem patterns_17_8_8_verified_oai : ∀ D ∈ patterns_17_8_8, PatternVerified 17 8 D := by

  simp only [patterns_17_8_8, List.forall_mem_cons]

  exact ⟨⟨certificate_2348, certificate_2348_valid⟩, ⟨⟨certificate_2349, certificate_2349_valid⟩, ⟨⟨certificate_2350, certificate_2350_valid⟩, ⟨⟨certificate_2351, certificate_2351_valid⟩, ⟨⟨certificate_2352, certificate_2352_valid⟩, ⟨⟨certificate_2353, certificate_2353_valid⟩, ⟨⟨certificate_2354, certificate_2354_valid⟩, ⟨⟨certificate_2355, certificate_2355_valid⟩, ⟨⟨certificate_2356, certificate_2356_valid⟩, ⟨⟨certificate_2357, certificate_2357_valid⟩, ⟨⟨certificate_2358, certificate_2358_valid⟩, ⟨⟨certificate_2359, certificate_2359_valid⟩, ⟨⟨certificate_2360, certificate_2360_valid⟩, ⟨⟨certificate_2361, certificate_2361_valid⟩, ⟨⟨certificate_2362, certificate_2362_valid⟩, ⟨⟨certificate_2363, certificate_2363_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_8_verified_oai := @OAI.CycleClique.patterns_17_8_8_verified_oai
