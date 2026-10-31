-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_28_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:49:38.609992+00:00
-- url     : https://prove2.me/submissions/fef4b3b7-ee5c-4682-917c-ec09c51fc743

import Mathlib
import Definitions.Def_OAIQ107D070
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates069
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2200_checked : certificate_2200.Valid 16 8 16 certificate_2200_q certificate_2200_edges 8 6 [] := by decide +kernel
theorem certificate_2200_valid : certificate_2200.Valid 16 8 (patternOrder [[1,1,1,1],[2,2]]) (patternClique [[1,1,1,1],[2,2]]) (patternEdges [[1,1,1,1],[2,2]]) (patternAmount [[1,1,1,1],[2,2]]) (patternEdgeCount [[1,1,1,1],[2,2]]) [] := certificate_2200_checked

theorem certificate_2201_checked : certificate_2201.Valid 16 8 15 certificate_2201_q certificate_2201_edges 7 6 [] := by decide +kernel
theorem certificate_2201_valid : certificate_2201.Valid 16 8 (patternOrder [[1,1,1,1,1],[2]]) (patternClique [[1,1,1,1,1],[2]]) (patternEdges [[1,1,1,1,1],[2]]) (patternAmount [[1,1,1,1,1],[2]]) (patternEdgeCount [[1,1,1,1,1],[2]]) [] := certificate_2201_checked

theorem certificate_2202_checked : certificate_2202.Valid 16 8 16 certificate_2202_q certificate_2202_edges 8 6 [] := by decide +kernel
theorem certificate_2202_valid : certificate_2202.Valid 16 8 (patternOrder [[1,1,1,1,1],[3]]) (patternClique [[1,1,1,1,1],[3]]) (patternEdges [[1,1,1,1,1],[3]]) (patternAmount [[1,1,1,1,1],[3]]) (patternEdgeCount [[1,1,1,1,1],[3]]) [] := certificate_2202_checked

theorem certificate_2203_checked : certificate_2203.Valid 16 8 15 certificate_2203_q certificate_2203_edges 7 7 [] := by decide +kernel
theorem certificate_2203_valid : certificate_2203.Valid 16 8 (patternOrder [[1,1,1,1,1,1,1]]) (patternClique [[1,1,1,1,1,1,1]]) (patternEdges [[1,1,1,1,1,1,1]]) (patternAmount [[1,1,1,1,1,1,1]]) (patternEdgeCount [[1,1,1,1,1,1,1]]) [] := certificate_2203_checked

theorem certificate_2204_checked : certificate_2204.Valid 16 8 16 certificate_2204_q certificate_2204_edges 8 7 [] := by decide +kernel
theorem certificate_2204_valid : certificate_2204.Valid 16 8 (patternOrder [[1,1,1,1,1,1,2]]) (patternClique [[1,1,1,1,1,1,2]]) (patternEdges [[1,1,1,1,1,1,2]]) (patternAmount [[1,1,1,1,1,1,2]]) (patternEdgeCount [[1,1,1,1,1,1,2]]) [] := certificate_2204_checked

theorem certificate_2205_checked : certificate_2205.Valid 16 8 16 certificate_2205_q certificate_2205_edges 8 7 [] := by decide +kernel
theorem certificate_2205_valid : certificate_2205.Valid 16 8 (patternOrder [[1,1,1,1,1,2,1]]) (patternClique [[1,1,1,1,1,2,1]]) (patternEdges [[1,1,1,1,1,2,1]]) (patternAmount [[1,1,1,1,1,2,1]]) (patternEdgeCount [[1,1,1,1,1,2,1]]) [] := certificate_2205_checked

theorem certificate_2206_checked : certificate_2206.Valid 16 8 16 certificate_2206_q certificate_2206_edges 8 6 [] := by decide +kernel
theorem certificate_2206_valid : certificate_2206.Valid 16 8 (patternOrder [[1,1,1,1,2],[2]]) (patternClique [[1,1,1,1,2],[2]]) (patternEdges [[1,1,1,1,2],[2]]) (patternAmount [[1,1,1,1,2],[2]]) (patternEdgeCount [[1,1,1,1,2],[2]]) [] := certificate_2206_checked

theorem certificate_2207_checked : certificate_2207.Valid 16 8 16 certificate_2207_q certificate_2207_edges 8 7 [] := by decide +kernel
theorem certificate_2207_valid : certificate_2207.Valid 16 8 (patternOrder [[1,1,1,1,2,1,1]]) (patternClique [[1,1,1,1,2,1,1]]) (patternEdges [[1,1,1,1,2,1,1]]) (patternAmount [[1,1,1,1,2,1,1]]) (patternEdgeCount [[1,1,1,1,2,1,1]]) [] := certificate_2207_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates070
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2208_checked : certificate_2208.Valid 16 8 16 certificate_2208_q certificate_2208_edges 8 6 [] := by decide +kernel
theorem certificate_2208_valid : certificate_2208.Valid 16 8 (patternOrder [[1,1,1,2],[1,2]]) (patternClique [[1,1,1,2],[1,2]]) (patternEdges [[1,1,1,2],[1,2]]) (patternAmount [[1,1,1,2],[1,2]]) (patternEdgeCount [[1,1,1,2],[1,2]]) [] := certificate_2208_checked

theorem certificate_2209_checked : certificate_2209.Valid 16 8 16 certificate_2209_q certificate_2209_edges 8 6 [] := by decide +kernel
theorem certificate_2209_valid : certificate_2209.Valid 16 8 (patternOrder [[1,1,1,2,1],[2]]) (patternClique [[1,1,1,2,1],[2]]) (patternEdges [[1,1,1,2,1],[2]]) (patternAmount [[1,1,1,2,1],[2]]) (patternEdgeCount [[1,1,1,2,1],[2]]) [] := certificate_2209_checked

theorem certificate_2210_checked : certificate_2210.Valid 16 8 16 certificate_2210_q certificate_2210_edges 8 7 [] := by decide +kernel
theorem certificate_2210_valid : certificate_2210.Valid 16 8 (patternOrder [[1,1,1,2,1,1,1]]) (patternClique [[1,1,1,2,1,1,1]]) (patternEdges [[1,1,1,2,1,1,1]]) (patternAmount [[1,1,1,2,1,1,1]]) (patternEdgeCount [[1,1,1,2,1,1,1]]) [] := certificate_2210_checked

theorem certificate_2211_checked : certificate_2211.Valid 16 8 16 certificate_2211_q certificate_2211_edges 8 6 [] := by decide +kernel
theorem certificate_2211_valid : certificate_2211.Valid 16 8 (patternOrder [[1,1,2],[1,1,2]]) (patternClique [[1,1,2],[1,1,2]]) (patternEdges [[1,1,2],[1,1,2]]) (patternAmount [[1,1,2],[1,1,2]]) (patternEdgeCount [[1,1,2],[1,1,2]]) [] := certificate_2211_checked

theorem certificate_2212_checked : certificate_2212.Valid 16 8 16 certificate_2212_q certificate_2212_edges 8 6 [] := by decide +kernel
theorem certificate_2212_valid : certificate_2212.Valid 16 8 (patternOrder [[1,1,2],[1,2,1]]) (patternClique [[1,1,2],[1,2,1]]) (patternEdges [[1,1,2],[1,2,1]]) (patternAmount [[1,1,2],[1,2,1]]) (patternEdgeCount [[1,1,2],[1,2,1]]) [] := certificate_2212_checked

theorem certificate_2213_checked : certificate_2213.Valid 16 8 16 certificate_2213_q certificate_2213_edges 8 5 [] := by decide +kernel
theorem certificate_2213_valid : certificate_2213.Valid 16 8 (patternOrder [[1,1,2],[2],[2]]) (patternClique [[1,1,2],[2],[2]]) (patternEdges [[1,1,2],[2],[2]]) (patternAmount [[1,1,2],[2],[2]]) (patternEdgeCount [[1,1,2],[2],[2]]) [] := certificate_2213_checked

theorem certificate_2214_checked : certificate_2214.Valid 16 8 16 certificate_2214_q certificate_2214_edges 8 6 [] := by decide +kernel
theorem certificate_2214_valid : certificate_2214.Valid 16 8 (patternOrder [[1,1,2,1],[1,2]]) (patternClique [[1,1,2,1],[1,2]]) (patternEdges [[1,1,2,1],[1,2]]) (patternAmount [[1,1,2,1],[1,2]]) (patternEdgeCount [[1,1,2,1],[1,2]]) [] := certificate_2214_checked

theorem certificate_2215_checked : certificate_2215.Valid 16 8 16 certificate_2215_q certificate_2215_edges 8 6 [] := by decide +kernel
theorem certificate_2215_valid : certificate_2215.Valid 16 8 (patternOrder [[1,1,2,1,1],[2]]) (patternClique [[1,1,2,1,1],[2]]) (patternEdges [[1,1,2,1,1],[2]]) (patternAmount [[1,1,2,1,1],[2]]) (patternEdgeCount [[1,1,2,1,1],[2]]) [] := certificate_2215_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns16x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_16_8_28_verified_oai : ∀ D ∈ patterns_16_8_28, PatternVerified 16 8 D := by

  simp only [patterns_16_8_28, List.forall_mem_cons]

  exact ⟨⟨certificate_2200, certificate_2200_valid⟩, ⟨⟨certificate_2201, certificate_2201_valid⟩, ⟨⟨certificate_2202, certificate_2202_valid⟩, ⟨⟨certificate_2203, certificate_2203_valid⟩, ⟨⟨certificate_2204, certificate_2204_valid⟩, ⟨⟨certificate_2205, certificate_2205_valid⟩, ⟨⟨certificate_2206, certificate_2206_valid⟩, ⟨⟨certificate_2207, certificate_2207_valid⟩, ⟨⟨certificate_2208, certificate_2208_valid⟩, ⟨⟨certificate_2209, certificate_2209_valid⟩, ⟨⟨certificate_2210, certificate_2210_valid⟩, ⟨⟨certificate_2211, certificate_2211_valid⟩, ⟨⟨certificate_2212, certificate_2212_valid⟩, ⟨⟨certificate_2213, certificate_2213_valid⟩, ⟨⟨certificate_2214, certificate_2214_valid⟩, ⟨⟨certificate_2215, certificate_2215_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_28_verified_oai := @OAI.CycleClique.patterns_16_8_28_verified_oai
