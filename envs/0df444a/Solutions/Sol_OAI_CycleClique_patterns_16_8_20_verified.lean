-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_20_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:44:07.638611+00:00
-- url     : https://prove2.me/submissions/aceb5721-07c0-4ccf-8e4d-60ee4aff3289

import Mathlib
import Definitions.Def_OAIQ107D065
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates065
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2072_checked : certificate_2072.Valid 16 8 16 certificate_2072_q certificate_2072_edges 8 5 [] := by decide +kernel
theorem certificate_2072_valid : certificate_2072.Valid 16 8 (patternOrder [[],[1,1,1],[2,3]]) (patternClique [[],[1,1,1],[2,3]]) (patternEdges [[],[1,1,1],[2,3]]) (patternAmount [[],[1,1,1],[2,3]]) (patternEdgeCount [[],[1,1,1],[2,3]]) [] := certificate_2072_checked

theorem certificate_2073_checked : certificate_2073.Valid 16 8 14 certificate_2073_q certificate_2073_edges 6 5 [] := by decide +kernel
theorem certificate_2073_valid : certificate_2073.Valid 16 8 (patternOrder [[],[1,1,1,1],[2]]) (patternClique [[],[1,1,1,1],[2]]) (patternEdges [[],[1,1,1,1],[2]]) (patternAmount [[],[1,1,1,1],[2]]) (patternEdgeCount [[],[1,1,1,1],[2]]) [] := certificate_2073_checked

theorem certificate_2074_checked : certificate_2074.Valid 16 8 15 certificate_2074_q certificate_2074_edges 7 5 [] := by decide +kernel
theorem certificate_2074_valid : certificate_2074.Valid 16 8 (patternOrder [[],[1,1,1,1],[3]]) (patternClique [[],[1,1,1,1],[3]]) (patternEdges [[],[1,1,1,1],[3]]) (patternAmount [[],[1,1,1,1],[3]]) (patternEdgeCount [[],[1,1,1,1],[3]]) [] := certificate_2074_checked

theorem certificate_2075_checked : certificate_2075.Valid 16 8 16 certificate_2075_q certificate_2075_edges 8 5 [] := by decide +kernel
theorem certificate_2075_valid : certificate_2075.Valid 16 8 (patternOrder [[],[1,1,1,1],[4]]) (patternClique [[],[1,1,1,1],[4]]) (patternEdges [[],[1,1,1,1],[4]]) (patternAmount [[],[1,1,1,1],[4]]) (patternEdgeCount [[],[1,1,1,1],[4]]) [] := certificate_2075_checked

theorem certificate_2076_checked : certificate_2076.Valid 16 8 14 certificate_2076_q certificate_2076_edges 6 6 [] := by decide +kernel
theorem certificate_2076_valid : certificate_2076.Valid 16 8 (patternOrder [[],[1,1,1,1,1,1]]) (patternClique [[],[1,1,1,1,1,1]]) (patternEdges [[],[1,1,1,1,1,1]]) (patternAmount [[],[1,1,1,1,1,1]]) (patternEdgeCount [[],[1,1,1,1,1,1]]) [] := certificate_2076_checked

theorem certificate_2077_checked : certificate_2077.Valid 16 8 15 certificate_2077_q certificate_2077_edges 7 6 [] := by decide +kernel
theorem certificate_2077_valid : certificate_2077.Valid 16 8 (patternOrder [[],[1,1,1,1,1,2]]) (patternClique [[],[1,1,1,1,1,2]]) (patternEdges [[],[1,1,1,1,1,2]]) (patternAmount [[],[1,1,1,1,1,2]]) (patternEdgeCount [[],[1,1,1,1,1,2]]) [] := certificate_2077_checked

theorem certificate_2078_checked : certificate_2078.Valid 16 8 16 certificate_2078_q certificate_2078_edges 8 6 [] := by decide +kernel
theorem certificate_2078_valid : certificate_2078.Valid 16 8 (patternOrder [[],[1,1,1,1,1,3]]) (patternClique [[],[1,1,1,1,1,3]]) (patternEdges [[],[1,1,1,1,1,3]]) (patternAmount [[],[1,1,1,1,1,3]]) (patternEdgeCount [[],[1,1,1,1,1,3]]) [] := certificate_2078_checked

theorem certificate_2079_checked : certificate_2079.Valid 16 8 15 certificate_2079_q certificate_2079_edges 7 6 [] := by decide +kernel
theorem certificate_2079_valid : certificate_2079.Valid 16 8 (patternOrder [[],[1,1,1,1,2,1]]) (patternClique [[],[1,1,1,1,2,1]]) (patternEdges [[],[1,1,1,1,2,1]]) (patternAmount [[],[1,1,1,1,2,1]]) (patternEdgeCount [[],[1,1,1,1,2,1]]) [] := certificate_2079_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates066
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2080_checked : certificate_2080.Valid 16 8 16 certificate_2080_q certificate_2080_edges 8 6 [] := by decide +kernel
theorem certificate_2080_valid : certificate_2080.Valid 16 8 (patternOrder [[],[1,1,1,1,2,2]]) (patternClique [[],[1,1,1,1,2,2]]) (patternEdges [[],[1,1,1,1,2,2]]) (patternAmount [[],[1,1,1,1,2,2]]) (patternEdgeCount [[],[1,1,1,1,2,2]]) [] := certificate_2080_checked

theorem certificate_2081_checked : certificate_2081.Valid 16 8 16 certificate_2081_q certificate_2081_edges 8 6 [] := by decide +kernel
theorem certificate_2081_valid : certificate_2081.Valid 16 8 (patternOrder [[],[1,1,1,1,3,1]]) (patternClique [[],[1,1,1,1,3,1]]) (patternEdges [[],[1,1,1,1,3,1]]) (patternAmount [[],[1,1,1,1,3,1]]) (patternEdgeCount [[],[1,1,1,1,3,1]]) [] := certificate_2081_checked

theorem certificate_2082_checked : certificate_2082.Valid 16 8 15 certificate_2082_q certificate_2082_edges 7 5 [] := by decide +kernel
theorem certificate_2082_valid : certificate_2082.Valid 16 8 (patternOrder [[],[1,1,1,2],[2]]) (patternClique [[],[1,1,1,2],[2]]) (patternEdges [[],[1,1,1,2],[2]]) (patternAmount [[],[1,1,1,2],[2]]) (patternEdgeCount [[],[1,1,1,2],[2]]) [] := certificate_2082_checked

theorem certificate_2083_checked : certificate_2083.Valid 16 8 16 certificate_2083_q certificate_2083_edges 8 5 [] := by decide +kernel
theorem certificate_2083_valid : certificate_2083.Valid 16 8 (patternOrder [[],[1,1,1,2],[3]]) (patternClique [[],[1,1,1,2],[3]]) (patternEdges [[],[1,1,1,2],[3]]) (patternAmount [[],[1,1,1,2],[3]]) (patternEdgeCount [[],[1,1,1,2],[3]]) [] := certificate_2083_checked

theorem certificate_2084_checked : certificate_2084.Valid 16 8 15 certificate_2084_q certificate_2084_edges 7 6 [] := by decide +kernel
theorem certificate_2084_valid : certificate_2084.Valid 16 8 (patternOrder [[],[1,1,1,2,1,1]]) (patternClique [[],[1,1,1,2,1,1]]) (patternEdges [[],[1,1,1,2,1,1]]) (patternAmount [[],[1,1,1,2,1,1]]) (patternEdgeCount [[],[1,1,1,2,1,1]]) [] := certificate_2084_checked

theorem certificate_2085_checked : certificate_2085.Valid 16 8 16 certificate_2085_q certificate_2085_edges 8 6 [] := by decide +kernel
theorem certificate_2085_valid : certificate_2085.Valid 16 8 (patternOrder [[],[1,1,1,2,1,2]]) (patternClique [[],[1,1,1,2,1,2]]) (patternEdges [[],[1,1,1,2,1,2]]) (patternAmount [[],[1,1,1,2,1,2]]) (patternEdgeCount [[],[1,1,1,2,1,2]]) [] := certificate_2085_checked

theorem certificate_2086_checked : certificate_2086.Valid 16 8 16 certificate_2086_q certificate_2086_edges 8 6 [] := by decide +kernel
theorem certificate_2086_valid : certificate_2086.Valid 16 8 (patternOrder [[],[1,1,1,2,2,1]]) (patternClique [[],[1,1,1,2,2,1]]) (patternEdges [[],[1,1,1,2,2,1]]) (patternAmount [[],[1,1,1,2,2,1]]) (patternEdgeCount [[],[1,1,1,2,2,1]]) [] := certificate_2086_checked

theorem certificate_2087_checked : certificate_2087.Valid 16 8 16 certificate_2087_q certificate_2087_edges 8 5 [] := by decide +kernel
theorem certificate_2087_valid : certificate_2087.Valid 16 8 (patternOrder [[],[1,1,1,3],[2]]) (patternClique [[],[1,1,1,3],[2]]) (patternEdges [[],[1,1,1,3],[2]]) (patternAmount [[],[1,1,1,3],[2]]) (patternEdgeCount [[],[1,1,1,3],[2]]) [] := certificate_2087_checked

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

theorem patterns_16_8_20_verified_oai : ∀ D ∈ patterns_16_8_20, PatternVerified 16 8 D := by

  simp only [patterns_16_8_20, List.forall_mem_cons]

  exact ⟨⟨certificate_2072, certificate_2072_valid⟩, ⟨⟨certificate_2073, certificate_2073_valid⟩, ⟨⟨certificate_2074, certificate_2074_valid⟩, ⟨⟨certificate_2075, certificate_2075_valid⟩, ⟨⟨certificate_2076, certificate_2076_valid⟩, ⟨⟨certificate_2077, certificate_2077_valid⟩, ⟨⟨certificate_2078, certificate_2078_valid⟩, ⟨⟨certificate_2079, certificate_2079_valid⟩, ⟨⟨certificate_2080, certificate_2080_valid⟩, ⟨⟨certificate_2081, certificate_2081_valid⟩, ⟨⟨certificate_2082, certificate_2082_valid⟩, ⟨⟨certificate_2083, certificate_2083_valid⟩, ⟨⟨certificate_2084, certificate_2084_valid⟩, ⟨⟨certificate_2085, certificate_2085_valid⟩, ⟨⟨certificate_2086, certificate_2086_valid⟩, ⟨⟨certificate_2087, certificate_2087_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_20_verified_oai := @OAI.CycleClique.patterns_16_8_20_verified_oai
