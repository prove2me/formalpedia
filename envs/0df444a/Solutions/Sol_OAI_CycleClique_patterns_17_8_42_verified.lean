-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_42_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:44:11.517081+00:00
-- url     : https://prove2.me/submissions/4358993f-af68-41d3-9a5a-a7f3cf7b0c37

import Mathlib
import Definitions.Def_OAIQ107D005
import Definitions.Def_OAIQ107D097
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates091
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2892_checked : certificate_2892.Valid 17 8 13 certificate_2892_q certificate_2892_edges 5 5 [] := by decide +kernel
theorem certificate_2892_valid : certificate_2892.Valid 17 8 (patternOrder [[1],[1,1],[1,1]]) (patternClique [[1],[1,1],[1,1]]) (patternEdges [[1],[1,1],[1,1]]) (patternAmount [[1],[1,1],[1,1]]) (patternEdgeCount [[1],[1,1],[1,1]]) [] := certificate_2892_checked

theorem certificate_2893_checked : certificate_2893.Valid 17 8 14 certificate_2893_q certificate_2893_edges 6 5 [] := by decide +kernel
theorem certificate_2893_valid : certificate_2893.Valid 17 8 (patternOrder [[1],[1,1],[1,2]]) (patternClique [[1],[1,1],[1,2]]) (patternEdges [[1],[1,1],[1,2]]) (patternAmount [[1],[1,1],[1,2]]) (patternEdgeCount [[1],[1,1],[1,2]]) [] := certificate_2893_checked

theorem certificate_2894_checked : certificate_2894.Valid 17 8 15 certificate_2894_q certificate_2894_edges 7 5 [] := by decide +kernel
theorem certificate_2894_valid : certificate_2894.Valid 17 8 (patternOrder [[1],[1,1],[1,3]]) (patternClique [[1],[1,1],[1,3]]) (patternEdges [[1],[1,1],[1,3]]) (patternAmount [[1],[1,1],[1,3]]) (patternEdgeCount [[1],[1,1],[1,3]]) [] := certificate_2894_checked

theorem certificate_2895_checked : certificate_2895.Valid 17 8 16 certificate_2895_q certificate_2895_edges 8 5 [] := by decide +kernel
theorem certificate_2895_valid : certificate_2895.Valid 17 8 (patternOrder [[1],[1,1],[1,4]]) (patternClique [[1],[1,1],[1,4]]) (patternEdges [[1],[1,1],[1,4]]) (patternAmount [[1],[1,1],[1,4]]) (patternEdgeCount [[1],[1,1],[1,4]]) [] := certificate_2895_checked

theorem certificate_2896_checked : certificate_2896.Valid 17 8 17 certificate_2896_q certificate_2896_edges 9 5 [] := by decide +kernel
theorem certificate_2896_valid : certificate_2896.Valid 17 8 (patternOrder [[1],[1,1],[1,5]]) (patternClique [[1],[1,1],[1,5]]) (patternEdges [[1],[1,1],[1,5]]) (patternAmount [[1],[1,1],[1,5]]) (patternEdgeCount [[1],[1,1],[1,5]]) [] := certificate_2896_checked

theorem certificate_2897_checked : certificate_2897.Valid 17 8 15 certificate_2897_q certificate_2897_edges 7 5 [] := by decide +kernel
theorem certificate_2897_valid : certificate_2897.Valid 17 8 (patternOrder [[1],[1,1],[2,2]]) (patternClique [[1],[1,1],[2,2]]) (patternEdges [[1],[1,1],[2,2]]) (patternAmount [[1],[1,1],[2,2]]) (patternEdgeCount [[1],[1,1],[2,2]]) [] := certificate_2897_checked

theorem certificate_2898_checked : certificate_2898.Valid 17 8 16 certificate_2898_q certificate_2898_edges 8 5 [] := by decide +kernel
theorem certificate_2898_valid : certificate_2898.Valid 17 8 (patternOrder [[1],[1,1],[2,3]]) (patternClique [[1],[1,1],[2,3]]) (patternEdges [[1],[1,1],[2,3]]) (patternAmount [[1],[1,1],[2,3]]) (patternEdgeCount [[1],[1,1],[2,3]]) [] := certificate_2898_checked

theorem certificate_2899_checked : certificate_2899.Valid 17 8 17 certificate_2899_q certificate_2899_edges 9 5 [] := by decide +kernel
theorem certificate_2899_valid : certificate_2899.Valid 17 8 (patternOrder [[1],[1,1],[2,4]]) (patternClique [[1],[1,1],[2,4]]) (patternEdges [[1],[1,1],[2,4]]) (patternAmount [[1],[1,1],[2,4]]) (patternEdgeCount [[1],[1,1],[2,4]]) [] := certificate_2899_checked

theorem certificate_2900_checked : certificate_2900.Valid 17 8 17 certificate_2900_q certificate_2900_edges 9 5 [] := by decide +kernel
theorem certificate_2900_valid : certificate_2900.Valid 17 8 (patternOrder [[1],[1,1],[3,3]]) (patternClique [[1],[1,1],[3,3]]) (patternEdges [[1],[1,1],[3,3]]) (patternAmount [[1],[1,1],[3,3]]) (patternEdgeCount [[1],[1,1],[3,3]]) [] := certificate_2900_checked

theorem certificate_2901_checked : certificate_2901.Valid 17 8 14 certificate_2901_q certificate_2901_edges 6 5 [] := by decide +kernel
theorem certificate_2901_valid : certificate_2901.Valid 17 8 (patternOrder [[1],[1,1,1],[2]]) (patternClique [[1],[1,1,1],[2]]) (patternEdges [[1],[1,1,1],[2]]) (patternAmount [[1],[1,1,1],[2]]) (patternEdgeCount [[1],[1,1,1],[2]]) [] := certificate_2901_checked

theorem certificate_2902_checked : certificate_2902.Valid 17 8 15 certificate_2902_q certificate_2902_edges 7 5 [] := by decide +kernel
theorem certificate_2902_valid : certificate_2902.Valid 17 8 (patternOrder [[1],[1,1,1],[3]]) (patternClique [[1],[1,1,1],[3]]) (patternEdges [[1],[1,1,1],[3]]) (patternAmount [[1],[1,1,1],[3]]) (patternEdgeCount [[1],[1,1,1],[3]]) [] := certificate_2902_checked

theorem certificate_2903_checked : certificate_2903.Valid 17 8 16 certificate_2903_q certificate_2903_edges 8 5 [] := by decide +kernel
theorem certificate_2903_valid : certificate_2903.Valid 17 8 (patternOrder [[1],[1,1,1],[4]]) (patternClique [[1],[1,1,1],[4]]) (patternEdges [[1],[1,1,1],[4]]) (patternAmount [[1],[1,1,1],[4]]) (patternEdgeCount [[1],[1,1,1],[4]]) [] := certificate_2903_checked

theorem certificate_2904_checked : certificate_2904.Valid 17 8 17 certificate_2904_q certificate_2904_edges 9 5 [] := by decide +kernel
theorem certificate_2904_valid : certificate_2904.Valid 17 8 (patternOrder [[1],[1,1,1],[5]]) (patternClique [[1],[1,1,1],[5]]) (patternEdges [[1],[1,1,1],[5]]) (patternAmount [[1],[1,1,1],[5]]) (patternEdgeCount [[1],[1,1,1],[5]]) [] := certificate_2904_checked

theorem certificate_2905_checked : certificate_2905.Valid 17 8 14 certificate_2905_q certificate_2905_edges 6 6 [] := by decide +kernel
theorem certificate_2905_valid : certificate_2905.Valid 17 8 (patternOrder [[1],[1,1,1,1,1]]) (patternClique [[1],[1,1,1,1,1]]) (patternEdges [[1],[1,1,1,1,1]]) (patternAmount [[1],[1,1,1,1,1]]) (patternEdgeCount [[1],[1,1,1,1,1]]) [] := certificate_2905_checked

theorem certificate_2906_checked : certificate_2906.Valid 17 8 15 certificate_2906_q certificate_2906_edges 7 6 [] := by decide +kernel
theorem certificate_2906_valid : certificate_2906.Valid 17 8 (patternOrder [[1],[1,1,1,1,2]]) (patternClique [[1],[1,1,1,1,2]]) (patternEdges [[1],[1,1,1,1,2]]) (patternAmount [[1],[1,1,1,1,2]]) (patternEdgeCount [[1],[1,1,1,1,2]]) [] := certificate_2906_checked

theorem certificate_2907_checked : certificate_2907.Valid 17 8 16 certificate_2907_q certificate_2907_edges 8 6 [] := by decide +kernel
theorem certificate_2907_valid : certificate_2907.Valid 17 8 (patternOrder [[1],[1,1,1,1,3]]) (patternClique [[1],[1,1,1,1,3]]) (patternEdges [[1],[1,1,1,1,3]]) (patternAmount [[1],[1,1,1,1,3]]) (patternEdgeCount [[1],[1,1,1,1,3]]) [] := certificate_2907_checked

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

theorem patterns_17_8_42_verified_oai : ∀ D ∈ patterns_17_8_42, PatternVerified 17 8 D := by

  simp only [patterns_17_8_42, List.forall_mem_cons]

  exact ⟨⟨certificate_2892, certificate_2892_valid⟩, ⟨⟨certificate_2893, certificate_2893_valid⟩, ⟨⟨certificate_2894, certificate_2894_valid⟩, ⟨⟨certificate_2895, certificate_2895_valid⟩, ⟨⟨certificate_2896, certificate_2896_valid⟩, ⟨⟨certificate_2897, certificate_2897_valid⟩, ⟨⟨certificate_2898, certificate_2898_valid⟩, ⟨⟨certificate_2899, certificate_2899_valid⟩, ⟨⟨certificate_2900, certificate_2900_valid⟩, ⟨⟨certificate_2901, certificate_2901_valid⟩, ⟨⟨certificate_2902, certificate_2902_valid⟩, ⟨⟨certificate_2903, certificate_2903_valid⟩, ⟨⟨certificate_2904, certificate_2904_valid⟩, ⟨⟨certificate_2905, certificate_2905_valid⟩, ⟨⟨certificate_2906, certificate_2906_valid⟩, ⟨⟨certificate_2907, certificate_2907_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_42_verified_oai := @OAI.CycleClique.patterns_17_8_42_verified_oai
