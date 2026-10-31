-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_47_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:52:10.316655+00:00
-- url     : https://prove2.me/submissions/8a58725f-3f45-4ab3-b06c-9495215dd3c9

import Mathlib
import Definitions.Def_OAIQ107D005
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates093
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2972_checked : certificate_2972.Valid 17 8 17 certificate_2972_q certificate_2972_edges 9 5 [] := by decide +kernel
theorem certificate_2972_valid : certificate_2972.Valid 17 8 (patternOrder [[1,1],[1,1],[5]]) (patternClique [[1,1],[1,1],[5]]) (patternEdges [[1,1],[1,1],[5]]) (patternAmount [[1,1],[1,1],[5]]) (patternEdgeCount [[1,1],[1,1],[5]]) [] := certificate_2972_checked

theorem certificate_2973_checked : certificate_2973.Valid 17 8 14 certificate_2973_q certificate_2973_edges 6 6 [] := by decide +kernel
theorem certificate_2973_valid : certificate_2973.Valid 17 8 (patternOrder [[1,1],[1,1,1,1]]) (patternClique [[1,1],[1,1,1,1]]) (patternEdges [[1,1],[1,1,1,1]]) (patternAmount [[1,1],[1,1,1,1]]) (patternEdgeCount [[1,1],[1,1,1,1]]) [] := certificate_2973_checked

theorem certificate_2974_checked : certificate_2974.Valid 17 8 15 certificate_2974_q certificate_2974_edges 7 6 [] := by decide +kernel
theorem certificate_2974_valid : certificate_2974.Valid 17 8 (patternOrder [[1,1],[1,1,1,2]]) (patternClique [[1,1],[1,1,1,2]]) (patternEdges [[1,1],[1,1,1,2]]) (patternAmount [[1,1],[1,1,1,2]]) (patternEdgeCount [[1,1],[1,1,1,2]]) [] := certificate_2974_checked

theorem certificate_2975_checked : certificate_2975.Valid 17 8 16 certificate_2975_q certificate_2975_edges 8 6 [] := by decide +kernel
theorem certificate_2975_valid : certificate_2975.Valid 17 8 (patternOrder [[1,1],[1,1,1,3]]) (patternClique [[1,1],[1,1,1,3]]) (patternEdges [[1,1],[1,1,1,3]]) (patternAmount [[1,1],[1,1,1,3]]) (patternEdgeCount [[1,1],[1,1,1,3]]) [] := certificate_2975_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates094
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2976_checked : certificate_2976.Valid 17 8 17 certificate_2976_q certificate_2976_edges 9 6 [] := by decide +kernel
theorem certificate_2976_valid : certificate_2976.Valid 17 8 (patternOrder [[1,1],[1,1,1,4]]) (patternClique [[1,1],[1,1,1,4]]) (patternEdges [[1,1],[1,1,1,4]]) (patternAmount [[1,1],[1,1,1,4]]) (patternEdgeCount [[1,1],[1,1,1,4]]) [] := certificate_2976_checked

theorem certificate_2977_checked : certificate_2977.Valid 17 8 15 certificate_2977_q certificate_2977_edges 7 6 [] := by decide +kernel
theorem certificate_2977_valid : certificate_2977.Valid 17 8 (patternOrder [[1,1],[1,1,2,1]]) (patternClique [[1,1],[1,1,2,1]]) (patternEdges [[1,1],[1,1,2,1]]) (patternAmount [[1,1],[1,1,2,1]]) (patternEdgeCount [[1,1],[1,1,2,1]]) [] := certificate_2977_checked

theorem certificate_2978_checked : certificate_2978.Valid 17 8 16 certificate_2978_q certificate_2978_edges 8 6 [] := by decide +kernel
theorem certificate_2978_valid : certificate_2978.Valid 17 8 (patternOrder [[1,1],[1,1,2,2]]) (patternClique [[1,1],[1,1,2,2]]) (patternEdges [[1,1],[1,1,2,2]]) (patternAmount [[1,1],[1,1,2,2]]) (patternEdgeCount [[1,1],[1,1,2,2]]) [] := certificate_2978_checked

theorem certificate_2979_checked : certificate_2979.Valid 17 8 17 certificate_2979_q certificate_2979_edges 9 6 [] := by decide +kernel
theorem certificate_2979_valid : certificate_2979.Valid 17 8 (patternOrder [[1,1],[1,1,2,3]]) (patternClique [[1,1],[1,1,2,3]]) (patternEdges [[1,1],[1,1,2,3]]) (patternAmount [[1,1],[1,1,2,3]]) (patternEdgeCount [[1,1],[1,1,2,3]]) [] := certificate_2979_checked

theorem certificate_2980_checked : certificate_2980.Valid 17 8 16 certificate_2980_q certificate_2980_edges 8 6 [] := by decide +kernel
theorem certificate_2980_valid : certificate_2980.Valid 17 8 (patternOrder [[1,1],[1,1,3,1]]) (patternClique [[1,1],[1,1,3,1]]) (patternEdges [[1,1],[1,1,3,1]]) (patternAmount [[1,1],[1,1,3,1]]) (patternEdgeCount [[1,1],[1,1,3,1]]) [] := certificate_2980_checked

theorem certificate_2981_checked : certificate_2981.Valid 17 8 17 certificate_2981_q certificate_2981_edges 9 6 [] := by decide +kernel
theorem certificate_2981_valid : certificate_2981.Valid 17 8 (patternOrder [[1,1],[1,1,3,2]]) (patternClique [[1,1],[1,1,3,2]]) (patternEdges [[1,1],[1,1,3,2]]) (patternAmount [[1,1],[1,1,3,2]]) (patternEdgeCount [[1,1],[1,1,3,2]]) [] := certificate_2981_checked

theorem certificate_2982_checked : certificate_2982.Valid 17 8 17 certificate_2982_q certificate_2982_edges 9 6 [] := by decide +kernel
theorem certificate_2982_valid : certificate_2982.Valid 17 8 (patternOrder [[1,1],[1,1,4,1]]) (patternClique [[1,1],[1,1,4,1]]) (patternEdges [[1,1],[1,1,4,1]]) (patternAmount [[1,1],[1,1,4,1]]) (patternEdgeCount [[1,1],[1,1,4,1]]) [] := certificate_2982_checked

theorem certificate_2983_checked : certificate_2983.Valid 17 8 15 certificate_2983_q certificate_2983_edges 7 5 [] := by decide +kernel
theorem certificate_2983_valid : certificate_2983.Valid 17 8 (patternOrder [[1,1],[1,2],[2]]) (patternClique [[1,1],[1,2],[2]]) (patternEdges [[1,1],[1,2],[2]]) (patternAmount [[1,1],[1,2],[2]]) (patternEdgeCount [[1,1],[1,2],[2]]) [] := certificate_2983_checked

theorem certificate_2984_checked : certificate_2984.Valid 17 8 16 certificate_2984_q certificate_2984_edges 8 5 [] := by decide +kernel
theorem certificate_2984_valid : certificate_2984.Valid 17 8 (patternOrder [[1,1],[1,2],[3]]) (patternClique [[1,1],[1,2],[3]]) (patternEdges [[1,1],[1,2],[3]]) (patternAmount [[1,1],[1,2],[3]]) (patternEdgeCount [[1,1],[1,2],[3]]) [] := certificate_2984_checked

theorem certificate_2985_checked : certificate_2985.Valid 17 8 17 certificate_2985_q certificate_2985_edges 9 5 [] := by decide +kernel
theorem certificate_2985_valid : certificate_2985.Valid 17 8 (patternOrder [[1,1],[1,2],[4]]) (patternClique [[1,1],[1,2],[4]]) (patternEdges [[1,1],[1,2],[4]]) (patternAmount [[1,1],[1,2],[4]]) (patternEdgeCount [[1,1],[1,2],[4]]) [] := certificate_2985_checked

theorem certificate_2986_checked : certificate_2986.Valid 17 8 16 certificate_2986_q certificate_2986_edges 8 6 [] := by decide +kernel
theorem certificate_2986_valid : certificate_2986.Valid 17 8 (patternOrder [[1,1],[1,2,1,2]]) (patternClique [[1,1],[1,2,1,2]]) (patternEdges [[1,1],[1,2,1,2]]) (patternAmount [[1,1],[1,2,1,2]]) (patternEdgeCount [[1,1],[1,2,1,2]]) [] := certificate_2986_checked

theorem certificate_2987_checked : certificate_2987.Valid 17 8 17 certificate_2987_q certificate_2987_edges 9 6 [] := by decide +kernel
theorem certificate_2987_valid : certificate_2987.Valid 17 8 (patternOrder [[1,1],[1,2,1,3]]) (patternClique [[1,1],[1,2,1,3]]) (patternEdges [[1,1],[1,2,1,3]]) (patternAmount [[1,1],[1,2,1,3]]) (patternEdgeCount [[1,1],[1,2,1,3]]) [] := certificate_2987_checked

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

theorem patterns_17_8_47_verified_oai : ∀ D ∈ patterns_17_8_47, PatternVerified 17 8 D := by

  simp only [patterns_17_8_47, List.forall_mem_cons]

  exact ⟨⟨certificate_2972, certificate_2972_valid⟩, ⟨⟨certificate_2973, certificate_2973_valid⟩, ⟨⟨certificate_2974, certificate_2974_valid⟩, ⟨⟨certificate_2975, certificate_2975_valid⟩, ⟨⟨certificate_2976, certificate_2976_valid⟩, ⟨⟨certificate_2977, certificate_2977_valid⟩, ⟨⟨certificate_2978, certificate_2978_valid⟩, ⟨⟨certificate_2979, certificate_2979_valid⟩, ⟨⟨certificate_2980, certificate_2980_valid⟩, ⟨⟨certificate_2981, certificate_2981_valid⟩, ⟨⟨certificate_2982, certificate_2982_valid⟩, ⟨⟨certificate_2983, certificate_2983_valid⟩, ⟨⟨certificate_2984, certificate_2984_valid⟩, ⟨⟨certificate_2985, certificate_2985_valid⟩, ⟨⟨certificate_2986, certificate_2986_valid⟩, ⟨⟨certificate_2987, certificate_2987_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_47_verified_oai := @OAI.CycleClique.patterns_17_8_47_verified_oai
