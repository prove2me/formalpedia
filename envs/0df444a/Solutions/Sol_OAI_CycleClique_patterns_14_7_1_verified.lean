-- Prove2me | solution 1 for OAI.CycleClique.patterns_14_7_1_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:22:10.196518+00:00
-- url     : https://prove2.me/submissions/07d9f759-c6dd-401f-99c3-a764276197c3

import Mathlib
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates027
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_852_checked : certificate_852.Valid 14 7 13 certificate_852_q certificate_852_edges 6 2 [] := by decide +kernel
theorem certificate_852_valid : certificate_852.Valid 14 7 (patternOrder [[],[],[],[],[2,4]]) (patternClique [[],[],[],[],[2,4]]) (patternEdges [[],[],[],[],[2,4]]) (patternAmount [[],[],[],[],[2,4]]) (patternEdgeCount [[],[],[],[],[2,4]]) [] := certificate_852_checked

theorem certificate_853_checked : certificate_853.Valid 14 7 14 certificate_853_q certificate_853_edges 7 2 [] := by decide +kernel
theorem certificate_853_valid : certificate_853.Valid 14 7 (patternOrder [[],[],[],[],[2,5]]) (patternClique [[],[],[],[],[2,5]]) (patternEdges [[],[],[],[],[2,5]]) (patternAmount [[],[],[],[],[2,5]]) (patternEdgeCount [[],[],[],[],[2,5]]) [] := certificate_853_checked

theorem certificate_854_checked : certificate_854.Valid 14 7 13 certificate_854_q certificate_854_edges 6 2 [] := by decide +kernel
theorem certificate_854_valid : certificate_854.Valid 14 7 (patternOrder [[],[],[],[],[3,3]]) (patternClique [[],[],[],[],[3,3]]) (patternEdges [[],[],[],[],[3,3]]) (patternAmount [[],[],[],[],[3,3]]) (patternEdgeCount [[],[],[],[],[3,3]]) [] := certificate_854_checked

theorem certificate_855_checked : certificate_855.Valid 14 7 14 certificate_855_q certificate_855_edges 7 2 [] := by decide +kernel
theorem certificate_855_valid : certificate_855.Valid 14 7 (patternOrder [[],[],[],[],[3,4]]) (patternClique [[],[],[],[],[3,4]]) (patternEdges [[],[],[],[],[3,4]]) (patternAmount [[],[],[],[],[3,4]]) (patternEdgeCount [[],[],[],[],[3,4]]) [] := certificate_855_checked

theorem certificate_856_checked : certificate_856.Valid 14 7 9 certificate_856_q certificate_856_edges 2 2 [] := by decide +kernel
theorem certificate_856_valid : certificate_856.Valid 14 7 (patternOrder [[],[],[],[1],[1]]) (patternClique [[],[],[],[1],[1]]) (patternEdges [[],[],[],[1],[1]]) (patternAmount [[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[1],[1]]) [] := certificate_856_checked

theorem certificate_857_checked : certificate_857.Valid 14 7 10 certificate_857_q certificate_857_edges 3 2 [] := by decide +kernel
theorem certificate_857_valid : certificate_857.Valid 14 7 (patternOrder [[],[],[],[1],[2]]) (patternClique [[],[],[],[1],[2]]) (patternEdges [[],[],[],[1],[2]]) (patternAmount [[],[],[],[1],[2]]) (patternEdgeCount [[],[],[],[1],[2]]) [] := certificate_857_checked

theorem certificate_858_checked : certificate_858.Valid 14 7 11 certificate_858_q certificate_858_edges 4 2 [] := by decide +kernel
theorem certificate_858_valid : certificate_858.Valid 14 7 (patternOrder [[],[],[],[1],[3]]) (patternClique [[],[],[],[1],[3]]) (patternEdges [[],[],[],[1],[3]]) (patternAmount [[],[],[],[1],[3]]) (patternEdgeCount [[],[],[],[1],[3]]) [] := certificate_858_checked

theorem certificate_859_checked : certificate_859.Valid 14 7 12 certificate_859_q certificate_859_edges 5 2 [] := by decide +kernel
theorem certificate_859_valid : certificate_859.Valid 14 7 (patternOrder [[],[],[],[1],[4]]) (patternClique [[],[],[],[1],[4]]) (patternEdges [[],[],[],[1],[4]]) (patternAmount [[],[],[],[1],[4]]) (patternEdgeCount [[],[],[],[1],[4]]) [] := certificate_859_checked

theorem certificate_860_checked : certificate_860.Valid 14 7 13 certificate_860_q certificate_860_edges 6 2 [] := by decide +kernel
theorem certificate_860_valid : certificate_860.Valid 14 7 (patternOrder [[],[],[],[1],[5]]) (patternClique [[],[],[],[1],[5]]) (patternEdges [[],[],[],[1],[5]]) (patternAmount [[],[],[],[1],[5]]) (patternEdgeCount [[],[],[],[1],[5]]) [] := certificate_860_checked

theorem certificate_861_checked : certificate_861.Valid 14 7 14 certificate_861_q certificate_861_edges 7 2 [] := by decide +kernel
theorem certificate_861_valid : certificate_861.Valid 14 7 (patternOrder [[],[],[],[1],[6]]) (patternClique [[],[],[],[1],[6]]) (patternEdges [[],[],[],[1],[6]]) (patternAmount [[],[],[],[1],[6]]) (patternEdgeCount [[],[],[],[1],[6]]) [] := certificate_861_checked

theorem certificate_862_checked : certificate_862.Valid 14 7 10 certificate_862_q certificate_862_edges 3 3 [] := by decide +kernel
theorem certificate_862_valid : certificate_862.Valid 14 7 (patternOrder [[],[],[],[1,1,1]]) (patternClique [[],[],[],[1,1,1]]) (patternEdges [[],[],[],[1,1,1]]) (patternAmount [[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[1,1,1]]) [] := certificate_862_checked

theorem certificate_863_checked : certificate_863.Valid 14 7 11 certificate_863_q certificate_863_edges 4 3 [] := by decide +kernel
theorem certificate_863_valid : certificate_863.Valid 14 7 (patternOrder [[],[],[],[1,1,2]]) (patternClique [[],[],[],[1,1,2]]) (patternEdges [[],[],[],[1,1,2]]) (patternAmount [[],[],[],[1,1,2]]) (patternEdgeCount [[],[],[],[1,1,2]]) [] := certificate_863_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates028
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_864_checked : certificate_864.Valid 14 7 12 certificate_864_q certificate_864_edges 5 3 [] := by decide +kernel
theorem certificate_864_valid : certificate_864.Valid 14 7 (patternOrder [[],[],[],[1,1,3]]) (patternClique [[],[],[],[1,1,3]]) (patternEdges [[],[],[],[1,1,3]]) (patternAmount [[],[],[],[1,1,3]]) (patternEdgeCount [[],[],[],[1,1,3]]) [] := certificate_864_checked

theorem certificate_865_checked : certificate_865.Valid 14 7 13 certificate_865_q certificate_865_edges 6 3 [] := by decide +kernel
theorem certificate_865_valid : certificate_865.Valid 14 7 (patternOrder [[],[],[],[1,1,4]]) (patternClique [[],[],[],[1,1,4]]) (patternEdges [[],[],[],[1,1,4]]) (patternAmount [[],[],[],[1,1,4]]) (patternEdgeCount [[],[],[],[1,1,4]]) [] := certificate_865_checked

theorem certificate_866_checked : certificate_866.Valid 14 7 14 certificate_866_q certificate_866_edges 7 3 [] := by decide +kernel
theorem certificate_866_valid : certificate_866.Valid 14 7 (patternOrder [[],[],[],[1,1,5]]) (patternClique [[],[],[],[1,1,5]]) (patternEdges [[],[],[],[1,1,5]]) (patternAmount [[],[],[],[1,1,5]]) (patternEdgeCount [[],[],[],[1,1,5]]) [] := certificate_866_checked

theorem certificate_867_checked : certificate_867.Valid 14 7 11 certificate_867_q certificate_867_edges 4 3 [] := by decide +kernel
theorem certificate_867_valid : certificate_867.Valid 14 7 (patternOrder [[],[],[],[1,2,1]]) (patternClique [[],[],[],[1,2,1]]) (patternEdges [[],[],[],[1,2,1]]) (patternAmount [[],[],[],[1,2,1]]) (patternEdgeCount [[],[],[],[1,2,1]]) [] := certificate_867_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns14x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_14_7_1_verified_oai : ∀ D ∈ patterns_14_7_1, PatternVerified 14 7 D := by

  simp only [patterns_14_7_1, List.forall_mem_cons]

  exact ⟨⟨certificate_852, certificate_852_valid⟩, ⟨⟨certificate_853, certificate_853_valid⟩, ⟨⟨certificate_854, certificate_854_valid⟩, ⟨⟨certificate_855, certificate_855_valid⟩, ⟨⟨certificate_856, certificate_856_valid⟩, ⟨⟨certificate_857, certificate_857_valid⟩, ⟨⟨certificate_858, certificate_858_valid⟩, ⟨⟨certificate_859, certificate_859_valid⟩, ⟨⟨certificate_860, certificate_860_valid⟩, ⟨⟨certificate_861, certificate_861_valid⟩, ⟨⟨certificate_862, certificate_862_valid⟩, ⟨⟨certificate_863, certificate_863_valid⟩, ⟨⟨certificate_864, certificate_864_valid⟩, ⟨⟨certificate_865, certificate_865_valid⟩, ⟨⟨certificate_866, certificate_866_valid⟩, ⟨⟨certificate_867, certificate_867_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_14_7_1_verified_oai := @OAI.CycleClique.patterns_14_7_1_verified_oai
