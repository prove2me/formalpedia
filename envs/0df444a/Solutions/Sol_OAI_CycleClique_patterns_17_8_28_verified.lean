-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_28_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:26:15.562605+00:00
-- url     : https://prove2.me/submissions/1066ae32-b634-486b-b29b-d14b980a7ba1

import Mathlib
import Definitions.Def_OAIQ107D005
import Definitions.Def_OAIQ107D088
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates084
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2668_checked : certificate_2668.Valid 17 8 14 certificate_2668_q certificate_2668_edges 6 4 [] := by decide +kernel
theorem certificate_2668_valid : certificate_2668.Valid 17 8 (patternOrder [[],[1],[1,2],[2]]) (patternClique [[],[1],[1,2],[2]]) (patternEdges [[],[1],[1,2],[2]]) (patternAmount [[],[1],[1,2],[2]]) (patternEdgeCount [[],[1],[1,2],[2]]) [] := certificate_2668_checked

theorem certificate_2669_checked : certificate_2669.Valid 17 8 15 certificate_2669_q certificate_2669_edges 7 4 [] := by decide +kernel
theorem certificate_2669_valid : certificate_2669.Valid 17 8 (patternOrder [[],[1],[1,2],[3]]) (patternClique [[],[1],[1,2],[3]]) (patternEdges [[],[1],[1,2],[3]]) (patternAmount [[],[1],[1,2],[3]]) (patternEdgeCount [[],[1],[1,2],[3]]) [] := certificate_2669_checked

theorem certificate_2670_checked : certificate_2670.Valid 17 8 16 certificate_2670_q certificate_2670_edges 8 4 [] := by decide +kernel
theorem certificate_2670_valid : certificate_2670.Valid 17 8 (patternOrder [[],[1],[1,2],[4]]) (patternClique [[],[1],[1,2],[4]]) (patternEdges [[],[1],[1,2],[4]]) (patternAmount [[],[1],[1,2],[4]]) (patternEdgeCount [[],[1],[1,2],[4]]) [] := certificate_2670_checked

theorem certificate_2671_checked : certificate_2671.Valid 17 8 17 certificate_2671_q certificate_2671_edges 9 4 [] := by decide +kernel
theorem certificate_2671_valid : certificate_2671.Valid 17 8 (patternOrder [[],[1],[1,2],[5]]) (patternClique [[],[1],[1,2],[5]]) (patternEdges [[],[1],[1,2],[5]]) (patternAmount [[],[1],[1,2],[5]]) (patternEdgeCount [[],[1],[1,2],[5]]) [] := certificate_2671_checked

theorem certificate_2672_checked : certificate_2672.Valid 17 8 15 certificate_2672_q certificate_2672_edges 7 5 [] := by decide +kernel
theorem certificate_2672_valid : certificate_2672.Valid 17 8 (patternOrder [[],[1],[1,2,1,2]]) (patternClique [[],[1],[1,2,1,2]]) (patternEdges [[],[1],[1,2,1,2]]) (patternAmount [[],[1],[1,2,1,2]]) (patternEdgeCount [[],[1],[1,2,1,2]]) [] := certificate_2672_checked

theorem certificate_2673_checked : certificate_2673.Valid 17 8 16 certificate_2673_q certificate_2673_edges 8 5 [] := by decide +kernel
theorem certificate_2673_valid : certificate_2673.Valid 17 8 (patternOrder [[],[1],[1,2,1,3]]) (patternClique [[],[1],[1,2,1,3]]) (patternEdges [[],[1],[1,2,1,3]]) (patternAmount [[],[1],[1,2,1,3]]) (patternEdgeCount [[],[1],[1,2,1,3]]) [] := certificate_2673_checked

theorem certificate_2674_checked : certificate_2674.Valid 17 8 17 certificate_2674_q certificate_2674_edges 9 5 [] := by decide +kernel
theorem certificate_2674_valid : certificate_2674.Valid 17 8 (patternOrder [[],[1],[1,2,1,4]]) (patternClique [[],[1],[1,2,1,4]]) (patternEdges [[],[1],[1,2,1,4]]) (patternAmount [[],[1],[1,2,1,4]]) (patternEdgeCount [[],[1],[1,2,1,4]]) [] := certificate_2674_checked

theorem certificate_2675_checked : certificate_2675.Valid 17 8 15 certificate_2675_q certificate_2675_edges 7 5 [] := by decide +kernel
theorem certificate_2675_valid : certificate_2675.Valid 17 8 (patternOrder [[],[1],[1,2,2,1]]) (patternClique [[],[1],[1,2,2,1]]) (patternEdges [[],[1],[1,2,2,1]]) (patternAmount [[],[1],[1,2,2,1]]) (patternEdgeCount [[],[1],[1,2,2,1]]) [] := certificate_2675_checked

theorem certificate_2676_checked : certificate_2676.Valid 17 8 16 certificate_2676_q certificate_2676_edges 8 5 [] := by decide +kernel
theorem certificate_2676_valid : certificate_2676.Valid 17 8 (patternOrder [[],[1],[1,2,2,2]]) (patternClique [[],[1],[1,2,2,2]]) (patternEdges [[],[1],[1,2,2,2]]) (patternAmount [[],[1],[1,2,2,2]]) (patternEdgeCount [[],[1],[1,2,2,2]]) [] := certificate_2676_checked

theorem certificate_2677_checked : certificate_2677.Valid 17 8 17 certificate_2677_q certificate_2677_edges 9 5 [] := by decide +kernel
theorem certificate_2677_valid : certificate_2677.Valid 17 8 (patternOrder [[],[1],[1,2,2,3]]) (patternClique [[],[1],[1,2,2,3]]) (patternEdges [[],[1],[1,2,2,3]]) (patternAmount [[],[1],[1,2,2,3]]) (patternEdgeCount [[],[1],[1,2,2,3]]) [] := certificate_2677_checked

theorem certificate_2678_checked : certificate_2678.Valid 17 8 16 certificate_2678_q certificate_2678_edges 8 5 [] := by decide +kernel
theorem certificate_2678_valid : certificate_2678.Valid 17 8 (patternOrder [[],[1],[1,2,3,1]]) (patternClique [[],[1],[1,2,3,1]]) (patternEdges [[],[1],[1,2,3,1]]) (patternAmount [[],[1],[1,2,3,1]]) (patternEdgeCount [[],[1],[1,2,3,1]]) [] := certificate_2678_checked

theorem certificate_2679_checked : certificate_2679.Valid 17 8 17 certificate_2679_q certificate_2679_edges 9 5 [] := by decide +kernel
theorem certificate_2679_valid : certificate_2679.Valid 17 8 (patternOrder [[],[1],[1,2,3,2]]) (patternClique [[],[1],[1,2,3,2]]) (patternEdges [[],[1],[1,2,3,2]]) (patternAmount [[],[1],[1,2,3,2]]) (patternEdgeCount [[],[1],[1,2,3,2]]) [] := certificate_2679_checked

theorem certificate_2680_checked : certificate_2680.Valid 17 8 17 certificate_2680_q certificate_2680_edges 9 5 [] := by decide +kernel
theorem certificate_2680_valid : certificate_2680.Valid 17 8 (patternOrder [[],[1],[1,2,4,1]]) (patternClique [[],[1],[1,2,4,1]]) (patternEdges [[],[1],[1,2,4,1]]) (patternAmount [[],[1],[1,2,4,1]]) (patternEdgeCount [[],[1],[1,2,4,1]]) [] := certificate_2680_checked

theorem certificate_2681_checked : certificate_2681.Valid 17 8 15 certificate_2681_q certificate_2681_edges 7 4 [] := by decide +kernel
theorem certificate_2681_valid : certificate_2681.Valid 17 8 (patternOrder [[],[1],[1,3],[2]]) (patternClique [[],[1],[1,3],[2]]) (patternEdges [[],[1],[1,3],[2]]) (patternAmount [[],[1],[1,3],[2]]) (patternEdgeCount [[],[1],[1,3],[2]]) [] := certificate_2681_checked

theorem certificate_2682_checked : certificate_2682.Valid 17 8 16 certificate_2682_q certificate_2682_edges 8 4 [] := by decide +kernel
theorem certificate_2682_valid : certificate_2682.Valid 17 8 (patternOrder [[],[1],[1,3],[3]]) (patternClique [[],[1],[1,3],[3]]) (patternEdges [[],[1],[1,3],[3]]) (patternAmount [[],[1],[1,3],[3]]) (patternEdgeCount [[],[1],[1,3],[3]]) [] := certificate_2682_checked

theorem certificate_2683_checked : certificate_2683.Valid 17 8 17 certificate_2683_q certificate_2683_edges 9 4 [] := by decide +kernel
theorem certificate_2683_valid : certificate_2683.Valid 17 8 (patternOrder [[],[1],[1,3],[4]]) (patternClique [[],[1],[1,3],[4]]) (patternEdges [[],[1],[1,3],[4]]) (patternAmount [[],[1],[1,3],[4]]) (patternEdgeCount [[],[1],[1,3],[4]]) [] := certificate_2683_checked

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

theorem patterns_17_8_28_verified_oai : ∀ D ∈ patterns_17_8_28, PatternVerified 17 8 D := by

  simp only [patterns_17_8_28, List.forall_mem_cons]

  exact ⟨⟨certificate_2668, certificate_2668_valid⟩, ⟨⟨certificate_2669, certificate_2669_valid⟩, ⟨⟨certificate_2670, certificate_2670_valid⟩, ⟨⟨certificate_2671, certificate_2671_valid⟩, ⟨⟨certificate_2672, certificate_2672_valid⟩, ⟨⟨certificate_2673, certificate_2673_valid⟩, ⟨⟨certificate_2674, certificate_2674_valid⟩, ⟨⟨certificate_2675, certificate_2675_valid⟩, ⟨⟨certificate_2676, certificate_2676_valid⟩, ⟨⟨certificate_2677, certificate_2677_valid⟩, ⟨⟨certificate_2678, certificate_2678_valid⟩, ⟨⟨certificate_2679, certificate_2679_valid⟩, ⟨⟨certificate_2680, certificate_2680_valid⟩, ⟨⟨certificate_2681, certificate_2681_valid⟩, ⟨⟨certificate_2682, certificate_2682_valid⟩, ⟨⟨certificate_2683, certificate_2683_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_28_verified_oai := @OAI.CycleClique.patterns_17_8_28_verified_oai
