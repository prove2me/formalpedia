-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_35_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:20:54.99268+00:00
-- url     : https://prove2.me/submissions/8c40088b-769b-4729-b2f1-2c7da292288e

import Mathlib
import Definitions.Def_OAIQ107D133
import Definitions.Def_OAIQ107D134

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates087
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2780_checked : certificate_2780.Valid 17 8 16 certificate_2780_q certificate_2780_edges 8 5 [] := by decide +kernel
theorem certificate_2780_valid : certificate_2780.Valid 17 8 (patternOrder [[],[1,1,2,1],[3]]) (patternClique [[],[1,1,2,1],[3]]) (patternEdges [[],[1,1,2,1],[3]]) (patternAmount [[],[1,1,2,1],[3]]) (patternEdgeCount [[],[1,1,2,1],[3]]) [] := certificate_2780_checked

theorem certificate_2781_checked : certificate_2781.Valid 17 8 17 certificate_2781_q certificate_2781_edges 9 5 [] := by decide +kernel
theorem certificate_2781_valid : certificate_2781.Valid 17 8 (patternOrder [[],[1,1,2,1],[4]]) (patternClique [[],[1,1,2,1],[4]]) (patternEdges [[],[1,1,2,1],[4]]) (patternAmount [[],[1,1,2,1],[4]]) (patternEdgeCount [[],[1,1,2,1],[4]]) [] := certificate_2781_checked

theorem certificate_2782_checked : certificate_2782.Valid 17 8 16 certificate_2782_q certificate_2782_edges 8 6 [] := by decide +kernel
theorem certificate_2782_valid : certificate_2782.Valid 17 8 (patternOrder [[],[1,1,2,1,1,2]]) (patternClique [[],[1,1,2,1,1,2]]) (patternEdges [[],[1,1,2,1,1,2]]) (patternAmount [[],[1,1,2,1,1,2]]) (patternEdgeCount [[],[1,1,2,1,1,2]]) [] := certificate_2782_checked

theorem certificate_2783_checked : certificate_2783.Valid 17 8 17 certificate_2783_q certificate_2783_edges 9 6 [] := by decide +kernel
theorem certificate_2783_valid : certificate_2783.Valid 17 8 (patternOrder [[],[1,1,2,1,1,3]]) (patternClique [[],[1,1,2,1,1,3]]) (patternEdges [[],[1,1,2,1,1,3]]) (patternAmount [[],[1,1,2,1,1,3]]) (patternEdgeCount [[],[1,1,2,1,1,3]]) [] := certificate_2783_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates088
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2784_checked : certificate_2784.Valid 17 8 16 certificate_2784_q certificate_2784_edges 8 6 [] := by decide +kernel
theorem certificate_2784_valid : certificate_2784.Valid 17 8 (patternOrder [[],[1,1,2,1,2,1]]) (patternClique [[],[1,1,2,1,2,1]]) (patternEdges [[],[1,1,2,1,2,1]]) (patternAmount [[],[1,1,2,1,2,1]]) (patternEdgeCount [[],[1,1,2,1,2,1]]) [] := certificate_2784_checked

theorem certificate_2785_checked : certificate_2785.Valid 17 8 17 certificate_2785_q certificate_2785_edges 9 6 [] := by decide +kernel
theorem certificate_2785_valid : certificate_2785.Valid 17 8 (patternOrder [[],[1,1,2,1,2,2]]) (patternClique [[],[1,1,2,1,2,2]]) (patternEdges [[],[1,1,2,1,2,2]]) (patternAmount [[],[1,1,2,1,2,2]]) (patternEdgeCount [[],[1,1,2,1,2,2]]) [] := certificate_2785_checked

theorem certificate_2786_checked : certificate_2786.Valid 17 8 17 certificate_2786_q certificate_2786_edges 9 6 [] := by decide +kernel
theorem certificate_2786_valid : certificate_2786.Valid 17 8 (patternOrder [[],[1,1,2,1,3,1]]) (patternClique [[],[1,1,2,1,3,1]]) (patternEdges [[],[1,1,2,1,3,1]]) (patternAmount [[],[1,1,2,1,3,1]]) (patternEdgeCount [[],[1,1,2,1,3,1]]) [] := certificate_2786_checked

theorem certificate_2787_checked : certificate_2787.Valid 17 8 16 certificate_2787_q certificate_2787_edges 8 5 [] := by decide +kernel
theorem certificate_2787_valid : certificate_2787.Valid 17 8 (patternOrder [[],[1,1,2,2],[2]]) (patternClique [[],[1,1,2,2],[2]]) (patternEdges [[],[1,1,2,2],[2]]) (patternAmount [[],[1,1,2,2],[2]]) (patternEdgeCount [[],[1,1,2,2],[2]]) [] := certificate_2787_checked

theorem certificate_2788_checked : certificate_2788.Valid 17 8 17 certificate_2788_q certificate_2788_edges 9 5 [] := by decide +kernel
theorem certificate_2788_valid : certificate_2788.Valid 17 8 (patternOrder [[],[1,1,2,2],[3]]) (patternClique [[],[1,1,2,2],[3]]) (patternEdges [[],[1,1,2,2],[3]]) (patternAmount [[],[1,1,2,2],[3]]) (patternEdgeCount [[],[1,1,2,2],[3]]) [] := certificate_2788_checked

theorem certificate_2789_checked : certificate_2789.Valid 17 8 16 certificate_2789_q certificate_2789_edges 8 6 [] := by decide +kernel
theorem certificate_2789_valid : certificate_2789.Valid 17 8 (patternOrder [[],[1,1,2,2,1,1]]) (patternClique [[],[1,1,2,2,1,1]]) (patternEdges [[],[1,1,2,2,1,1]]) (patternAmount [[],[1,1,2,2,1,1]]) (patternEdgeCount [[],[1,1,2,2,1,1]]) [] := certificate_2789_checked

theorem certificate_2790_checked : certificate_2790.Valid 17 8 17 certificate_2790_q certificate_2790_edges 9 6 [] := by decide +kernel
theorem certificate_2790_valid : certificate_2790.Valid 17 8 (patternOrder [[],[1,1,2,2,1,2]]) (patternClique [[],[1,1,2,2,1,2]]) (patternEdges [[],[1,1,2,2,1,2]]) (patternAmount [[],[1,1,2,2,1,2]]) (patternEdgeCount [[],[1,1,2,2,1,2]]) [] := certificate_2790_checked

theorem certificate_2791_checked : certificate_2791.Valid 17 8 17 certificate_2791_q certificate_2791_edges 9 6 [] := by decide +kernel
theorem certificate_2791_valid : certificate_2791.Valid 17 8 (patternOrder [[],[1,1,2,2,2,1]]) (patternClique [[],[1,1,2,2,2,1]]) (patternEdges [[],[1,1,2,2,2,1]]) (patternAmount [[],[1,1,2,2,2,1]]) (patternEdgeCount [[],[1,1,2,2,2,1]]) [] := certificate_2791_checked

theorem certificate_2792_checked : certificate_2792.Valid 17 8 17 certificate_2792_q certificate_2792_edges 9 5 [] := by decide +kernel
theorem certificate_2792_valid : certificate_2792.Valid 17 8 (patternOrder [[],[1,1,2,3],[2]]) (patternClique [[],[1,1,2,3],[2]]) (patternEdges [[],[1,1,2,3],[2]]) (patternAmount [[],[1,1,2,3],[2]]) (patternEdgeCount [[],[1,1,2,3],[2]]) [] := certificate_2792_checked

theorem certificate_2793_checked : certificate_2793.Valid 17 8 17 certificate_2793_q certificate_2793_edges 9 6 [] := by decide +kernel
theorem certificate_2793_valid : certificate_2793.Valid 17 8 (patternOrder [[],[1,1,2,3,1,1]]) (patternClique [[],[1,1,2,3,1,1]]) (patternEdges [[],[1,1,2,3,1,1]]) (patternAmount [[],[1,1,2,3,1,1]]) (patternEdgeCount [[],[1,1,2,3,1,1]]) [] := certificate_2793_checked

theorem certificate_2794_checked : certificate_2794.Valid 17 8 16 certificate_2794_q certificate_2794_edges 8 5 [] := by decide +kernel
theorem certificate_2794_valid : certificate_2794.Valid 17 8 (patternOrder [[],[1,1,3],[1,2]]) (patternClique [[],[1,1,3],[1,2]]) (patternEdges [[],[1,1,3],[1,2]]) (patternAmount [[],[1,1,3],[1,2]]) (patternEdgeCount [[],[1,1,3],[1,2]]) [] := certificate_2794_checked

theorem certificate_2795_checked : certificate_2795.Valid 17 8 17 certificate_2795_q certificate_2795_edges 9 5 [] := by decide +kernel
theorem certificate_2795_valid : certificate_2795.Valid 17 8 (patternOrder [[],[1,1,3],[1,3]]) (patternClique [[],[1,1,3],[1,3]]) (patternEdges [[],[1,1,3],[1,3]]) (patternAmount [[],[1,1,3],[1,3]]) (patternEdgeCount [[],[1,1,3],[1,3]]) [] := certificate_2795_checked

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

theorem patterns_17_8_35_verified_oai : ∀ D ∈ patterns_17_8_35, PatternVerified 17 8 D := by

  simp only [patterns_17_8_35, List.forall_mem_cons]

  exact ⟨⟨certificate_2780, certificate_2780_valid⟩, ⟨⟨certificate_2781, certificate_2781_valid⟩, ⟨⟨certificate_2782, certificate_2782_valid⟩, ⟨⟨certificate_2783, certificate_2783_valid⟩, ⟨⟨certificate_2784, certificate_2784_valid⟩, ⟨⟨certificate_2785, certificate_2785_valid⟩, ⟨⟨certificate_2786, certificate_2786_valid⟩, ⟨⟨certificate_2787, certificate_2787_valid⟩, ⟨⟨certificate_2788, certificate_2788_valid⟩, ⟨⟨certificate_2789, certificate_2789_valid⟩, ⟨⟨certificate_2790, certificate_2790_valid⟩, ⟨⟨certificate_2791, certificate_2791_valid⟩, ⟨⟨certificate_2792, certificate_2792_valid⟩, ⟨⟨certificate_2793, certificate_2793_valid⟩, ⟨⟨certificate_2794, certificate_2794_valid⟩, ⟨⟨certificate_2795, certificate_2795_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_35_verified_oai := @OAI.CycleClique.patterns_17_8_35_verified_oai
