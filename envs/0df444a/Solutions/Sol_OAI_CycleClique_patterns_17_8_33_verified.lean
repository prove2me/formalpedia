-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_33_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:32:08.700274+00:00
-- url     : https://prove2.me/submissions/0cf43e6e-415e-40db-b593-51bc094bedfe

import Mathlib
import Definitions.Def_OAIQ107D005
import Definitions.Def_OAIQ107D091
import Definitions.Def_OAIQ107D092
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates086
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2748_checked : certificate_2748.Valid 17 8 14 certificate_2748_q certificate_2748_edges 6 6 [] := by decide +kernel
theorem certificate_2748_valid : certificate_2748.Valid 17 8 (patternOrder [[],[1,1,1,1,1,1]]) (patternClique [[],[1,1,1,1,1,1]]) (patternEdges [[],[1,1,1,1,1,1]]) (patternAmount [[],[1,1,1,1,1,1]]) (patternEdgeCount [[],[1,1,1,1,1,1]]) [] := certificate_2748_checked

theorem certificate_2749_checked : certificate_2749.Valid 17 8 15 certificate_2749_q certificate_2749_edges 7 6 [] := by decide +kernel
theorem certificate_2749_valid : certificate_2749.Valid 17 8 (patternOrder [[],[1,1,1,1,1,2]]) (patternClique [[],[1,1,1,1,1,2]]) (patternEdges [[],[1,1,1,1,1,2]]) (patternAmount [[],[1,1,1,1,1,2]]) (patternEdgeCount [[],[1,1,1,1,1,2]]) [] := certificate_2749_checked

theorem certificate_2750_checked : certificate_2750.Valid 17 8 16 certificate_2750_q certificate_2750_edges 8 6 [] := by decide +kernel
theorem certificate_2750_valid : certificate_2750.Valid 17 8 (patternOrder [[],[1,1,1,1,1,3]]) (patternClique [[],[1,1,1,1,1,3]]) (patternEdges [[],[1,1,1,1,1,3]]) (patternAmount [[],[1,1,1,1,1,3]]) (patternEdgeCount [[],[1,1,1,1,1,3]]) [] := certificate_2750_checked

theorem certificate_2751_checked : certificate_2751.Valid 17 8 17 certificate_2751_q certificate_2751_edges 9 6 [] := by decide +kernel
theorem certificate_2751_valid : certificate_2751.Valid 17 8 (patternOrder [[],[1,1,1,1,1,4]]) (patternClique [[],[1,1,1,1,1,4]]) (patternEdges [[],[1,1,1,1,1,4]]) (patternAmount [[],[1,1,1,1,1,4]]) (patternEdgeCount [[],[1,1,1,1,1,4]]) [] := certificate_2751_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates087
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2752_checked : certificate_2752.Valid 17 8 15 certificate_2752_q certificate_2752_edges 7 6 [] := by decide +kernel
theorem certificate_2752_valid : certificate_2752.Valid 17 8 (patternOrder [[],[1,1,1,1,2,1]]) (patternClique [[],[1,1,1,1,2,1]]) (patternEdges [[],[1,1,1,1,2,1]]) (patternAmount [[],[1,1,1,1,2,1]]) (patternEdgeCount [[],[1,1,1,1,2,1]]) [] := certificate_2752_checked

theorem certificate_2753_checked : certificate_2753.Valid 17 8 16 certificate_2753_q certificate_2753_edges 8 6 [] := by decide +kernel
theorem certificate_2753_valid : certificate_2753.Valid 17 8 (patternOrder [[],[1,1,1,1,2,2]]) (patternClique [[],[1,1,1,1,2,2]]) (patternEdges [[],[1,1,1,1,2,2]]) (patternAmount [[],[1,1,1,1,2,2]]) (patternEdgeCount [[],[1,1,1,1,2,2]]) [] := certificate_2753_checked

theorem certificate_2754_checked : certificate_2754.Valid 17 8 17 certificate_2754_q certificate_2754_edges 9 6 [] := by decide +kernel
theorem certificate_2754_valid : certificate_2754.Valid 17 8 (patternOrder [[],[1,1,1,1,2,3]]) (patternClique [[],[1,1,1,1,2,3]]) (patternEdges [[],[1,1,1,1,2,3]]) (patternAmount [[],[1,1,1,1,2,3]]) (patternEdgeCount [[],[1,1,1,1,2,3]]) [] := certificate_2754_checked

theorem certificate_2755_checked : certificate_2755.Valid 17 8 16 certificate_2755_q certificate_2755_edges 8 6 [] := by decide +kernel
theorem certificate_2755_valid : certificate_2755.Valid 17 8 (patternOrder [[],[1,1,1,1,3,1]]) (patternClique [[],[1,1,1,1,3,1]]) (patternEdges [[],[1,1,1,1,3,1]]) (patternAmount [[],[1,1,1,1,3,1]]) (patternEdgeCount [[],[1,1,1,1,3,1]]) [] := certificate_2755_checked

theorem certificate_2756_checked : certificate_2756.Valid 17 8 17 certificate_2756_q certificate_2756_edges 9 6 [] := by decide +kernel
theorem certificate_2756_valid : certificate_2756.Valid 17 8 (patternOrder [[],[1,1,1,1,3,2]]) (patternClique [[],[1,1,1,1,3,2]]) (patternEdges [[],[1,1,1,1,3,2]]) (patternAmount [[],[1,1,1,1,3,2]]) (patternEdgeCount [[],[1,1,1,1,3,2]]) [] := certificate_2756_checked

theorem certificate_2757_checked : certificate_2757.Valid 17 8 17 certificate_2757_q certificate_2757_edges 9 6 [] := by decide +kernel
theorem certificate_2757_valid : certificate_2757.Valid 17 8 (patternOrder [[],[1,1,1,1,4,1]]) (patternClique [[],[1,1,1,1,4,1]]) (patternEdges [[],[1,1,1,1,4,1]]) (patternAmount [[],[1,1,1,1,4,1]]) (patternEdgeCount [[],[1,1,1,1,4,1]]) [] := certificate_2757_checked

theorem certificate_2758_checked : certificate_2758.Valid 17 8 15 certificate_2758_q certificate_2758_edges 7 5 [] := by decide +kernel
theorem certificate_2758_valid : certificate_2758.Valid 17 8 (patternOrder [[],[1,1,1,2],[2]]) (patternClique [[],[1,1,1,2],[2]]) (patternEdges [[],[1,1,1,2],[2]]) (patternAmount [[],[1,1,1,2],[2]]) (patternEdgeCount [[],[1,1,1,2],[2]]) [] := certificate_2758_checked

theorem certificate_2759_checked : certificate_2759.Valid 17 8 16 certificate_2759_q certificate_2759_edges 8 5 [] := by decide +kernel
theorem certificate_2759_valid : certificate_2759.Valid 17 8 (patternOrder [[],[1,1,1,2],[3]]) (patternClique [[],[1,1,1,2],[3]]) (patternEdges [[],[1,1,1,2],[3]]) (patternAmount [[],[1,1,1,2],[3]]) (patternEdgeCount [[],[1,1,1,2],[3]]) [] := certificate_2759_checked

theorem certificate_2760_checked : certificate_2760.Valid 17 8 17 certificate_2760_q certificate_2760_edges 9 5 [] := by decide +kernel
theorem certificate_2760_valid : certificate_2760.Valid 17 8 (patternOrder [[],[1,1,1,2],[4]]) (patternClique [[],[1,1,1,2],[4]]) (patternEdges [[],[1,1,1,2],[4]]) (patternAmount [[],[1,1,1,2],[4]]) (patternEdgeCount [[],[1,1,1,2],[4]]) [] := certificate_2760_checked

theorem certificate_2761_checked : certificate_2761.Valid 17 8 15 certificate_2761_q certificate_2761_edges 7 6 [] := by decide +kernel
theorem certificate_2761_valid : certificate_2761.Valid 17 8 (patternOrder [[],[1,1,1,2,1,1]]) (patternClique [[],[1,1,1,2,1,1]]) (patternEdges [[],[1,1,1,2,1,1]]) (patternAmount [[],[1,1,1,2,1,1]]) (patternEdgeCount [[],[1,1,1,2,1,1]]) [] := certificate_2761_checked

theorem certificate_2762_checked : certificate_2762.Valid 17 8 16 certificate_2762_q certificate_2762_edges 8 6 [] := by decide +kernel
theorem certificate_2762_valid : certificate_2762.Valid 17 8 (patternOrder [[],[1,1,1,2,1,2]]) (patternClique [[],[1,1,1,2,1,2]]) (patternEdges [[],[1,1,1,2,1,2]]) (patternAmount [[],[1,1,1,2,1,2]]) (patternEdgeCount [[],[1,1,1,2,1,2]]) [] := certificate_2762_checked

theorem certificate_2763_checked : certificate_2763.Valid 17 8 17 certificate_2763_q certificate_2763_edges 9 6 [] := by decide +kernel
theorem certificate_2763_valid : certificate_2763.Valid 17 8 (patternOrder [[],[1,1,1,2,1,3]]) (patternClique [[],[1,1,1,2,1,3]]) (patternEdges [[],[1,1,1,2,1,3]]) (patternAmount [[],[1,1,1,2,1,3]]) (patternEdgeCount [[],[1,1,1,2,1,3]]) [] := certificate_2763_checked

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

theorem patterns_17_8_33_verified_oai : ∀ D ∈ patterns_17_8_33, PatternVerified 17 8 D := by

  simp only [patterns_17_8_33, List.forall_mem_cons]

  exact ⟨⟨certificate_2748, certificate_2748_valid⟩, ⟨⟨certificate_2749, certificate_2749_valid⟩, ⟨⟨certificate_2750, certificate_2750_valid⟩, ⟨⟨certificate_2751, certificate_2751_valid⟩, ⟨⟨certificate_2752, certificate_2752_valid⟩, ⟨⟨certificate_2753, certificate_2753_valid⟩, ⟨⟨certificate_2754, certificate_2754_valid⟩, ⟨⟨certificate_2755, certificate_2755_valid⟩, ⟨⟨certificate_2756, certificate_2756_valid⟩, ⟨⟨certificate_2757, certificate_2757_valid⟩, ⟨⟨certificate_2758, certificate_2758_valid⟩, ⟨⟨certificate_2759, certificate_2759_valid⟩, ⟨⟨certificate_2760, certificate_2760_valid⟩, ⟨⟨certificate_2761, certificate_2761_valid⟩, ⟨⟨certificate_2762, certificate_2762_valid⟩, ⟨⟨certificate_2763, certificate_2763_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_33_verified_oai := @OAI.CycleClique.patterns_17_8_33_verified_oai
