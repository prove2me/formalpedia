-- Prove2me | solution 1 for OAI.CycleClique.patterns_14_7_0_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:07:25.076+00:00
-- url     : https://prove2.me/submissions/b7f428e5-210b-4897-a8cc-3c117598fdd2

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

theorem certificate_836_checked : certificate_836.Valid 14 7 7 certificate_836_q certificate_836_edges 0 0 [] := by decide +kernel
theorem certificate_836_valid : certificate_836.Valid 14 7 (patternOrder [[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[]]) [] := certificate_836_checked

theorem certificate_837_checked : certificate_837.Valid 14 7 8 certificate_837_q certificate_837_edges 1 1 [] := by decide +kernel
theorem certificate_837_valid : certificate_837.Valid 14 7 (patternOrder [[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[1]]) [] := certificate_837_checked

theorem certificate_838_checked : certificate_838.Valid 14 7 9 certificate_838_q certificate_838_edges 2 1 [] := by decide +kernel
theorem certificate_838_valid : certificate_838.Valid 14 7 (patternOrder [[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[2]]) [] := certificate_838_checked

theorem certificate_839_checked : certificate_839.Valid 14 7 10 certificate_839_q certificate_839_edges 3 1 [] := by decide +kernel
theorem certificate_839_valid : certificate_839.Valid 14 7 (patternOrder [[],[],[],[],[],[3]]) (patternClique [[],[],[],[],[],[3]]) (patternEdges [[],[],[],[],[],[3]]) (patternAmount [[],[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[],[3]]) [] := certificate_839_checked

theorem certificate_840_checked : certificate_840.Valid 14 7 11 certificate_840_q certificate_840_edges 4 1 [] := by decide +kernel
theorem certificate_840_valid : certificate_840.Valid 14 7 (patternOrder [[],[],[],[],[],[4]]) (patternClique [[],[],[],[],[],[4]]) (patternEdges [[],[],[],[],[],[4]]) (patternAmount [[],[],[],[],[],[4]]) (patternEdgeCount [[],[],[],[],[],[4]]) [] := certificate_840_checked

theorem certificate_841_checked : certificate_841.Valid 14 7 12 certificate_841_q certificate_841_edges 5 1 [] := by decide +kernel
theorem certificate_841_valid : certificate_841.Valid 14 7 (patternOrder [[],[],[],[],[],[5]]) (patternClique [[],[],[],[],[],[5]]) (patternEdges [[],[],[],[],[],[5]]) (patternAmount [[],[],[],[],[],[5]]) (patternEdgeCount [[],[],[],[],[],[5]]) [] := certificate_841_checked

theorem certificate_842_checked : certificate_842.Valid 14 7 13 certificate_842_q certificate_842_edges 6 1 [] := by decide +kernel
theorem certificate_842_valid : certificate_842.Valid 14 7 (patternOrder [[],[],[],[],[],[6]]) (patternClique [[],[],[],[],[],[6]]) (patternEdges [[],[],[],[],[],[6]]) (patternAmount [[],[],[],[],[],[6]]) (patternEdgeCount [[],[],[],[],[],[6]]) [] := certificate_842_checked

theorem certificate_843_checked : certificate_843.Valid 14 7 14 certificate_843_q certificate_843_edges 7 1 [] := by decide +kernel
theorem certificate_843_valid : certificate_843.Valid 14 7 (patternOrder [[],[],[],[],[],[7]]) (patternClique [[],[],[],[],[],[7]]) (patternEdges [[],[],[],[],[],[7]]) (patternAmount [[],[],[],[],[],[7]]) (patternEdgeCount [[],[],[],[],[],[7]]) [] := certificate_843_checked

theorem certificate_844_checked : certificate_844.Valid 14 7 9 certificate_844_q certificate_844_edges 2 2 [] := by decide +kernel
theorem certificate_844_valid : certificate_844.Valid 14 7 (patternOrder [[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[1,1]]) [] := certificate_844_checked

theorem certificate_845_checked : certificate_845.Valid 14 7 10 certificate_845_q certificate_845_edges 3 2 [] := by decide +kernel
theorem certificate_845_valid : certificate_845.Valid 14 7 (patternOrder [[],[],[],[],[1,2]]) (patternClique [[],[],[],[],[1,2]]) (patternEdges [[],[],[],[],[1,2]]) (patternAmount [[],[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[],[1,2]]) [] := certificate_845_checked

theorem certificate_846_checked : certificate_846.Valid 14 7 11 certificate_846_q certificate_846_edges 4 2 [] := by decide +kernel
theorem certificate_846_valid : certificate_846.Valid 14 7 (patternOrder [[],[],[],[],[1,3]]) (patternClique [[],[],[],[],[1,3]]) (patternEdges [[],[],[],[],[1,3]]) (patternAmount [[],[],[],[],[1,3]]) (patternEdgeCount [[],[],[],[],[1,3]]) [] := certificate_846_checked

theorem certificate_847_checked : certificate_847.Valid 14 7 12 certificate_847_q certificate_847_edges 5 2 [] := by decide +kernel
theorem certificate_847_valid : certificate_847.Valid 14 7 (patternOrder [[],[],[],[],[1,4]]) (patternClique [[],[],[],[],[1,4]]) (patternEdges [[],[],[],[],[1,4]]) (patternAmount [[],[],[],[],[1,4]]) (patternEdgeCount [[],[],[],[],[1,4]]) [] := certificate_847_checked

theorem certificate_848_checked : certificate_848.Valid 14 7 13 certificate_848_q certificate_848_edges 6 2 [] := by decide +kernel
theorem certificate_848_valid : certificate_848.Valid 14 7 (patternOrder [[],[],[],[],[1,5]]) (patternClique [[],[],[],[],[1,5]]) (patternEdges [[],[],[],[],[1,5]]) (patternAmount [[],[],[],[],[1,5]]) (patternEdgeCount [[],[],[],[],[1,5]]) [] := certificate_848_checked

theorem certificate_849_checked : certificate_849.Valid 14 7 14 certificate_849_q certificate_849_edges 7 2 [] := by decide +kernel
theorem certificate_849_valid : certificate_849.Valid 14 7 (patternOrder [[],[],[],[],[1,6]]) (patternClique [[],[],[],[],[1,6]]) (patternEdges [[],[],[],[],[1,6]]) (patternAmount [[],[],[],[],[1,6]]) (patternEdgeCount [[],[],[],[],[1,6]]) [] := certificate_849_checked

theorem certificate_850_checked : certificate_850.Valid 14 7 11 certificate_850_q certificate_850_edges 4 2 [] := by decide +kernel
theorem certificate_850_valid : certificate_850.Valid 14 7 (patternOrder [[],[],[],[],[2,2]]) (patternClique [[],[],[],[],[2,2]]) (patternEdges [[],[],[],[],[2,2]]) (patternAmount [[],[],[],[],[2,2]]) (patternEdgeCount [[],[],[],[],[2,2]]) [] := certificate_850_checked

theorem certificate_851_checked : certificate_851.Valid 14 7 12 certificate_851_q certificate_851_edges 5 2 [] := by decide +kernel
theorem certificate_851_valid : certificate_851.Valid 14 7 (patternOrder [[],[],[],[],[2,3]]) (patternClique [[],[],[],[],[2,3]]) (patternEdges [[],[],[],[],[2,3]]) (patternAmount [[],[],[],[],[2,3]]) (patternEdgeCount [[],[],[],[],[2,3]]) [] := certificate_851_checked

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

theorem patterns_14_7_0_verified_oai : ∀ D ∈ patterns_14_7_0, PatternVerified 14 7 D := by

  simp only [patterns_14_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_836, certificate_836_valid⟩, ⟨⟨certificate_837, certificate_837_valid⟩, ⟨⟨certificate_838, certificate_838_valid⟩, ⟨⟨certificate_839, certificate_839_valid⟩, ⟨⟨certificate_840, certificate_840_valid⟩, ⟨⟨certificate_841, certificate_841_valid⟩, ⟨⟨certificate_842, certificate_842_valid⟩, ⟨⟨certificate_843, certificate_843_valid⟩, ⟨⟨certificate_844, certificate_844_valid⟩, ⟨⟨certificate_845, certificate_845_valid⟩, ⟨⟨certificate_846, certificate_846_valid⟩, ⟨⟨certificate_847, certificate_847_valid⟩, ⟨⟨certificate_848, certificate_848_valid⟩, ⟨⟨certificate_849, certificate_849_valid⟩, ⟨⟨certificate_850, certificate_850_valid⟩, ⟨⟨certificate_851, certificate_851_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_14_7_0_verified_oai := @OAI.CycleClique.patterns_14_7_0_verified_oai
