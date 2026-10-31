-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_39_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:35:29.418119+00:00
-- url     : https://prove2.me/submissions/95a4835a-9b49-457b-8a8e-963bd51e2f40

import Mathlib
import Definitions.Def_OAIQ107D095
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates089
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2844_checked : certificate_2844.Valid 17 8 17 certificate_2844_q certificate_2844_edges 9 5 [] := by decide +kernel
theorem certificate_2844_valid : certificate_2844.Valid 17 8 (patternOrder [[],[1,3,1,2],[2]]) (patternClique [[],[1,3,1,2],[2]]) (patternEdges [[],[1,3,1,2],[2]]) (patternAmount [[],[1,3,1,2],[2]]) (patternEdgeCount [[],[1,3,1,2],[2]]) [] := certificate_2844_checked

theorem certificate_2845_checked : certificate_2845.Valid 17 8 17 certificate_2845_q certificate_2845_edges 9 4 [] := by decide +kernel
theorem certificate_2845_valid : certificate_2845.Valid 17 8 (patternOrder [[],[1,4],[2],[2]]) (patternClique [[],[1,4],[2],[2]]) (patternEdges [[],[1,4],[2],[2]]) (patternAmount [[],[1,4],[2],[2]]) (patternEdgeCount [[],[1,4],[2],[2]]) [] := certificate_2845_checked

theorem certificate_2846_checked : certificate_2846.Valid 17 8 16 certificate_2846_q certificate_2846_edges 8 4 [] := by decide +kernel
theorem certificate_2846_valid : certificate_2846.Valid 17 8 (patternOrder [[],[2],[2],[2,2]]) (patternClique [[],[2],[2],[2,2]]) (patternEdges [[],[2],[2],[2,2]]) (patternAmount [[],[2],[2],[2,2]]) (patternEdgeCount [[],[2],[2],[2,2]]) [] := certificate_2846_checked

theorem certificate_2847_checked : certificate_2847.Valid 17 8 17 certificate_2847_q certificate_2847_edges 9 4 [] := by decide +kernel
theorem certificate_2847_valid : certificate_2847.Valid 17 8 (patternOrder [[],[2],[2],[2,3]]) (patternClique [[],[2],[2],[2,3]]) (patternEdges [[],[2],[2],[2,3]]) (patternAmount [[],[2],[2],[2,3]]) (patternEdgeCount [[],[2],[2],[2,3]]) [] := certificate_2847_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates090
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2848_checked : certificate_2848.Valid 17 8 16 certificate_2848_q certificate_2848_edges 8 5 [] := by decide +kernel
theorem certificate_2848_valid : certificate_2848.Valid 17 8 (patternOrder [[],[2],[2,1,1,2]]) (patternClique [[],[2],[2,1,1,2]]) (patternEdges [[],[2],[2,1,1,2]]) (patternAmount [[],[2],[2,1,1,2]]) (patternEdgeCount [[],[2],[2,1,1,2]]) [] := certificate_2848_checked

theorem certificate_2849_checked : certificate_2849.Valid 17 8 17 certificate_2849_q certificate_2849_edges 9 5 [] := by decide +kernel
theorem certificate_2849_valid : certificate_2849.Valid 17 8 (patternOrder [[],[2],[2,1,1,3]]) (patternClique [[],[2],[2,1,1,3]]) (patternEdges [[],[2],[2,1,1,3]]) (patternAmount [[],[2],[2,1,1,3]]) (patternEdgeCount [[],[2],[2,1,1,3]]) [] := certificate_2849_checked

theorem certificate_2850_checked : certificate_2850.Valid 17 8 17 certificate_2850_q certificate_2850_edges 9 5 [] := by decide +kernel
theorem certificate_2850_valid : certificate_2850.Valid 17 8 (patternOrder [[],[2],[2,1,2,2]]) (patternClique [[],[2],[2,1,2,2]]) (patternEdges [[],[2],[2,1,2,2]]) (patternAmount [[],[2],[2,1,2,2]]) (patternEdgeCount [[],[2],[2,1,2,2]]) [] := certificate_2850_checked

theorem certificate_2851_checked : certificate_2851.Valid 17 8 17 certificate_2851_q certificate_2851_edges 9 4 [] := by decide +kernel
theorem certificate_2851_valid : certificate_2851.Valid 17 8 (patternOrder [[],[2],[2,2],[3]]) (patternClique [[],[2],[2,2],[3]]) (patternEdges [[],[2],[2,2],[3]]) (patternAmount [[],[2],[2,2],[3]]) (patternEdgeCount [[],[2],[2,2],[3]]) [] := certificate_2851_checked

theorem certificate_2852_checked : certificate_2852.Valid 17 8 16 certificate_2852_q certificate_2852_edges 8 6 [] := by decide +kernel
theorem certificate_2852_valid : certificate_2852.Valid 17 8 (patternOrder [[],[2,1,1,1,1,2]]) (patternClique [[],[2,1,1,1,1,2]]) (patternEdges [[],[2,1,1,1,1,2]]) (patternAmount [[],[2,1,1,1,1,2]]) (patternEdgeCount [[],[2,1,1,1,1,2]]) [] := certificate_2852_checked

theorem certificate_2853_checked : certificate_2853.Valid 17 8 17 certificate_2853_q certificate_2853_edges 9 6 [] := by decide +kernel
theorem certificate_2853_valid : certificate_2853.Valid 17 8 (patternOrder [[],[2,1,1,1,1,3]]) (patternClique [[],[2,1,1,1,1,3]]) (patternEdges [[],[2,1,1,1,1,3]]) (patternAmount [[],[2,1,1,1,1,3]]) (patternEdgeCount [[],[2,1,1,1,1,3]]) [] := certificate_2853_checked

theorem certificate_2854_checked : certificate_2854.Valid 17 8 17 certificate_2854_q certificate_2854_edges 9 6 [] := by decide +kernel
theorem certificate_2854_valid : certificate_2854.Valid 17 8 (patternOrder [[],[2,1,1,1,2,2]]) (patternClique [[],[2,1,1,1,2,2]]) (patternEdges [[],[2,1,1,1,2,2]]) (patternAmount [[],[2,1,1,1,2,2]]) (patternEdgeCount [[],[2,1,1,1,2,2]]) [] := certificate_2854_checked

theorem certificate_2855_checked : certificate_2855.Valid 17 8 17 certificate_2855_q certificate_2855_edges 9 5 [] := by decide +kernel
theorem certificate_2855_valid : certificate_2855.Valid 17 8 (patternOrder [[],[2,1,1,2],[3]]) (patternClique [[],[2,1,1,2],[3]]) (patternEdges [[],[2,1,1,2],[3]]) (patternAmount [[],[2,1,1,2],[3]]) (patternEdgeCount [[],[2,1,1,2],[3]]) [] := certificate_2855_checked

theorem certificate_2856_checked : certificate_2856.Valid 17 8 17 certificate_2856_q certificate_2856_edges 9 6 [] := by decide +kernel
theorem certificate_2856_valid : certificate_2856.Valid 17 8 (patternOrder [[],[2,1,1,2,1,2]]) (patternClique [[],[2,1,1,2,1,2]]) (patternEdges [[],[2,1,1,2,1,2]]) (patternAmount [[],[2,1,1,2,1,2]]) (patternEdgeCount [[],[2,1,1,2,1,2]]) [] := certificate_2856_checked

theorem certificate_2857_checked : certificate_2857.Valid 17 8 17 certificate_2857_q certificate_2857_edges 9 5 [] := by decide +kernel
theorem certificate_2857_valid : certificate_2857.Valid 17 8 (patternOrder [[],[2,1,2],[2,2]]) (patternClique [[],[2,1,2],[2,2]]) (patternEdges [[],[2,1,2],[2,2]]) (patternAmount [[],[2,1,2],[2,2]]) (patternEdgeCount [[],[2,1,2],[2,2]]) [] := certificate_2857_checked

theorem certificate_2858_checked : certificate_2858.Valid 17 8 12 certificate_2858_q certificate_2858_edges 4 4 [] := by decide +kernel
theorem certificate_2858_valid : certificate_2858.Valid 17 8 (patternOrder [[1],[1],[1],[1]]) (patternClique [[1],[1],[1],[1]]) (patternEdges [[1],[1],[1],[1]]) (patternAmount [[1],[1],[1],[1]]) (patternEdgeCount [[1],[1],[1],[1]]) [] := certificate_2858_checked

theorem certificate_2859_checked : certificate_2859.Valid 17 8 13 certificate_2859_q certificate_2859_edges 5 4 [] := by decide +kernel
theorem certificate_2859_valid : certificate_2859.Valid 17 8 (patternOrder [[1],[1],[1],[2]]) (patternClique [[1],[1],[1],[2]]) (patternEdges [[1],[1],[1],[2]]) (patternAmount [[1],[1],[1],[2]]) (patternEdgeCount [[1],[1],[1],[2]]) [] := certificate_2859_checked

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

theorem patterns_17_8_39_verified_oai : ∀ D ∈ patterns_17_8_39, PatternVerified 17 8 D := by

  simp only [patterns_17_8_39, List.forall_mem_cons]

  exact ⟨⟨certificate_2844, certificate_2844_valid⟩, ⟨⟨certificate_2845, certificate_2845_valid⟩, ⟨⟨certificate_2846, certificate_2846_valid⟩, ⟨⟨certificate_2847, certificate_2847_valid⟩, ⟨⟨certificate_2848, certificate_2848_valid⟩, ⟨⟨certificate_2849, certificate_2849_valid⟩, ⟨⟨certificate_2850, certificate_2850_valid⟩, ⟨⟨certificate_2851, certificate_2851_valid⟩, ⟨⟨certificate_2852, certificate_2852_valid⟩, ⟨⟨certificate_2853, certificate_2853_valid⟩, ⟨⟨certificate_2854, certificate_2854_valid⟩, ⟨⟨certificate_2855, certificate_2855_valid⟩, ⟨⟨certificate_2856, certificate_2856_valid⟩, ⟨⟨certificate_2857, certificate_2857_valid⟩, ⟨⟨certificate_2858, certificate_2858_valid⟩, ⟨⟨certificate_2859, certificate_2859_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_39_verified_oai := @OAI.CycleClique.patterns_17_8_39_verified_oai
