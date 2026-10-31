-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_8_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:58:04.690572+00:00
-- url     : https://prove2.me/submissions/b57bf166-0fa6-45ac-b793-4dcab5a359ae

import Mathlib
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates059
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1880_checked : certificate_1880.Valid 16 8 16 certificate_1880_q certificate_1880_edges 8 3 [] := by decide +kernel
theorem certificate_1880_valid : certificate_1880.Valid 16 8 (patternOrder [[],[],[],[1,4],[3]]) (patternClique [[],[],[],[1,4],[3]]) (patternEdges [[],[],[],[1,4],[3]]) (patternAmount [[],[],[],[1,4],[3]]) (patternEdgeCount [[],[],[],[1,4],[3]]) [] := certificate_1880_checked

theorem certificate_1881_checked : certificate_1881.Valid 16 8 16 certificate_1881_q certificate_1881_edges 8 4 [] := by decide +kernel
theorem certificate_1881_valid : certificate_1881.Valid 16 8 (patternOrder [[],[],[],[1,4,1,2]]) (patternClique [[],[],[],[1,4,1,2]]) (patternEdges [[],[],[],[1,4,1,2]]) (patternAmount [[],[],[],[1,4,1,2]]) (patternEdgeCount [[],[],[],[1,4,1,2]]) [] := certificate_1881_checked

theorem certificate_1882_checked : certificate_1882.Valid 16 8 16 certificate_1882_q certificate_1882_edges 8 3 [] := by decide +kernel
theorem certificate_1882_valid : certificate_1882.Valid 16 8 (patternOrder [[],[],[],[1,5],[2]]) (patternClique [[],[],[],[1,5],[2]]) (patternEdges [[],[],[],[1,5],[2]]) (patternAmount [[],[],[],[1,5],[2]]) (patternEdgeCount [[],[],[],[1,5],[2]]) [] := certificate_1882_checked

theorem certificate_1883_checked : certificate_1883.Valid 16 8 14 certificate_1883_q certificate_1883_edges 6 3 [] := by decide +kernel
theorem certificate_1883_valid : certificate_1883.Valid 16 8 (patternOrder [[],[],[],[2],[2,2]]) (patternClique [[],[],[],[2],[2,2]]) (patternEdges [[],[],[],[2],[2,2]]) (patternAmount [[],[],[],[2],[2,2]]) (patternEdgeCount [[],[],[],[2],[2,2]]) [] := certificate_1883_checked

theorem certificate_1884_checked : certificate_1884.Valid 16 8 15 certificate_1884_q certificate_1884_edges 7 3 [] := by decide +kernel
theorem certificate_1884_valid : certificate_1884.Valid 16 8 (patternOrder [[],[],[],[2],[2,3]]) (patternClique [[],[],[],[2],[2,3]]) (patternEdges [[],[],[],[2],[2,3]]) (patternAmount [[],[],[],[2],[2,3]]) (patternEdgeCount [[],[],[],[2],[2,3]]) [] := certificate_1884_checked

theorem certificate_1885_checked : certificate_1885.Valid 16 8 16 certificate_1885_q certificate_1885_edges 8 3 [] := by decide +kernel
theorem certificate_1885_valid : certificate_1885.Valid 16 8 (patternOrder [[],[],[],[2],[2,4]]) (patternClique [[],[],[],[2],[2,4]]) (patternEdges [[],[],[],[2],[2,4]]) (patternAmount [[],[],[],[2],[2,4]]) (patternEdgeCount [[],[],[],[2],[2,4]]) [] := certificate_1885_checked

theorem certificate_1886_checked : certificate_1886.Valid 16 8 16 certificate_1886_q certificate_1886_edges 8 3 [] := by decide +kernel
theorem certificate_1886_valid : certificate_1886.Valid 16 8 (patternOrder [[],[],[],[2],[3,3]]) (patternClique [[],[],[],[2],[3,3]]) (patternEdges [[],[],[],[2],[3,3]]) (patternAmount [[],[],[],[2],[3,3]]) (patternEdgeCount [[],[],[],[2],[3,3]]) [] := certificate_1886_checked

theorem certificate_1887_checked : certificate_1887.Valid 16 8 14 certificate_1887_q certificate_1887_edges 6 4 [] := by decide +kernel
theorem certificate_1887_valid : certificate_1887.Valid 16 8 (patternOrder [[],[],[],[2,1,1,2]]) (patternClique [[],[],[],[2,1,1,2]]) (patternEdges [[],[],[],[2,1,1,2]]) (patternAmount [[],[],[],[2,1,1,2]]) (patternEdgeCount [[],[],[],[2,1,1,2]]) [] := certificate_1887_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates060
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1888_checked : certificate_1888.Valid 16 8 15 certificate_1888_q certificate_1888_edges 7 4 [] := by decide +kernel
theorem certificate_1888_valid : certificate_1888.Valid 16 8 (patternOrder [[],[],[],[2,1,1,3]]) (patternClique [[],[],[],[2,1,1,3]]) (patternEdges [[],[],[],[2,1,1,3]]) (patternAmount [[],[],[],[2,1,1,3]]) (patternEdgeCount [[],[],[],[2,1,1,3]]) [] := certificate_1888_checked

theorem certificate_1889_checked : certificate_1889.Valid 16 8 16 certificate_1889_q certificate_1889_edges 8 4 [] := by decide +kernel
theorem certificate_1889_valid : certificate_1889.Valid 16 8 (patternOrder [[],[],[],[2,1,1,4]]) (patternClique [[],[],[],[2,1,1,4]]) (patternEdges [[],[],[],[2,1,1,4]]) (patternAmount [[],[],[],[2,1,1,4]]) (patternEdgeCount [[],[],[],[2,1,1,4]]) [] := certificate_1889_checked

theorem certificate_1890_checked : certificate_1890.Valid 16 8 15 certificate_1890_q certificate_1890_edges 7 4 [] := by decide +kernel
theorem certificate_1890_valid : certificate_1890.Valid 16 8 (patternOrder [[],[],[],[2,1,2,2]]) (patternClique [[],[],[],[2,1,2,2]]) (patternEdges [[],[],[],[2,1,2,2]]) (patternAmount [[],[],[],[2,1,2,2]]) (patternEdgeCount [[],[],[],[2,1,2,2]]) [] := certificate_1890_checked

theorem certificate_1891_checked : certificate_1891.Valid 16 8 16 certificate_1891_q certificate_1891_edges 8 4 [] := by decide +kernel
theorem certificate_1891_valid : certificate_1891.Valid 16 8 (patternOrder [[],[],[],[2,1,2,3]]) (patternClique [[],[],[],[2,1,2,3]]) (patternEdges [[],[],[],[2,1,2,3]]) (patternAmount [[],[],[],[2,1,2,3]]) (patternEdgeCount [[],[],[],[2,1,2,3]]) [] := certificate_1891_checked

theorem certificate_1892_checked : certificate_1892.Valid 16 8 16 certificate_1892_q certificate_1892_edges 8 4 [] := by decide +kernel
theorem certificate_1892_valid : certificate_1892.Valid 16 8 (patternOrder [[],[],[],[2,1,3,2]]) (patternClique [[],[],[],[2,1,3,2]]) (patternEdges [[],[],[],[2,1,3,2]]) (patternAmount [[],[],[],[2,1,3,2]]) (patternEdgeCount [[],[],[],[2,1,3,2]]) [] := certificate_1892_checked

theorem certificate_1893_checked : certificate_1893.Valid 16 8 15 certificate_1893_q certificate_1893_edges 7 3 [] := by decide +kernel
theorem certificate_1893_valid : certificate_1893.Valid 16 8 (patternOrder [[],[],[],[2,2],[3]]) (patternClique [[],[],[],[2,2],[3]]) (patternEdges [[],[],[],[2,2],[3]]) (patternAmount [[],[],[],[2,2],[3]]) (patternEdgeCount [[],[],[],[2,2],[3]]) [] := certificate_1893_checked

theorem certificate_1894_checked : certificate_1894.Valid 16 8 16 certificate_1894_q certificate_1894_edges 8 3 [] := by decide +kernel
theorem certificate_1894_valid : certificate_1894.Valid 16 8 (patternOrder [[],[],[],[2,2],[4]]) (patternClique [[],[],[],[2,2],[4]]) (patternEdges [[],[],[],[2,2],[4]]) (patternAmount [[],[],[],[2,2],[4]]) (patternEdgeCount [[],[],[],[2,2],[4]]) [] := certificate_1894_checked

theorem certificate_1895_checked : certificate_1895.Valid 16 8 16 certificate_1895_q certificate_1895_edges 8 4 [] := by decide +kernel
theorem certificate_1895_valid : certificate_1895.Valid 16 8 (patternOrder [[],[],[],[2,2,1,3]]) (patternClique [[],[],[],[2,2,1,3]]) (patternEdges [[],[],[],[2,2,1,3]]) (patternAmount [[],[],[],[2,2,1,3]]) (patternEdgeCount [[],[],[],[2,2,1,3]]) [] := certificate_1895_checked

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

theorem patterns_16_8_8_verified_oai : ∀ D ∈ patterns_16_8_8, PatternVerified 16 8 D := by

  simp only [patterns_16_8_8, List.forall_mem_cons]

  exact ⟨⟨certificate_1880, certificate_1880_valid⟩, ⟨⟨certificate_1881, certificate_1881_valid⟩, ⟨⟨certificate_1882, certificate_1882_valid⟩, ⟨⟨certificate_1883, certificate_1883_valid⟩, ⟨⟨certificate_1884, certificate_1884_valid⟩, ⟨⟨certificate_1885, certificate_1885_valid⟩, ⟨⟨certificate_1886, certificate_1886_valid⟩, ⟨⟨certificate_1887, certificate_1887_valid⟩, ⟨⟨certificate_1888, certificate_1888_valid⟩, ⟨⟨certificate_1889, certificate_1889_valid⟩, ⟨⟨certificate_1890, certificate_1890_valid⟩, ⟨⟨certificate_1891, certificate_1891_valid⟩, ⟨⟨certificate_1892, certificate_1892_valid⟩, ⟨⟨certificate_1893, certificate_1893_valid⟩, ⟨⟨certificate_1894, certificate_1894_valid⟩, ⟨⟨certificate_1895, certificate_1895_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_8_verified_oai := @OAI.CycleClique.patterns_16_8_8_verified_oai
