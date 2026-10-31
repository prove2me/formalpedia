-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_7_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:57:20.383372+00:00
-- url     : https://prove2.me/submissions/288af6fd-8a97-4bbf-839b-a1f5df9719b2

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

theorem certificate_1864_checked : certificate_1864.Valid 16 8 15 certificate_1864_q certificate_1864_edges 7 4 [] := by decide +kernel
theorem certificate_1864_valid : certificate_1864.Valid 16 8 (patternOrder [[],[],[],[1,2,1,3]]) (patternClique [[],[],[],[1,2,1,3]]) (patternEdges [[],[],[],[1,2,1,3]]) (patternAmount [[],[],[],[1,2,1,3]]) (patternEdgeCount [[],[],[],[1,2,1,3]]) [] := certificate_1864_checked

theorem certificate_1865_checked : certificate_1865.Valid 16 8 16 certificate_1865_q certificate_1865_edges 8 4 [] := by decide +kernel
theorem certificate_1865_valid : certificate_1865.Valid 16 8 (patternOrder [[],[],[],[1,2,1,4]]) (patternClique [[],[],[],[1,2,1,4]]) (patternEdges [[],[],[],[1,2,1,4]]) (patternAmount [[],[],[],[1,2,1,4]]) (patternEdgeCount [[],[],[],[1,2,1,4]]) [] := certificate_1865_checked

theorem certificate_1866_checked : certificate_1866.Valid 16 8 14 certificate_1866_q certificate_1866_edges 6 4 [] := by decide +kernel
theorem certificate_1866_valid : certificate_1866.Valid 16 8 (patternOrder [[],[],[],[1,2,2,1]]) (patternClique [[],[],[],[1,2,2,1]]) (patternEdges [[],[],[],[1,2,2,1]]) (patternAmount [[],[],[],[1,2,2,1]]) (patternEdgeCount [[],[],[],[1,2,2,1]]) [] := certificate_1866_checked

theorem certificate_1867_checked : certificate_1867.Valid 16 8 15 certificate_1867_q certificate_1867_edges 7 4 [] := by decide +kernel
theorem certificate_1867_valid : certificate_1867.Valid 16 8 (patternOrder [[],[],[],[1,2,2,2]]) (patternClique [[],[],[],[1,2,2,2]]) (patternEdges [[],[],[],[1,2,2,2]]) (patternAmount [[],[],[],[1,2,2,2]]) (patternEdgeCount [[],[],[],[1,2,2,2]]) [] := certificate_1867_checked

theorem certificate_1868_checked : certificate_1868.Valid 16 8 16 certificate_1868_q certificate_1868_edges 8 4 [] := by decide +kernel
theorem certificate_1868_valid : certificate_1868.Valid 16 8 (patternOrder [[],[],[],[1,2,2,3]]) (patternClique [[],[],[],[1,2,2,3]]) (patternEdges [[],[],[],[1,2,2,3]]) (patternAmount [[],[],[],[1,2,2,3]]) (patternEdgeCount [[],[],[],[1,2,2,3]]) [] := certificate_1868_checked

theorem certificate_1869_checked : certificate_1869.Valid 16 8 15 certificate_1869_q certificate_1869_edges 7 4 [] := by decide +kernel
theorem certificate_1869_valid : certificate_1869.Valid 16 8 (patternOrder [[],[],[],[1,2,3,1]]) (patternClique [[],[],[],[1,2,3,1]]) (patternEdges [[],[],[],[1,2,3,1]]) (patternAmount [[],[],[],[1,2,3,1]]) (patternEdgeCount [[],[],[],[1,2,3,1]]) [] := certificate_1869_checked

theorem certificate_1870_checked : certificate_1870.Valid 16 8 16 certificate_1870_q certificate_1870_edges 8 4 [] := by decide +kernel
theorem certificate_1870_valid : certificate_1870.Valid 16 8 (patternOrder [[],[],[],[1,2,3,2]]) (patternClique [[],[],[],[1,2,3,2]]) (patternEdges [[],[],[],[1,2,3,2]]) (patternAmount [[],[],[],[1,2,3,2]]) (patternEdgeCount [[],[],[],[1,2,3,2]]) [] := certificate_1870_checked

theorem certificate_1871_checked : certificate_1871.Valid 16 8 16 certificate_1871_q certificate_1871_edges 8 4 [] := by decide +kernel
theorem certificate_1871_valid : certificate_1871.Valid 16 8 (patternOrder [[],[],[],[1,2,4,1]]) (patternClique [[],[],[],[1,2,4,1]]) (patternEdges [[],[],[],[1,2,4,1]]) (patternAmount [[],[],[],[1,2,4,1]]) (patternEdgeCount [[],[],[],[1,2,4,1]]) [] := certificate_1871_checked

theorem certificate_1872_checked : certificate_1872.Valid 16 8 14 certificate_1872_q certificate_1872_edges 6 3 [] := by decide +kernel
theorem certificate_1872_valid : certificate_1872.Valid 16 8 (patternOrder [[],[],[],[1,3],[2]]) (patternClique [[],[],[],[1,3],[2]]) (patternEdges [[],[],[],[1,3],[2]]) (patternAmount [[],[],[],[1,3],[2]]) (patternEdgeCount [[],[],[],[1,3],[2]]) [] := certificate_1872_checked

theorem certificate_1873_checked : certificate_1873.Valid 16 8 15 certificate_1873_q certificate_1873_edges 7 3 [] := by decide +kernel
theorem certificate_1873_valid : certificate_1873.Valid 16 8 (patternOrder [[],[],[],[1,3],[3]]) (patternClique [[],[],[],[1,3],[3]]) (patternEdges [[],[],[],[1,3],[3]]) (patternAmount [[],[],[],[1,3],[3]]) (patternEdgeCount [[],[],[],[1,3],[3]]) [] := certificate_1873_checked

theorem certificate_1874_checked : certificate_1874.Valid 16 8 16 certificate_1874_q certificate_1874_edges 8 3 [] := by decide +kernel
theorem certificate_1874_valid : certificate_1874.Valid 16 8 (patternOrder [[],[],[],[1,3],[4]]) (patternClique [[],[],[],[1,3],[4]]) (patternEdges [[],[],[],[1,3],[4]]) (patternAmount [[],[],[],[1,3],[4]]) (patternEdgeCount [[],[],[],[1,3],[4]]) [] := certificate_1874_checked

theorem certificate_1875_checked : certificate_1875.Valid 16 8 15 certificate_1875_q certificate_1875_edges 7 4 [] := by decide +kernel
theorem certificate_1875_valid : certificate_1875.Valid 16 8 (patternOrder [[],[],[],[1,3,1,2]]) (patternClique [[],[],[],[1,3,1,2]]) (patternEdges [[],[],[],[1,3,1,2]]) (patternAmount [[],[],[],[1,3,1,2]]) (patternEdgeCount [[],[],[],[1,3,1,2]]) [] := certificate_1875_checked

theorem certificate_1876_checked : certificate_1876.Valid 16 8 16 certificate_1876_q certificate_1876_edges 8 4 [] := by decide +kernel
theorem certificate_1876_valid : certificate_1876.Valid 16 8 (patternOrder [[],[],[],[1,3,1,3]]) (patternClique [[],[],[],[1,3,1,3]]) (patternEdges [[],[],[],[1,3,1,3]]) (patternAmount [[],[],[],[1,3,1,3]]) (patternEdgeCount [[],[],[],[1,3,1,3]]) [] := certificate_1876_checked

theorem certificate_1877_checked : certificate_1877.Valid 16 8 16 certificate_1877_q certificate_1877_edges 8 4 [] := by decide +kernel
theorem certificate_1877_valid : certificate_1877.Valid 16 8 (patternOrder [[],[],[],[1,3,2,2]]) (patternClique [[],[],[],[1,3,2,2]]) (patternEdges [[],[],[],[1,3,2,2]]) (patternAmount [[],[],[],[1,3,2,2]]) (patternEdgeCount [[],[],[],[1,3,2,2]]) [] := certificate_1877_checked

theorem certificate_1878_checked : certificate_1878.Valid 16 8 16 certificate_1878_q certificate_1878_edges 8 4 [] := by decide +kernel
theorem certificate_1878_valid : certificate_1878.Valid 16 8 (patternOrder [[],[],[],[1,3,3,1]]) (patternClique [[],[],[],[1,3,3,1]]) (patternEdges [[],[],[],[1,3,3,1]]) (patternAmount [[],[],[],[1,3,3,1]]) (patternEdgeCount [[],[],[],[1,3,3,1]]) [] := certificate_1878_checked

theorem certificate_1879_checked : certificate_1879.Valid 16 8 15 certificate_1879_q certificate_1879_edges 7 3 [] := by decide +kernel
theorem certificate_1879_valid : certificate_1879.Valid 16 8 (patternOrder [[],[],[],[1,4],[2]]) (patternClique [[],[],[],[1,4],[2]]) (patternEdges [[],[],[],[1,4],[2]]) (patternAmount [[],[],[],[1,4],[2]]) (patternEdgeCount [[],[],[],[1,4],[2]]) [] := certificate_1879_checked

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

theorem patterns_16_8_7_verified_oai : ∀ D ∈ patterns_16_8_7, PatternVerified 16 8 D := by

  simp only [patterns_16_8_7, List.forall_mem_cons]

  exact ⟨⟨certificate_1864, certificate_1864_valid⟩, ⟨⟨certificate_1865, certificate_1865_valid⟩, ⟨⟨certificate_1866, certificate_1866_valid⟩, ⟨⟨certificate_1867, certificate_1867_valid⟩, ⟨⟨certificate_1868, certificate_1868_valid⟩, ⟨⟨certificate_1869, certificate_1869_valid⟩, ⟨⟨certificate_1870, certificate_1870_valid⟩, ⟨⟨certificate_1871, certificate_1871_valid⟩, ⟨⟨certificate_1872, certificate_1872_valid⟩, ⟨⟨certificate_1873, certificate_1873_valid⟩, ⟨⟨certificate_1874, certificate_1874_valid⟩, ⟨⟨certificate_1875, certificate_1875_valid⟩, ⟨⟨certificate_1876, certificate_1876_valid⟩, ⟨⟨certificate_1877, certificate_1877_valid⟩, ⟨⟨certificate_1878, certificate_1878_valid⟩, ⟨⟨certificate_1879, certificate_1879_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_7_verified_oai := @OAI.CycleClique.patterns_16_8_7_verified_oai
