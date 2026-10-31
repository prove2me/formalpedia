-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_5_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:54:46.582669+00:00
-- url     : https://prove2.me/submissions/9849b7f6-5c16-491e-8b9c-479b90af268f

import Mathlib
import Definitions.Def_OAIQ107D054
import Definitions.Def_OAIQ107D129
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates058
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1832_checked : certificate_1832.Valid 16 8 16 certificate_1832_q certificate_1832_edges 8 3 [] := by decide +kernel
theorem certificate_1832_valid : certificate_1832.Valid 16 8 (patternOrder [[],[],[],[1],[1,6]]) (patternClique [[],[],[],[1],[1,6]]) (patternEdges [[],[],[],[1],[1,6]]) (patternAmount [[],[],[],[1],[1,6]]) (patternEdgeCount [[],[],[],[1],[1,6]]) [] := certificate_1832_checked

theorem certificate_1833_checked : certificate_1833.Valid 16 8 13 certificate_1833_q certificate_1833_edges 5 3 [] := by decide +kernel
theorem certificate_1833_valid : certificate_1833.Valid 16 8 (patternOrder [[],[],[],[1],[2,2]]) (patternClique [[],[],[],[1],[2,2]]) (patternEdges [[],[],[],[1],[2,2]]) (patternAmount [[],[],[],[1],[2,2]]) (patternEdgeCount [[],[],[],[1],[2,2]]) [] := certificate_1833_checked

theorem certificate_1834_checked : certificate_1834.Valid 16 8 14 certificate_1834_q certificate_1834_edges 6 3 [] := by decide +kernel
theorem certificate_1834_valid : certificate_1834.Valid 16 8 (patternOrder [[],[],[],[1],[2,3]]) (patternClique [[],[],[],[1],[2,3]]) (patternEdges [[],[],[],[1],[2,3]]) (patternAmount [[],[],[],[1],[2,3]]) (patternEdgeCount [[],[],[],[1],[2,3]]) [] := certificate_1834_checked

theorem certificate_1835_checked : certificate_1835.Valid 16 8 15 certificate_1835_q certificate_1835_edges 7 3 [] := by decide +kernel
theorem certificate_1835_valid : certificate_1835.Valid 16 8 (patternOrder [[],[],[],[1],[2,4]]) (patternClique [[],[],[],[1],[2,4]]) (patternEdges [[],[],[],[1],[2,4]]) (patternAmount [[],[],[],[1],[2,4]]) (patternEdgeCount [[],[],[],[1],[2,4]]) [] := certificate_1835_checked

theorem certificate_1836_checked : certificate_1836.Valid 16 8 16 certificate_1836_q certificate_1836_edges 8 3 [] := by decide +kernel
theorem certificate_1836_valid : certificate_1836.Valid 16 8 (patternOrder [[],[],[],[1],[2,5]]) (patternClique [[],[],[],[1],[2,5]]) (patternEdges [[],[],[],[1],[2,5]]) (patternAmount [[],[],[],[1],[2,5]]) (patternEdgeCount [[],[],[],[1],[2,5]]) [] := certificate_1836_checked

theorem certificate_1837_checked : certificate_1837.Valid 16 8 15 certificate_1837_q certificate_1837_edges 7 3 [] := by decide +kernel
theorem certificate_1837_valid : certificate_1837.Valid 16 8 (patternOrder [[],[],[],[1],[3,3]]) (patternClique [[],[],[],[1],[3,3]]) (patternEdges [[],[],[],[1],[3,3]]) (patternAmount [[],[],[],[1],[3,3]]) (patternEdgeCount [[],[],[],[1],[3,3]]) [] := certificate_1837_checked

theorem certificate_1838_checked : certificate_1838.Valid 16 8 16 certificate_1838_q certificate_1838_edges 8 3 [] := by decide +kernel
theorem certificate_1838_valid : certificate_1838.Valid 16 8 (patternOrder [[],[],[],[1],[3,4]]) (patternClique [[],[],[],[1],[3,4]]) (patternEdges [[],[],[],[1],[3,4]]) (patternAmount [[],[],[],[1],[3,4]]) (patternEdgeCount [[],[],[],[1],[3,4]]) [] := certificate_1838_checked

theorem certificate_1839_checked : certificate_1839.Valid 16 8 12 certificate_1839_q certificate_1839_edges 4 3 [] := by decide +kernel
theorem certificate_1839_valid : certificate_1839.Valid 16 8 (patternOrder [[],[],[],[1,1],[2]]) (patternClique [[],[],[],[1,1],[2]]) (patternEdges [[],[],[],[1,1],[2]]) (patternAmount [[],[],[],[1,1],[2]]) (patternEdgeCount [[],[],[],[1,1],[2]]) [] := certificate_1839_checked

theorem certificate_1840_checked : certificate_1840.Valid 16 8 13 certificate_1840_q certificate_1840_edges 5 3 [] := by decide +kernel
theorem certificate_1840_valid : certificate_1840.Valid 16 8 (patternOrder [[],[],[],[1,1],[3]]) (patternClique [[],[],[],[1,1],[3]]) (patternEdges [[],[],[],[1,1],[3]]) (patternAmount [[],[],[],[1,1],[3]]) (patternEdgeCount [[],[],[],[1,1],[3]]) [] := certificate_1840_checked

theorem certificate_1841_checked : certificate_1841.Valid 16 8 14 certificate_1841_q certificate_1841_edges 6 3 [] := by decide +kernel
theorem certificate_1841_valid : certificate_1841.Valid 16 8 (patternOrder [[],[],[],[1,1],[4]]) (patternClique [[],[],[],[1,1],[4]]) (patternEdges [[],[],[],[1,1],[4]]) (patternAmount [[],[],[],[1,1],[4]]) (patternEdgeCount [[],[],[],[1,1],[4]]) [] := certificate_1841_checked

theorem certificate_1842_checked : certificate_1842.Valid 16 8 15 certificate_1842_q certificate_1842_edges 7 3 [] := by decide +kernel
theorem certificate_1842_valid : certificate_1842.Valid 16 8 (patternOrder [[],[],[],[1,1],[5]]) (patternClique [[],[],[],[1,1],[5]]) (patternEdges [[],[],[],[1,1],[5]]) (patternAmount [[],[],[],[1,1],[5]]) (patternEdgeCount [[],[],[],[1,1],[5]]) [] := certificate_1842_checked

theorem certificate_1843_checked : certificate_1843.Valid 16 8 16 certificate_1843_q certificate_1843_edges 8 3 [] := by decide +kernel
theorem certificate_1843_valid : certificate_1843.Valid 16 8 (patternOrder [[],[],[],[1,1],[6]]) (patternClique [[],[],[],[1,1],[6]]) (patternEdges [[],[],[],[1,1],[6]]) (patternAmount [[],[],[],[1,1],[6]]) (patternEdgeCount [[],[],[],[1,1],[6]]) [] := certificate_1843_checked

theorem certificate_1844_checked : certificate_1844.Valid 16 8 12 certificate_1844_q certificate_1844_edges 4 4 [] := by decide +kernel
theorem certificate_1844_valid : certificate_1844.Valid 16 8 (patternOrder [[],[],[],[1,1,1,1]]) (patternClique [[],[],[],[1,1,1,1]]) (patternEdges [[],[],[],[1,1,1,1]]) (patternAmount [[],[],[],[1,1,1,1]]) (patternEdgeCount [[],[],[],[1,1,1,1]]) [] := certificate_1844_checked

theorem certificate_1845_checked : certificate_1845.Valid 16 8 13 certificate_1845_q certificate_1845_edges 5 4 [] := by decide +kernel
theorem certificate_1845_valid : certificate_1845.Valid 16 8 (patternOrder [[],[],[],[1,1,1,2]]) (patternClique [[],[],[],[1,1,1,2]]) (patternEdges [[],[],[],[1,1,1,2]]) (patternAmount [[],[],[],[1,1,1,2]]) (patternEdgeCount [[],[],[],[1,1,1,2]]) [] := certificate_1845_checked

theorem certificate_1846_checked : certificate_1846.Valid 16 8 14 certificate_1846_q certificate_1846_edges 6 4 [] := by decide +kernel
theorem certificate_1846_valid : certificate_1846.Valid 16 8 (patternOrder [[],[],[],[1,1,1,3]]) (patternClique [[],[],[],[1,1,1,3]]) (patternEdges [[],[],[],[1,1,1,3]]) (patternAmount [[],[],[],[1,1,1,3]]) (patternEdgeCount [[],[],[],[1,1,1,3]]) [] := certificate_1846_checked

theorem certificate_1847_checked : certificate_1847.Valid 16 8 15 certificate_1847_q certificate_1847_edges 7 4 [] := by decide +kernel
theorem certificate_1847_valid : certificate_1847.Valid 16 8 (patternOrder [[],[],[],[1,1,1,4]]) (patternClique [[],[],[],[1,1,1,4]]) (patternEdges [[],[],[],[1,1,1,4]]) (patternAmount [[],[],[],[1,1,1,4]]) (patternEdgeCount [[],[],[],[1,1,1,4]]) [] := certificate_1847_checked

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

theorem patterns_16_8_5_verified_oai : ∀ D ∈ patterns_16_8_5, PatternVerified 16 8 D := by

  simp only [patterns_16_8_5, List.forall_mem_cons]

  exact ⟨⟨certificate_1832, certificate_1832_valid⟩, ⟨⟨certificate_1833, certificate_1833_valid⟩, ⟨⟨certificate_1834, certificate_1834_valid⟩, ⟨⟨certificate_1835, certificate_1835_valid⟩, ⟨⟨certificate_1836, certificate_1836_valid⟩, ⟨⟨certificate_1837, certificate_1837_valid⟩, ⟨⟨certificate_1838, certificate_1838_valid⟩, ⟨⟨certificate_1839, certificate_1839_valid⟩, ⟨⟨certificate_1840, certificate_1840_valid⟩, ⟨⟨certificate_1841, certificate_1841_valid⟩, ⟨⟨certificate_1842, certificate_1842_valid⟩, ⟨⟨certificate_1843, certificate_1843_valid⟩, ⟨⟨certificate_1844, certificate_1844_valid⟩, ⟨⟨certificate_1845, certificate_1845_valid⟩, ⟨⟨certificate_1846, certificate_1846_valid⟩, ⟨⟨certificate_1847, certificate_1847_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_5_verified_oai := @OAI.CycleClique.patterns_16_8_5_verified_oai
