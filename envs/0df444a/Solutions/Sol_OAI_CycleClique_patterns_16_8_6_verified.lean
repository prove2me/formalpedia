-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_6_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:55:09.519213+00:00
-- url     : https://prove2.me/submissions/968e1cc7-2007-48d1-b0c4-7eea2e9d69ed

import Mathlib
import Definitions.Def_OAIQ107D130
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

theorem certificate_1848_checked : certificate_1848.Valid 16 8 16 certificate_1848_q certificate_1848_edges 8 4 [] := by decide +kernel
theorem certificate_1848_valid : certificate_1848.Valid 16 8 (patternOrder [[],[],[],[1,1,1,5]]) (patternClique [[],[],[],[1,1,1,5]]) (patternEdges [[],[],[],[1,1,1,5]]) (patternAmount [[],[],[],[1,1,1,5]]) (patternEdgeCount [[],[],[],[1,1,1,5]]) [] := certificate_1848_checked

theorem certificate_1849_checked : certificate_1849.Valid 16 8 13 certificate_1849_q certificate_1849_edges 5 4 [] := by decide +kernel
theorem certificate_1849_valid : certificate_1849.Valid 16 8 (patternOrder [[],[],[],[1,1,2,1]]) (patternClique [[],[],[],[1,1,2,1]]) (patternEdges [[],[],[],[1,1,2,1]]) (patternAmount [[],[],[],[1,1,2,1]]) (patternEdgeCount [[],[],[],[1,1,2,1]]) [] := certificate_1849_checked

theorem certificate_1850_checked : certificate_1850.Valid 16 8 14 certificate_1850_q certificate_1850_edges 6 4 [] := by decide +kernel
theorem certificate_1850_valid : certificate_1850.Valid 16 8 (patternOrder [[],[],[],[1,1,2,2]]) (patternClique [[],[],[],[1,1,2,2]]) (patternEdges [[],[],[],[1,1,2,2]]) (patternAmount [[],[],[],[1,1,2,2]]) (patternEdgeCount [[],[],[],[1,1,2,2]]) [] := certificate_1850_checked

theorem certificate_1851_checked : certificate_1851.Valid 16 8 15 certificate_1851_q certificate_1851_edges 7 4 [] := by decide +kernel
theorem certificate_1851_valid : certificate_1851.Valid 16 8 (patternOrder [[],[],[],[1,1,2,3]]) (patternClique [[],[],[],[1,1,2,3]]) (patternEdges [[],[],[],[1,1,2,3]]) (patternAmount [[],[],[],[1,1,2,3]]) (patternEdgeCount [[],[],[],[1,1,2,3]]) [] := certificate_1851_checked

theorem certificate_1852_checked : certificate_1852.Valid 16 8 16 certificate_1852_q certificate_1852_edges 8 4 [] := by decide +kernel
theorem certificate_1852_valid : certificate_1852.Valid 16 8 (patternOrder [[],[],[],[1,1,2,4]]) (patternClique [[],[],[],[1,1,2,4]]) (patternEdges [[],[],[],[1,1,2,4]]) (patternAmount [[],[],[],[1,1,2,4]]) (patternEdgeCount [[],[],[],[1,1,2,4]]) [] := certificate_1852_checked

theorem certificate_1853_checked : certificate_1853.Valid 16 8 14 certificate_1853_q certificate_1853_edges 6 4 [] := by decide +kernel
theorem certificate_1853_valid : certificate_1853.Valid 16 8 (patternOrder [[],[],[],[1,1,3,1]]) (patternClique [[],[],[],[1,1,3,1]]) (patternEdges [[],[],[],[1,1,3,1]]) (patternAmount [[],[],[],[1,1,3,1]]) (patternEdgeCount [[],[],[],[1,1,3,1]]) [] := certificate_1853_checked

theorem certificate_1854_checked : certificate_1854.Valid 16 8 15 certificate_1854_q certificate_1854_edges 7 4 [] := by decide +kernel
theorem certificate_1854_valid : certificate_1854.Valid 16 8 (patternOrder [[],[],[],[1,1,3,2]]) (patternClique [[],[],[],[1,1,3,2]]) (patternEdges [[],[],[],[1,1,3,2]]) (patternAmount [[],[],[],[1,1,3,2]]) (patternEdgeCount [[],[],[],[1,1,3,2]]) [] := certificate_1854_checked

theorem certificate_1855_checked : certificate_1855.Valid 16 8 16 certificate_1855_q certificate_1855_edges 8 4 [] := by decide +kernel
theorem certificate_1855_valid : certificate_1855.Valid 16 8 (patternOrder [[],[],[],[1,1,3,3]]) (patternClique [[],[],[],[1,1,3,3]]) (patternEdges [[],[],[],[1,1,3,3]]) (patternAmount [[],[],[],[1,1,3,3]]) (patternEdgeCount [[],[],[],[1,1,3,3]]) [] := certificate_1855_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates059
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1856_checked : certificate_1856.Valid 16 8 15 certificate_1856_q certificate_1856_edges 7 4 [] := by decide +kernel
theorem certificate_1856_valid : certificate_1856.Valid 16 8 (patternOrder [[],[],[],[1,1,4,1]]) (patternClique [[],[],[],[1,1,4,1]]) (patternEdges [[],[],[],[1,1,4,1]]) (patternAmount [[],[],[],[1,1,4,1]]) (patternEdgeCount [[],[],[],[1,1,4,1]]) [] := certificate_1856_checked

theorem certificate_1857_checked : certificate_1857.Valid 16 8 16 certificate_1857_q certificate_1857_edges 8 4 [] := by decide +kernel
theorem certificate_1857_valid : certificate_1857.Valid 16 8 (patternOrder [[],[],[],[1,1,4,2]]) (patternClique [[],[],[],[1,1,4,2]]) (patternEdges [[],[],[],[1,1,4,2]]) (patternAmount [[],[],[],[1,1,4,2]]) (patternEdgeCount [[],[],[],[1,1,4,2]]) [] := certificate_1857_checked

theorem certificate_1858_checked : certificate_1858.Valid 16 8 16 certificate_1858_q certificate_1858_edges 8 4 [] := by decide +kernel
theorem certificate_1858_valid : certificate_1858.Valid 16 8 (patternOrder [[],[],[],[1,1,5,1]]) (patternClique [[],[],[],[1,1,5,1]]) (patternEdges [[],[],[],[1,1,5,1]]) (patternAmount [[],[],[],[1,1,5,1]]) (patternEdgeCount [[],[],[],[1,1,5,1]]) [] := certificate_1858_checked

theorem certificate_1859_checked : certificate_1859.Valid 16 8 13 certificate_1859_q certificate_1859_edges 5 3 [] := by decide +kernel
theorem certificate_1859_valid : certificate_1859.Valid 16 8 (patternOrder [[],[],[],[1,2],[2]]) (patternClique [[],[],[],[1,2],[2]]) (patternEdges [[],[],[],[1,2],[2]]) (patternAmount [[],[],[],[1,2],[2]]) (patternEdgeCount [[],[],[],[1,2],[2]]) [] := certificate_1859_checked

theorem certificate_1860_checked : certificate_1860.Valid 16 8 14 certificate_1860_q certificate_1860_edges 6 3 [] := by decide +kernel
theorem certificate_1860_valid : certificate_1860.Valid 16 8 (patternOrder [[],[],[],[1,2],[3]]) (patternClique [[],[],[],[1,2],[3]]) (patternEdges [[],[],[],[1,2],[3]]) (patternAmount [[],[],[],[1,2],[3]]) (patternEdgeCount [[],[],[],[1,2],[3]]) [] := certificate_1860_checked

theorem certificate_1861_checked : certificate_1861.Valid 16 8 15 certificate_1861_q certificate_1861_edges 7 3 [] := by decide +kernel
theorem certificate_1861_valid : certificate_1861.Valid 16 8 (patternOrder [[],[],[],[1,2],[4]]) (patternClique [[],[],[],[1,2],[4]]) (patternEdges [[],[],[],[1,2],[4]]) (patternAmount [[],[],[],[1,2],[4]]) (patternEdgeCount [[],[],[],[1,2],[4]]) [] := certificate_1861_checked

theorem certificate_1862_checked : certificate_1862.Valid 16 8 16 certificate_1862_q certificate_1862_edges 8 3 [] := by decide +kernel
theorem certificate_1862_valid : certificate_1862.Valid 16 8 (patternOrder [[],[],[],[1,2],[5]]) (patternClique [[],[],[],[1,2],[5]]) (patternEdges [[],[],[],[1,2],[5]]) (patternAmount [[],[],[],[1,2],[5]]) (patternEdgeCount [[],[],[],[1,2],[5]]) [] := certificate_1862_checked

theorem certificate_1863_checked : certificate_1863.Valid 16 8 14 certificate_1863_q certificate_1863_edges 6 4 [] := by decide +kernel
theorem certificate_1863_valid : certificate_1863.Valid 16 8 (patternOrder [[],[],[],[1,2,1,2]]) (patternClique [[],[],[],[1,2,1,2]]) (patternEdges [[],[],[],[1,2,1,2]]) (patternAmount [[],[],[],[1,2,1,2]]) (patternEdgeCount [[],[],[],[1,2,1,2]]) [] := certificate_1863_checked

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

theorem patterns_16_8_6_verified_oai : ∀ D ∈ patterns_16_8_6, PatternVerified 16 8 D := by

  simp only [patterns_16_8_6, List.forall_mem_cons]

  exact ⟨⟨certificate_1848, certificate_1848_valid⟩, ⟨⟨certificate_1849, certificate_1849_valid⟩, ⟨⟨certificate_1850, certificate_1850_valid⟩, ⟨⟨certificate_1851, certificate_1851_valid⟩, ⟨⟨certificate_1852, certificate_1852_valid⟩, ⟨⟨certificate_1853, certificate_1853_valid⟩, ⟨⟨certificate_1854, certificate_1854_valid⟩, ⟨⟨certificate_1855, certificate_1855_valid⟩, ⟨⟨certificate_1856, certificate_1856_valid⟩, ⟨⟨certificate_1857, certificate_1857_valid⟩, ⟨⟨certificate_1858, certificate_1858_valid⟩, ⟨⟨certificate_1859, certificate_1859_valid⟩, ⟨⟨certificate_1860, certificate_1860_valid⟩, ⟨⟨certificate_1861, certificate_1861_valid⟩, ⟨⟨certificate_1862, certificate_1862_valid⟩, ⟨⟨certificate_1863, certificate_1863_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_6_verified_oai := @OAI.CycleClique.patterns_16_8_6_verified_oai
