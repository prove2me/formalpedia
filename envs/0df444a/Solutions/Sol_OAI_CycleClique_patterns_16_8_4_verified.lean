-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_4_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:51:52.531606+00:00
-- url     : https://prove2.me/submissions/54d0111e-0c1f-475e-b609-85637f906038

import Mathlib
import Definitions.Def_OAIQ107D003
import Definitions.Def_OAIQ107D053
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates057
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1816_checked : certificate_1816.Valid 16 8 16 certificate_1816_q certificate_1816_edges 8 3 [] := by decide +kernel
theorem certificate_1816_valid : certificate_1816.Valid 16 8 (patternOrder [[],[],[],[],[2,2,4]]) (patternClique [[],[],[],[],[2,2,4]]) (patternEdges [[],[],[],[],[2,2,4]]) (patternAmount [[],[],[],[],[2,2,4]]) (patternEdgeCount [[],[],[],[],[2,2,4]]) [] := certificate_1816_checked

theorem certificate_1817_checked : certificate_1817.Valid 16 8 15 certificate_1817_q certificate_1817_edges 7 3 [] := by decide +kernel
theorem certificate_1817_valid : certificate_1817.Valid 16 8 (patternOrder [[],[],[],[],[2,3,2]]) (patternClique [[],[],[],[],[2,3,2]]) (patternEdges [[],[],[],[],[2,3,2]]) (patternAmount [[],[],[],[],[2,3,2]]) (patternEdgeCount [[],[],[],[],[2,3,2]]) [] := certificate_1817_checked

theorem certificate_1818_checked : certificate_1818.Valid 16 8 16 certificate_1818_q certificate_1818_edges 8 3 [] := by decide +kernel
theorem certificate_1818_valid : certificate_1818.Valid 16 8 (patternOrder [[],[],[],[],[2,3,3]]) (patternClique [[],[],[],[],[2,3,3]]) (patternEdges [[],[],[],[],[2,3,3]]) (patternAmount [[],[],[],[],[2,3,3]]) (patternEdgeCount [[],[],[],[],[2,3,3]]) [] := certificate_1818_checked

theorem certificate_1819_checked : certificate_1819.Valid 16 8 16 certificate_1819_q certificate_1819_edges 8 3 [] := by decide +kernel
theorem certificate_1819_valid : certificate_1819.Valid 16 8 (patternOrder [[],[],[],[],[2,4,2]]) (patternClique [[],[],[],[],[2,4,2]]) (patternEdges [[],[],[],[],[2,4,2]]) (patternAmount [[],[],[],[],[2,4,2]]) (patternEdgeCount [[],[],[],[],[2,4,2]]) [] := certificate_1819_checked

theorem certificate_1820_checked : certificate_1820.Valid 16 8 14 certificate_1820_q certificate_1820_edges 6 2 [] := by decide +kernel
theorem certificate_1820_valid : certificate_1820.Valid 16 8 (patternOrder [[],[],[],[],[3],[3]]) (patternClique [[],[],[],[],[3],[3]]) (patternEdges [[],[],[],[],[3],[3]]) (patternAmount [[],[],[],[],[3],[3]]) (patternEdgeCount [[],[],[],[],[3],[3]]) [] := certificate_1820_checked

theorem certificate_1821_checked : certificate_1821.Valid 16 8 15 certificate_1821_q certificate_1821_edges 7 2 [] := by decide +kernel
theorem certificate_1821_valid : certificate_1821.Valid 16 8 (patternOrder [[],[],[],[],[3],[4]]) (patternClique [[],[],[],[],[3],[4]]) (patternEdges [[],[],[],[],[3],[4]]) (patternAmount [[],[],[],[],[3],[4]]) (patternEdgeCount [[],[],[],[],[3],[4]]) [] := certificate_1821_checked

theorem certificate_1822_checked : certificate_1822.Valid 16 8 16 certificate_1822_q certificate_1822_edges 8 2 [] := by decide +kernel
theorem certificate_1822_valid : certificate_1822.Valid 16 8 (patternOrder [[],[],[],[],[3],[5]]) (patternClique [[],[],[],[],[3],[5]]) (patternEdges [[],[],[],[],[3],[5]]) (patternAmount [[],[],[],[],[3],[5]]) (patternEdgeCount [[],[],[],[],[3],[5]]) [] := certificate_1822_checked

theorem certificate_1823_checked : certificate_1823.Valid 16 8 15 certificate_1823_q certificate_1823_edges 7 3 [] := by decide +kernel
theorem certificate_1823_valid : certificate_1823.Valid 16 8 (patternOrder [[],[],[],[],[3,1,3]]) (patternClique [[],[],[],[],[3,1,3]]) (patternEdges [[],[],[],[],[3,1,3]]) (patternAmount [[],[],[],[],[3,1,3]]) (patternEdgeCount [[],[],[],[],[3,1,3]]) [] := certificate_1823_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates058
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1824_checked : certificate_1824.Valid 16 8 16 certificate_1824_q certificate_1824_edges 8 3 [] := by decide +kernel
theorem certificate_1824_valid : certificate_1824.Valid 16 8 (patternOrder [[],[],[],[],[3,1,4]]) (patternClique [[],[],[],[],[3,1,4]]) (patternEdges [[],[],[],[],[3,1,4]]) (patternAmount [[],[],[],[],[3,1,4]]) (patternEdgeCount [[],[],[],[],[3,1,4]]) [] := certificate_1824_checked

theorem certificate_1825_checked : certificate_1825.Valid 16 8 16 certificate_1825_q certificate_1825_edges 8 3 [] := by decide +kernel
theorem certificate_1825_valid : certificate_1825.Valid 16 8 (patternOrder [[],[],[],[],[3,2,3]]) (patternClique [[],[],[],[],[3,2,3]]) (patternEdges [[],[],[],[],[3,2,3]]) (patternAmount [[],[],[],[],[3,2,3]]) (patternEdgeCount [[],[],[],[],[3,2,3]]) [] := certificate_1825_checked

theorem certificate_1826_checked : certificate_1826.Valid 16 8 16 certificate_1826_q certificate_1826_edges 8 2 [] := by decide +kernel
theorem certificate_1826_valid : certificate_1826.Valid 16 8 (patternOrder [[],[],[],[],[4],[4]]) (patternClique [[],[],[],[],[4],[4]]) (patternEdges [[],[],[],[],[4],[4]]) (patternAmount [[],[],[],[],[4],[4]]) (patternEdgeCount [[],[],[],[],[4],[4]]) [] := certificate_1826_checked

theorem certificate_1827_checked : certificate_1827.Valid 16 8 11 certificate_1827_q certificate_1827_edges 3 3 [] := by decide +kernel
theorem certificate_1827_valid : certificate_1827.Valid 16 8 (patternOrder [[],[],[],[1],[1,1]]) (patternClique [[],[],[],[1],[1,1]]) (patternEdges [[],[],[],[1],[1,1]]) (patternAmount [[],[],[],[1],[1,1]]) (patternEdgeCount [[],[],[],[1],[1,1]]) [] := certificate_1827_checked

theorem certificate_1828_checked : certificate_1828.Valid 16 8 12 certificate_1828_q certificate_1828_edges 4 3 [] := by decide +kernel
theorem certificate_1828_valid : certificate_1828.Valid 16 8 (patternOrder [[],[],[],[1],[1,2]]) (patternClique [[],[],[],[1],[1,2]]) (patternEdges [[],[],[],[1],[1,2]]) (patternAmount [[],[],[],[1],[1,2]]) (patternEdgeCount [[],[],[],[1],[1,2]]) [] := certificate_1828_checked

theorem certificate_1829_checked : certificate_1829.Valid 16 8 13 certificate_1829_q certificate_1829_edges 5 3 [] := by decide +kernel
theorem certificate_1829_valid : certificate_1829.Valid 16 8 (patternOrder [[],[],[],[1],[1,3]]) (patternClique [[],[],[],[1],[1,3]]) (patternEdges [[],[],[],[1],[1,3]]) (patternAmount [[],[],[],[1],[1,3]]) (patternEdgeCount [[],[],[],[1],[1,3]]) [] := certificate_1829_checked

theorem certificate_1830_checked : certificate_1830.Valid 16 8 14 certificate_1830_q certificate_1830_edges 6 3 [] := by decide +kernel
theorem certificate_1830_valid : certificate_1830.Valid 16 8 (patternOrder [[],[],[],[1],[1,4]]) (patternClique [[],[],[],[1],[1,4]]) (patternEdges [[],[],[],[1],[1,4]]) (patternAmount [[],[],[],[1],[1,4]]) (patternEdgeCount [[],[],[],[1],[1,4]]) [] := certificate_1830_checked

theorem certificate_1831_checked : certificate_1831.Valid 16 8 15 certificate_1831_q certificate_1831_edges 7 3 [] := by decide +kernel
theorem certificate_1831_valid : certificate_1831.Valid 16 8 (patternOrder [[],[],[],[1],[1,5]]) (patternClique [[],[],[],[1],[1,5]]) (patternEdges [[],[],[],[1],[1,5]]) (patternAmount [[],[],[],[1],[1,5]]) (patternEdgeCount [[],[],[],[1],[1,5]]) [] := certificate_1831_checked

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

theorem patterns_16_8_4_verified_oai : ∀ D ∈ patterns_16_8_4, PatternVerified 16 8 D := by

  simp only [patterns_16_8_4, List.forall_mem_cons]

  exact ⟨⟨certificate_1816, certificate_1816_valid⟩, ⟨⟨certificate_1817, certificate_1817_valid⟩, ⟨⟨certificate_1818, certificate_1818_valid⟩, ⟨⟨certificate_1819, certificate_1819_valid⟩, ⟨⟨certificate_1820, certificate_1820_valid⟩, ⟨⟨certificate_1821, certificate_1821_valid⟩, ⟨⟨certificate_1822, certificate_1822_valid⟩, ⟨⟨certificate_1823, certificate_1823_valid⟩, ⟨⟨certificate_1824, certificate_1824_valid⟩, ⟨⟨certificate_1825, certificate_1825_valid⟩, ⟨⟨certificate_1826, certificate_1826_valid⟩, ⟨⟨certificate_1827, certificate_1827_valid⟩, ⟨⟨certificate_1828, certificate_1828_valid⟩, ⟨⟨certificate_1829, certificate_1829_valid⟩, ⟨⟨certificate_1830, certificate_1830_valid⟩, ⟨⟨certificate_1831, certificate_1831_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_4_verified_oai := @OAI.CycleClique.patterns_16_8_4_verified_oai
