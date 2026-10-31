-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_3_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:50:25.064154+00:00
-- url     : https://prove2.me/submissions/8934df89-f81a-4e9a-8ffe-9503963ad7a5

import Mathlib
import Definitions.Def_OAIQ107D129
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

theorem certificate_1800_checked : certificate_1800.Valid 16 8 15 certificate_1800_q certificate_1800_edges 7 3 [] := by decide +kernel
theorem certificate_1800_valid : certificate_1800.Valid 16 8 (patternOrder [[],[],[],[],[1,4,2]]) (patternClique [[],[],[],[],[1,4,2]]) (patternEdges [[],[],[],[],[1,4,2]]) (patternAmount [[],[],[],[],[1,4,2]]) (patternEdgeCount [[],[],[],[],[1,4,2]]) [] := certificate_1800_checked

theorem certificate_1801_checked : certificate_1801.Valid 16 8 16 certificate_1801_q certificate_1801_edges 8 3 [] := by decide +kernel
theorem certificate_1801_valid : certificate_1801.Valid 16 8 (patternOrder [[],[],[],[],[1,4,3]]) (patternClique [[],[],[],[],[1,4,3]]) (patternEdges [[],[],[],[],[1,4,3]]) (patternAmount [[],[],[],[],[1,4,3]]) (patternEdgeCount [[],[],[],[],[1,4,3]]) [] := certificate_1801_checked

theorem certificate_1802_checked : certificate_1802.Valid 16 8 15 certificate_1802_q certificate_1802_edges 7 3 [] := by decide +kernel
theorem certificate_1802_valid : certificate_1802.Valid 16 8 (patternOrder [[],[],[],[],[1,5,1]]) (patternClique [[],[],[],[],[1,5,1]]) (patternEdges [[],[],[],[],[1,5,1]]) (patternAmount [[],[],[],[],[1,5,1]]) (patternEdgeCount [[],[],[],[],[1,5,1]]) [] := certificate_1802_checked

theorem certificate_1803_checked : certificate_1803.Valid 16 8 16 certificate_1803_q certificate_1803_edges 8 3 [] := by decide +kernel
theorem certificate_1803_valid : certificate_1803.Valid 16 8 (patternOrder [[],[],[],[],[1,5,2]]) (patternClique [[],[],[],[],[1,5,2]]) (patternEdges [[],[],[],[],[1,5,2]]) (patternAmount [[],[],[],[],[1,5,2]]) (patternEdgeCount [[],[],[],[],[1,5,2]]) [] := certificate_1803_checked

theorem certificate_1804_checked : certificate_1804.Valid 16 8 16 certificate_1804_q certificate_1804_edges 8 3 [] := by decide +kernel
theorem certificate_1804_valid : certificate_1804.Valid 16 8 (patternOrder [[],[],[],[],[1,6,1]]) (patternClique [[],[],[],[],[1,6,1]]) (patternEdges [[],[],[],[],[1,6,1]]) (patternAmount [[],[],[],[],[1,6,1]]) (patternEdgeCount [[],[],[],[],[1,6,1]]) [] := certificate_1804_checked

theorem certificate_1805_checked : certificate_1805.Valid 16 8 12 certificate_1805_q certificate_1805_edges 4 2 [] := by decide +kernel
theorem certificate_1805_valid : certificate_1805.Valid 16 8 (patternOrder [[],[],[],[],[2],[2]]) (patternClique [[],[],[],[],[2],[2]]) (patternEdges [[],[],[],[],[2],[2]]) (patternAmount [[],[],[],[],[2],[2]]) (patternEdgeCount [[],[],[],[],[2],[2]]) [] := certificate_1805_checked

theorem certificate_1806_checked : certificate_1806.Valid 16 8 13 certificate_1806_q certificate_1806_edges 5 2 [] := by decide +kernel
theorem certificate_1806_valid : certificate_1806.Valid 16 8 (patternOrder [[],[],[],[],[2],[3]]) (patternClique [[],[],[],[],[2],[3]]) (patternEdges [[],[],[],[],[2],[3]]) (patternAmount [[],[],[],[],[2],[3]]) (patternEdgeCount [[],[],[],[],[2],[3]]) [] := certificate_1806_checked

theorem certificate_1807_checked : certificate_1807.Valid 16 8 14 certificate_1807_q certificate_1807_edges 6 2 [] := by decide +kernel
theorem certificate_1807_valid : certificate_1807.Valid 16 8 (patternOrder [[],[],[],[],[2],[4]]) (patternClique [[],[],[],[],[2],[4]]) (patternEdges [[],[],[],[],[2],[4]]) (patternAmount [[],[],[],[],[2],[4]]) (patternEdgeCount [[],[],[],[],[2],[4]]) [] := certificate_1807_checked

theorem certificate_1808_checked : certificate_1808.Valid 16 8 15 certificate_1808_q certificate_1808_edges 7 2 [] := by decide +kernel
theorem certificate_1808_valid : certificate_1808.Valid 16 8 (patternOrder [[],[],[],[],[2],[5]]) (patternClique [[],[],[],[],[2],[5]]) (patternEdges [[],[],[],[],[2],[5]]) (patternAmount [[],[],[],[],[2],[5]]) (patternEdgeCount [[],[],[],[],[2],[5]]) [] := certificate_1808_checked

theorem certificate_1809_checked : certificate_1809.Valid 16 8 16 certificate_1809_q certificate_1809_edges 8 2 [] := by decide +kernel
theorem certificate_1809_valid : certificate_1809.Valid 16 8 (patternOrder [[],[],[],[],[2],[6]]) (patternClique [[],[],[],[],[2],[6]]) (patternEdges [[],[],[],[],[2],[6]]) (patternAmount [[],[],[],[],[2],[6]]) (patternEdgeCount [[],[],[],[],[2],[6]]) [] := certificate_1809_checked

theorem certificate_1810_checked : certificate_1810.Valid 16 8 13 certificate_1810_q certificate_1810_edges 5 3 [] := by decide +kernel
theorem certificate_1810_valid : certificate_1810.Valid 16 8 (patternOrder [[],[],[],[],[2,1,2]]) (patternClique [[],[],[],[],[2,1,2]]) (patternEdges [[],[],[],[],[2,1,2]]) (patternAmount [[],[],[],[],[2,1,2]]) (patternEdgeCount [[],[],[],[],[2,1,2]]) [] := certificate_1810_checked

theorem certificate_1811_checked : certificate_1811.Valid 16 8 14 certificate_1811_q certificate_1811_edges 6 3 [] := by decide +kernel
theorem certificate_1811_valid : certificate_1811.Valid 16 8 (patternOrder [[],[],[],[],[2,1,3]]) (patternClique [[],[],[],[],[2,1,3]]) (patternEdges [[],[],[],[],[2,1,3]]) (patternAmount [[],[],[],[],[2,1,3]]) (patternEdgeCount [[],[],[],[],[2,1,3]]) [] := certificate_1811_checked

theorem certificate_1812_checked : certificate_1812.Valid 16 8 15 certificate_1812_q certificate_1812_edges 7 3 [] := by decide +kernel
theorem certificate_1812_valid : certificate_1812.Valid 16 8 (patternOrder [[],[],[],[],[2,1,4]]) (patternClique [[],[],[],[],[2,1,4]]) (patternEdges [[],[],[],[],[2,1,4]]) (patternAmount [[],[],[],[],[2,1,4]]) (patternEdgeCount [[],[],[],[],[2,1,4]]) [] := certificate_1812_checked

theorem certificate_1813_checked : certificate_1813.Valid 16 8 16 certificate_1813_q certificate_1813_edges 8 3 [] := by decide +kernel
theorem certificate_1813_valid : certificate_1813.Valid 16 8 (patternOrder [[],[],[],[],[2,1,5]]) (patternClique [[],[],[],[],[2,1,5]]) (patternEdges [[],[],[],[],[2,1,5]]) (patternAmount [[],[],[],[],[2,1,5]]) (patternEdgeCount [[],[],[],[],[2,1,5]]) [] := certificate_1813_checked

theorem certificate_1814_checked : certificate_1814.Valid 16 8 14 certificate_1814_q certificate_1814_edges 6 3 [] := by decide +kernel
theorem certificate_1814_valid : certificate_1814.Valid 16 8 (patternOrder [[],[],[],[],[2,2,2]]) (patternClique [[],[],[],[],[2,2,2]]) (patternEdges [[],[],[],[],[2,2,2]]) (patternAmount [[],[],[],[],[2,2,2]]) (patternEdgeCount [[],[],[],[],[2,2,2]]) [] := certificate_1814_checked

theorem certificate_1815_checked : certificate_1815.Valid 16 8 15 certificate_1815_q certificate_1815_edges 7 3 [] := by decide +kernel
theorem certificate_1815_valid : certificate_1815.Valid 16 8 (patternOrder [[],[],[],[],[2,2,3]]) (patternClique [[],[],[],[],[2,2,3]]) (patternEdges [[],[],[],[],[2,2,3]]) (patternAmount [[],[],[],[],[2,2,3]]) (patternEdgeCount [[],[],[],[],[2,2,3]]) [] := certificate_1815_checked

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

theorem patterns_16_8_3_verified_oai : ∀ D ∈ patterns_16_8_3, PatternVerified 16 8 D := by

  simp only [patterns_16_8_3, List.forall_mem_cons]

  exact ⟨⟨certificate_1800, certificate_1800_valid⟩, ⟨⟨certificate_1801, certificate_1801_valid⟩, ⟨⟨certificate_1802, certificate_1802_valid⟩, ⟨⟨certificate_1803, certificate_1803_valid⟩, ⟨⟨certificate_1804, certificate_1804_valid⟩, ⟨⟨certificate_1805, certificate_1805_valid⟩, ⟨⟨certificate_1806, certificate_1806_valid⟩, ⟨⟨certificate_1807, certificate_1807_valid⟩, ⟨⟨certificate_1808, certificate_1808_valid⟩, ⟨⟨certificate_1809, certificate_1809_valid⟩, ⟨⟨certificate_1810, certificate_1810_valid⟩, ⟨⟨certificate_1811, certificate_1811_valid⟩, ⟨⟨certificate_1812, certificate_1812_valid⟩, ⟨⟨certificate_1813, certificate_1813_valid⟩, ⟨⟨certificate_1814, certificate_1814_valid⟩, ⟨⟨certificate_1815, certificate_1815_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_3_verified_oai := @OAI.CycleClique.patterns_16_8_3_verified_oai
