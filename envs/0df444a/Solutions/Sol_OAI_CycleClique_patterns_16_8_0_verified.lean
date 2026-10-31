-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_0_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:21:44.798768+00:00
-- url     : https://prove2.me/submissions/58d22ac5-3e40-4ce8-b179-67644397d017

import Mathlib
import Definitions.Def_OAIQ107D129
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates055
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1752_checked : certificate_1752.Valid 16 8 8 certificate_1752_q certificate_1752_edges 0 0 [] := by decide +kernel
theorem certificate_1752_valid : certificate_1752.Valid 16 8 (patternOrder [[],[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[],[]]) [] := certificate_1752_checked

theorem certificate_1753_checked : certificate_1753.Valid 16 8 9 certificate_1753_q certificate_1753_edges 1 1 [] := by decide +kernel
theorem certificate_1753_valid : certificate_1753.Valid 16 8 (patternOrder [[],[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[],[1]]) [] := certificate_1753_checked

theorem certificate_1754_checked : certificate_1754.Valid 16 8 10 certificate_1754_q certificate_1754_edges 2 1 [] := by decide +kernel
theorem certificate_1754_valid : certificate_1754.Valid 16 8 (patternOrder [[],[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[],[2]]) [] := certificate_1754_checked

theorem certificate_1755_checked : certificate_1755.Valid 16 8 11 certificate_1755_q certificate_1755_edges 3 1 [] := by decide +kernel
theorem certificate_1755_valid : certificate_1755.Valid 16 8 (patternOrder [[],[],[],[],[],[],[3]]) (patternClique [[],[],[],[],[],[],[3]]) (patternEdges [[],[],[],[],[],[],[3]]) (patternAmount [[],[],[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[],[],[3]]) [] := certificate_1755_checked

theorem certificate_1756_checked : certificate_1756.Valid 16 8 12 certificate_1756_q certificate_1756_edges 4 1 [] := by decide +kernel
theorem certificate_1756_valid : certificate_1756.Valid 16 8 (patternOrder [[],[],[],[],[],[],[4]]) (patternClique [[],[],[],[],[],[],[4]]) (patternEdges [[],[],[],[],[],[],[4]]) (patternAmount [[],[],[],[],[],[],[4]]) (patternEdgeCount [[],[],[],[],[],[],[4]]) [] := certificate_1756_checked

theorem certificate_1757_checked : certificate_1757.Valid 16 8 13 certificate_1757_q certificate_1757_edges 5 1 [] := by decide +kernel
theorem certificate_1757_valid : certificate_1757.Valid 16 8 (patternOrder [[],[],[],[],[],[],[5]]) (patternClique [[],[],[],[],[],[],[5]]) (patternEdges [[],[],[],[],[],[],[5]]) (patternAmount [[],[],[],[],[],[],[5]]) (patternEdgeCount [[],[],[],[],[],[],[5]]) [] := certificate_1757_checked

theorem certificate_1758_checked : certificate_1758.Valid 16 8 14 certificate_1758_q certificate_1758_edges 6 1 [] := by decide +kernel
theorem certificate_1758_valid : certificate_1758.Valid 16 8 (patternOrder [[],[],[],[],[],[],[6]]) (patternClique [[],[],[],[],[],[],[6]]) (patternEdges [[],[],[],[],[],[],[6]]) (patternAmount [[],[],[],[],[],[],[6]]) (patternEdgeCount [[],[],[],[],[],[],[6]]) [] := certificate_1758_checked

theorem certificate_1759_checked : certificate_1759.Valid 16 8 15 certificate_1759_q certificate_1759_edges 7 1 [] := by decide +kernel
theorem certificate_1759_valid : certificate_1759.Valid 16 8 (patternOrder [[],[],[],[],[],[],[7]]) (patternClique [[],[],[],[],[],[],[7]]) (patternEdges [[],[],[],[],[],[],[7]]) (patternAmount [[],[],[],[],[],[],[7]]) (patternEdgeCount [[],[],[],[],[],[],[7]]) [] := certificate_1759_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates056
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1760_checked : certificate_1760.Valid 16 8 16 certificate_1760_q certificate_1760_edges 8 1 [] := by decide +kernel
theorem certificate_1760_valid : certificate_1760.Valid 16 8 (patternOrder [[],[],[],[],[],[],[8]]) (patternClique [[],[],[],[],[],[],[8]]) (patternEdges [[],[],[],[],[],[],[8]]) (patternAmount [[],[],[],[],[],[],[8]]) (patternEdgeCount [[],[],[],[],[],[],[8]]) [] := certificate_1760_checked

theorem certificate_1761_checked : certificate_1761.Valid 16 8 10 certificate_1761_q certificate_1761_edges 2 2 [] := by decide +kernel
theorem certificate_1761_valid : certificate_1761.Valid 16 8 (patternOrder [[],[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[],[1,1]]) [] := certificate_1761_checked

theorem certificate_1762_checked : certificate_1762.Valid 16 8 11 certificate_1762_q certificate_1762_edges 3 2 [] := by decide +kernel
theorem certificate_1762_valid : certificate_1762.Valid 16 8 (patternOrder [[],[],[],[],[],[1,2]]) (patternClique [[],[],[],[],[],[1,2]]) (patternEdges [[],[],[],[],[],[1,2]]) (patternAmount [[],[],[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[],[],[1,2]]) [] := certificate_1762_checked

theorem certificate_1763_checked : certificate_1763.Valid 16 8 12 certificate_1763_q certificate_1763_edges 4 2 [] := by decide +kernel
theorem certificate_1763_valid : certificate_1763.Valid 16 8 (patternOrder [[],[],[],[],[],[1,3]]) (patternClique [[],[],[],[],[],[1,3]]) (patternEdges [[],[],[],[],[],[1,3]]) (patternAmount [[],[],[],[],[],[1,3]]) (patternEdgeCount [[],[],[],[],[],[1,3]]) [] := certificate_1763_checked

theorem certificate_1764_checked : certificate_1764.Valid 16 8 13 certificate_1764_q certificate_1764_edges 5 2 [] := by decide +kernel
theorem certificate_1764_valid : certificate_1764.Valid 16 8 (patternOrder [[],[],[],[],[],[1,4]]) (patternClique [[],[],[],[],[],[1,4]]) (patternEdges [[],[],[],[],[],[1,4]]) (patternAmount [[],[],[],[],[],[1,4]]) (patternEdgeCount [[],[],[],[],[],[1,4]]) [] := certificate_1764_checked

theorem certificate_1765_checked : certificate_1765.Valid 16 8 14 certificate_1765_q certificate_1765_edges 6 2 [] := by decide +kernel
theorem certificate_1765_valid : certificate_1765.Valid 16 8 (patternOrder [[],[],[],[],[],[1,5]]) (patternClique [[],[],[],[],[],[1,5]]) (patternEdges [[],[],[],[],[],[1,5]]) (patternAmount [[],[],[],[],[],[1,5]]) (patternEdgeCount [[],[],[],[],[],[1,5]]) [] := certificate_1765_checked

theorem certificate_1766_checked : certificate_1766.Valid 16 8 15 certificate_1766_q certificate_1766_edges 7 2 [] := by decide +kernel
theorem certificate_1766_valid : certificate_1766.Valid 16 8 (patternOrder [[],[],[],[],[],[1,6]]) (patternClique [[],[],[],[],[],[1,6]]) (patternEdges [[],[],[],[],[],[1,6]]) (patternAmount [[],[],[],[],[],[1,6]]) (patternEdgeCount [[],[],[],[],[],[1,6]]) [] := certificate_1766_checked

theorem certificate_1767_checked : certificate_1767.Valid 16 8 16 certificate_1767_q certificate_1767_edges 8 2 [] := by decide +kernel
theorem certificate_1767_valid : certificate_1767.Valid 16 8 (patternOrder [[],[],[],[],[],[1,7]]) (patternClique [[],[],[],[],[],[1,7]]) (patternEdges [[],[],[],[],[],[1,7]]) (patternAmount [[],[],[],[],[],[1,7]]) (patternEdgeCount [[],[],[],[],[],[1,7]]) [] := certificate_1767_checked

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

theorem patterns_16_8_0_verified_oai : ∀ D ∈ patterns_16_8_0, PatternVerified 16 8 D := by

  simp only [patterns_16_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_1752, certificate_1752_valid⟩, ⟨⟨certificate_1753, certificate_1753_valid⟩, ⟨⟨certificate_1754, certificate_1754_valid⟩, ⟨⟨certificate_1755, certificate_1755_valid⟩, ⟨⟨certificate_1756, certificate_1756_valid⟩, ⟨⟨certificate_1757, certificate_1757_valid⟩, ⟨⟨certificate_1758, certificate_1758_valid⟩, ⟨⟨certificate_1759, certificate_1759_valid⟩, ⟨⟨certificate_1760, certificate_1760_valid⟩, ⟨⟨certificate_1761, certificate_1761_valid⟩, ⟨⟨certificate_1762, certificate_1762_valid⟩, ⟨⟨certificate_1763, certificate_1763_valid⟩, ⟨⟨certificate_1764, certificate_1764_valid⟩, ⟨⟨certificate_1765, certificate_1765_valid⟩, ⟨⟨certificate_1766, certificate_1766_valid⟩, ⟨⟨certificate_1767, certificate_1767_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_0_verified_oai := @OAI.CycleClique.patterns_16_8_0_verified_oai
