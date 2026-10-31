-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_1_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:42:39.969309+00:00
-- url     : https://prove2.me/submissions/6608a0f6-9d5b-469c-bb70-35b8f0d44321

import Mathlib
import Definitions.Def_OAIQ107D129
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates056
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1768_checked : certificate_1768.Valid 16 8 12 certificate_1768_q certificate_1768_edges 4 2 [] := by decide +kernel
theorem certificate_1768_valid : certificate_1768.Valid 16 8 (patternOrder [[],[],[],[],[],[2,2]]) (patternClique [[],[],[],[],[],[2,2]]) (patternEdges [[],[],[],[],[],[2,2]]) (patternAmount [[],[],[],[],[],[2,2]]) (patternEdgeCount [[],[],[],[],[],[2,2]]) [] := certificate_1768_checked

theorem certificate_1769_checked : certificate_1769.Valid 16 8 13 certificate_1769_q certificate_1769_edges 5 2 [] := by decide +kernel
theorem certificate_1769_valid : certificate_1769.Valid 16 8 (patternOrder [[],[],[],[],[],[2,3]]) (patternClique [[],[],[],[],[],[2,3]]) (patternEdges [[],[],[],[],[],[2,3]]) (patternAmount [[],[],[],[],[],[2,3]]) (patternEdgeCount [[],[],[],[],[],[2,3]]) [] := certificate_1769_checked

theorem certificate_1770_checked : certificate_1770.Valid 16 8 14 certificate_1770_q certificate_1770_edges 6 2 [] := by decide +kernel
theorem certificate_1770_valid : certificate_1770.Valid 16 8 (patternOrder [[],[],[],[],[],[2,4]]) (patternClique [[],[],[],[],[],[2,4]]) (patternEdges [[],[],[],[],[],[2,4]]) (patternAmount [[],[],[],[],[],[2,4]]) (patternEdgeCount [[],[],[],[],[],[2,4]]) [] := certificate_1770_checked

theorem certificate_1771_checked : certificate_1771.Valid 16 8 15 certificate_1771_q certificate_1771_edges 7 2 [] := by decide +kernel
theorem certificate_1771_valid : certificate_1771.Valid 16 8 (patternOrder [[],[],[],[],[],[2,5]]) (patternClique [[],[],[],[],[],[2,5]]) (patternEdges [[],[],[],[],[],[2,5]]) (patternAmount [[],[],[],[],[],[2,5]]) (patternEdgeCount [[],[],[],[],[],[2,5]]) [] := certificate_1771_checked

theorem certificate_1772_checked : certificate_1772.Valid 16 8 16 certificate_1772_q certificate_1772_edges 8 2 [] := by decide +kernel
theorem certificate_1772_valid : certificate_1772.Valid 16 8 (patternOrder [[],[],[],[],[],[2,6]]) (patternClique [[],[],[],[],[],[2,6]]) (patternEdges [[],[],[],[],[],[2,6]]) (patternAmount [[],[],[],[],[],[2,6]]) (patternEdgeCount [[],[],[],[],[],[2,6]]) [] := certificate_1772_checked

theorem certificate_1773_checked : certificate_1773.Valid 16 8 14 certificate_1773_q certificate_1773_edges 6 2 [] := by decide +kernel
theorem certificate_1773_valid : certificate_1773.Valid 16 8 (patternOrder [[],[],[],[],[],[3,3]]) (patternClique [[],[],[],[],[],[3,3]]) (patternEdges [[],[],[],[],[],[3,3]]) (patternAmount [[],[],[],[],[],[3,3]]) (patternEdgeCount [[],[],[],[],[],[3,3]]) [] := certificate_1773_checked

theorem certificate_1774_checked : certificate_1774.Valid 16 8 15 certificate_1774_q certificate_1774_edges 7 2 [] := by decide +kernel
theorem certificate_1774_valid : certificate_1774.Valid 16 8 (patternOrder [[],[],[],[],[],[3,4]]) (patternClique [[],[],[],[],[],[3,4]]) (patternEdges [[],[],[],[],[],[3,4]]) (patternAmount [[],[],[],[],[],[3,4]]) (patternEdgeCount [[],[],[],[],[],[3,4]]) [] := certificate_1774_checked

theorem certificate_1775_checked : certificate_1775.Valid 16 8 16 certificate_1775_q certificate_1775_edges 8 2 [] := by decide +kernel
theorem certificate_1775_valid : certificate_1775.Valid 16 8 (patternOrder [[],[],[],[],[],[3,5]]) (patternClique [[],[],[],[],[],[3,5]]) (patternEdges [[],[],[],[],[],[3,5]]) (patternAmount [[],[],[],[],[],[3,5]]) (patternEdgeCount [[],[],[],[],[],[3,5]]) [] := certificate_1775_checked

theorem certificate_1776_checked : certificate_1776.Valid 16 8 16 certificate_1776_q certificate_1776_edges 8 2 [] := by decide +kernel
theorem certificate_1776_valid : certificate_1776.Valid 16 8 (patternOrder [[],[],[],[],[],[4,4]]) (patternClique [[],[],[],[],[],[4,4]]) (patternEdges [[],[],[],[],[],[4,4]]) (patternAmount [[],[],[],[],[],[4,4]]) (patternEdgeCount [[],[],[],[],[],[4,4]]) [] := certificate_1776_checked

theorem certificate_1777_checked : certificate_1777.Valid 16 8 10 certificate_1777_q certificate_1777_edges 2 2 [] := by decide +kernel
theorem certificate_1777_valid : certificate_1777.Valid 16 8 (patternOrder [[],[],[],[],[1],[1]]) (patternClique [[],[],[],[],[1],[1]]) (patternEdges [[],[],[],[],[1],[1]]) (patternAmount [[],[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[],[1],[1]]) [] := certificate_1777_checked

theorem certificate_1778_checked : certificate_1778.Valid 16 8 11 certificate_1778_q certificate_1778_edges 3 2 [] := by decide +kernel
theorem certificate_1778_valid : certificate_1778.Valid 16 8 (patternOrder [[],[],[],[],[1],[2]]) (patternClique [[],[],[],[],[1],[2]]) (patternEdges [[],[],[],[],[1],[2]]) (patternAmount [[],[],[],[],[1],[2]]) (patternEdgeCount [[],[],[],[],[1],[2]]) [] := certificate_1778_checked

theorem certificate_1779_checked : certificate_1779.Valid 16 8 12 certificate_1779_q certificate_1779_edges 4 2 [] := by decide +kernel
theorem certificate_1779_valid : certificate_1779.Valid 16 8 (patternOrder [[],[],[],[],[1],[3]]) (patternClique [[],[],[],[],[1],[3]]) (patternEdges [[],[],[],[],[1],[3]]) (patternAmount [[],[],[],[],[1],[3]]) (patternEdgeCount [[],[],[],[],[1],[3]]) [] := certificate_1779_checked

theorem certificate_1780_checked : certificate_1780.Valid 16 8 13 certificate_1780_q certificate_1780_edges 5 2 [] := by decide +kernel
theorem certificate_1780_valid : certificate_1780.Valid 16 8 (patternOrder [[],[],[],[],[1],[4]]) (patternClique [[],[],[],[],[1],[4]]) (patternEdges [[],[],[],[],[1],[4]]) (patternAmount [[],[],[],[],[1],[4]]) (patternEdgeCount [[],[],[],[],[1],[4]]) [] := certificate_1780_checked

theorem certificate_1781_checked : certificate_1781.Valid 16 8 14 certificate_1781_q certificate_1781_edges 6 2 [] := by decide +kernel
theorem certificate_1781_valid : certificate_1781.Valid 16 8 (patternOrder [[],[],[],[],[1],[5]]) (patternClique [[],[],[],[],[1],[5]]) (patternEdges [[],[],[],[],[1],[5]]) (patternAmount [[],[],[],[],[1],[5]]) (patternEdgeCount [[],[],[],[],[1],[5]]) [] := certificate_1781_checked

theorem certificate_1782_checked : certificate_1782.Valid 16 8 15 certificate_1782_q certificate_1782_edges 7 2 [] := by decide +kernel
theorem certificate_1782_valid : certificate_1782.Valid 16 8 (patternOrder [[],[],[],[],[1],[6]]) (patternClique [[],[],[],[],[1],[6]]) (patternEdges [[],[],[],[],[1],[6]]) (patternAmount [[],[],[],[],[1],[6]]) (patternEdgeCount [[],[],[],[],[1],[6]]) [] := certificate_1782_checked

theorem certificate_1783_checked : certificate_1783.Valid 16 8 16 certificate_1783_q certificate_1783_edges 8 2 [] := by decide +kernel
theorem certificate_1783_valid : certificate_1783.Valid 16 8 (patternOrder [[],[],[],[],[1],[7]]) (patternClique [[],[],[],[],[1],[7]]) (patternEdges [[],[],[],[],[1],[7]]) (patternAmount [[],[],[],[],[1],[7]]) (patternEdgeCount [[],[],[],[],[1],[7]]) [] := certificate_1783_checked

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

theorem patterns_16_8_1_verified_oai : ∀ D ∈ patterns_16_8_1, PatternVerified 16 8 D := by

  simp only [patterns_16_8_1, List.forall_mem_cons]

  exact ⟨⟨certificate_1768, certificate_1768_valid⟩, ⟨⟨certificate_1769, certificate_1769_valid⟩, ⟨⟨certificate_1770, certificate_1770_valid⟩, ⟨⟨certificate_1771, certificate_1771_valid⟩, ⟨⟨certificate_1772, certificate_1772_valid⟩, ⟨⟨certificate_1773, certificate_1773_valid⟩, ⟨⟨certificate_1774, certificate_1774_valid⟩, ⟨⟨certificate_1775, certificate_1775_valid⟩, ⟨⟨certificate_1776, certificate_1776_valid⟩, ⟨⟨certificate_1777, certificate_1777_valid⟩, ⟨⟨certificate_1778, certificate_1778_valid⟩, ⟨⟨certificate_1779, certificate_1779_valid⟩, ⟨⟨certificate_1780, certificate_1780_valid⟩, ⟨⟨certificate_1781, certificate_1781_valid⟩, ⟨⟨certificate_1782, certificate_1782_valid⟩, ⟨⟨certificate_1783, certificate_1783_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_1_verified_oai := @OAI.CycleClique.patterns_16_8_1_verified_oai
