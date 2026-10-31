-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_2_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:50:01.210605+00:00
-- url     : https://prove2.me/submissions/675eb070-3ef3-4696-af31-870dea29ec54

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

theorem certificate_1784_checked : certificate_1784.Valid 16 8 11 certificate_1784_q certificate_1784_edges 3 3 [] := by decide +kernel
theorem certificate_1784_valid : certificate_1784.Valid 16 8 (patternOrder [[],[],[],[],[1,1,1]]) (patternClique [[],[],[],[],[1,1,1]]) (patternEdges [[],[],[],[],[1,1,1]]) (patternAmount [[],[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[],[1,1,1]]) [] := certificate_1784_checked

theorem certificate_1785_checked : certificate_1785.Valid 16 8 12 certificate_1785_q certificate_1785_edges 4 3 [] := by decide +kernel
theorem certificate_1785_valid : certificate_1785.Valid 16 8 (patternOrder [[],[],[],[],[1,1,2]]) (patternClique [[],[],[],[],[1,1,2]]) (patternEdges [[],[],[],[],[1,1,2]]) (patternAmount [[],[],[],[],[1,1,2]]) (patternEdgeCount [[],[],[],[],[1,1,2]]) [] := certificate_1785_checked

theorem certificate_1786_checked : certificate_1786.Valid 16 8 13 certificate_1786_q certificate_1786_edges 5 3 [] := by decide +kernel
theorem certificate_1786_valid : certificate_1786.Valid 16 8 (patternOrder [[],[],[],[],[1,1,3]]) (patternClique [[],[],[],[],[1,1,3]]) (patternEdges [[],[],[],[],[1,1,3]]) (patternAmount [[],[],[],[],[1,1,3]]) (patternEdgeCount [[],[],[],[],[1,1,3]]) [] := certificate_1786_checked

theorem certificate_1787_checked : certificate_1787.Valid 16 8 14 certificate_1787_q certificate_1787_edges 6 3 [] := by decide +kernel
theorem certificate_1787_valid : certificate_1787.Valid 16 8 (patternOrder [[],[],[],[],[1,1,4]]) (patternClique [[],[],[],[],[1,1,4]]) (patternEdges [[],[],[],[],[1,1,4]]) (patternAmount [[],[],[],[],[1,1,4]]) (patternEdgeCount [[],[],[],[],[1,1,4]]) [] := certificate_1787_checked

theorem certificate_1788_checked : certificate_1788.Valid 16 8 15 certificate_1788_q certificate_1788_edges 7 3 [] := by decide +kernel
theorem certificate_1788_valid : certificate_1788.Valid 16 8 (patternOrder [[],[],[],[],[1,1,5]]) (patternClique [[],[],[],[],[1,1,5]]) (patternEdges [[],[],[],[],[1,1,5]]) (patternAmount [[],[],[],[],[1,1,5]]) (patternEdgeCount [[],[],[],[],[1,1,5]]) [] := certificate_1788_checked

theorem certificate_1789_checked : certificate_1789.Valid 16 8 16 certificate_1789_q certificate_1789_edges 8 3 [] := by decide +kernel
theorem certificate_1789_valid : certificate_1789.Valid 16 8 (patternOrder [[],[],[],[],[1,1,6]]) (patternClique [[],[],[],[],[1,1,6]]) (patternEdges [[],[],[],[],[1,1,6]]) (patternAmount [[],[],[],[],[1,1,6]]) (patternEdgeCount [[],[],[],[],[1,1,6]]) [] := certificate_1789_checked

theorem certificate_1790_checked : certificate_1790.Valid 16 8 12 certificate_1790_q certificate_1790_edges 4 3 [] := by decide +kernel
theorem certificate_1790_valid : certificate_1790.Valid 16 8 (patternOrder [[],[],[],[],[1,2,1]]) (patternClique [[],[],[],[],[1,2,1]]) (patternEdges [[],[],[],[],[1,2,1]]) (patternAmount [[],[],[],[],[1,2,1]]) (patternEdgeCount [[],[],[],[],[1,2,1]]) [] := certificate_1790_checked

theorem certificate_1791_checked : certificate_1791.Valid 16 8 13 certificate_1791_q certificate_1791_edges 5 3 [] := by decide +kernel
theorem certificate_1791_valid : certificate_1791.Valid 16 8 (patternOrder [[],[],[],[],[1,2,2]]) (patternClique [[],[],[],[],[1,2,2]]) (patternEdges [[],[],[],[],[1,2,2]]) (patternAmount [[],[],[],[],[1,2,2]]) (patternEdgeCount [[],[],[],[],[1,2,2]]) [] := certificate_1791_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates057
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1792_checked : certificate_1792.Valid 16 8 14 certificate_1792_q certificate_1792_edges 6 3 [] := by decide +kernel
theorem certificate_1792_valid : certificate_1792.Valid 16 8 (patternOrder [[],[],[],[],[1,2,3]]) (patternClique [[],[],[],[],[1,2,3]]) (patternEdges [[],[],[],[],[1,2,3]]) (patternAmount [[],[],[],[],[1,2,3]]) (patternEdgeCount [[],[],[],[],[1,2,3]]) [] := certificate_1792_checked

theorem certificate_1793_checked : certificate_1793.Valid 16 8 15 certificate_1793_q certificate_1793_edges 7 3 [] := by decide +kernel
theorem certificate_1793_valid : certificate_1793.Valid 16 8 (patternOrder [[],[],[],[],[1,2,4]]) (patternClique [[],[],[],[],[1,2,4]]) (patternEdges [[],[],[],[],[1,2,4]]) (patternAmount [[],[],[],[],[1,2,4]]) (patternEdgeCount [[],[],[],[],[1,2,4]]) [] := certificate_1793_checked

theorem certificate_1794_checked : certificate_1794.Valid 16 8 16 certificate_1794_q certificate_1794_edges 8 3 [] := by decide +kernel
theorem certificate_1794_valid : certificate_1794.Valid 16 8 (patternOrder [[],[],[],[],[1,2,5]]) (patternClique [[],[],[],[],[1,2,5]]) (patternEdges [[],[],[],[],[1,2,5]]) (patternAmount [[],[],[],[],[1,2,5]]) (patternEdgeCount [[],[],[],[],[1,2,5]]) [] := certificate_1794_checked

theorem certificate_1795_checked : certificate_1795.Valid 16 8 13 certificate_1795_q certificate_1795_edges 5 3 [] := by decide +kernel
theorem certificate_1795_valid : certificate_1795.Valid 16 8 (patternOrder [[],[],[],[],[1,3,1]]) (patternClique [[],[],[],[],[1,3,1]]) (patternEdges [[],[],[],[],[1,3,1]]) (patternAmount [[],[],[],[],[1,3,1]]) (patternEdgeCount [[],[],[],[],[1,3,1]]) [] := certificate_1795_checked

theorem certificate_1796_checked : certificate_1796.Valid 16 8 14 certificate_1796_q certificate_1796_edges 6 3 [] := by decide +kernel
theorem certificate_1796_valid : certificate_1796.Valid 16 8 (patternOrder [[],[],[],[],[1,3,2]]) (patternClique [[],[],[],[],[1,3,2]]) (patternEdges [[],[],[],[],[1,3,2]]) (patternAmount [[],[],[],[],[1,3,2]]) (patternEdgeCount [[],[],[],[],[1,3,2]]) [] := certificate_1796_checked

theorem certificate_1797_checked : certificate_1797.Valid 16 8 15 certificate_1797_q certificate_1797_edges 7 3 [] := by decide +kernel
theorem certificate_1797_valid : certificate_1797.Valid 16 8 (patternOrder [[],[],[],[],[1,3,3]]) (patternClique [[],[],[],[],[1,3,3]]) (patternEdges [[],[],[],[],[1,3,3]]) (patternAmount [[],[],[],[],[1,3,3]]) (patternEdgeCount [[],[],[],[],[1,3,3]]) [] := certificate_1797_checked

theorem certificate_1798_checked : certificate_1798.Valid 16 8 16 certificate_1798_q certificate_1798_edges 8 3 [] := by decide +kernel
theorem certificate_1798_valid : certificate_1798.Valid 16 8 (patternOrder [[],[],[],[],[1,3,4]]) (patternClique [[],[],[],[],[1,3,4]]) (patternEdges [[],[],[],[],[1,3,4]]) (patternAmount [[],[],[],[],[1,3,4]]) (patternEdgeCount [[],[],[],[],[1,3,4]]) [] := certificate_1798_checked

theorem certificate_1799_checked : certificate_1799.Valid 16 8 14 certificate_1799_q certificate_1799_edges 6 3 [] := by decide +kernel
theorem certificate_1799_valid : certificate_1799.Valid 16 8 (patternOrder [[],[],[],[],[1,4,1]]) (patternClique [[],[],[],[],[1,4,1]]) (patternEdges [[],[],[],[],[1,4,1]]) (patternAmount [[],[],[],[],[1,4,1]]) (patternEdgeCount [[],[],[],[],[1,4,1]]) [] := certificate_1799_checked

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

theorem patterns_16_8_2_verified_oai : ∀ D ∈ patterns_16_8_2, PatternVerified 16 8 D := by

  simp only [patterns_16_8_2, List.forall_mem_cons]

  exact ⟨⟨certificate_1784, certificate_1784_valid⟩, ⟨⟨certificate_1785, certificate_1785_valid⟩, ⟨⟨certificate_1786, certificate_1786_valid⟩, ⟨⟨certificate_1787, certificate_1787_valid⟩, ⟨⟨certificate_1788, certificate_1788_valid⟩, ⟨⟨certificate_1789, certificate_1789_valid⟩, ⟨⟨certificate_1790, certificate_1790_valid⟩, ⟨⟨certificate_1791, certificate_1791_valid⟩, ⟨⟨certificate_1792, certificate_1792_valid⟩, ⟨⟨certificate_1793, certificate_1793_valid⟩, ⟨⟨certificate_1794, certificate_1794_valid⟩, ⟨⟨certificate_1795, certificate_1795_valid⟩, ⟨⟨certificate_1796, certificate_1796_valid⟩, ⟨⟨certificate_1797, certificate_1797_valid⟩, ⟨⟨certificate_1798, certificate_1798_valid⟩, ⟨⟨certificate_1799, certificate_1799_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_2_verified_oai := @OAI.CycleClique.patterns_16_8_2_verified_oai
