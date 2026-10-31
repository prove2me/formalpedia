-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_9_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:58:27.263191+00:00
-- url     : https://prove2.me/submissions/088a8ade-ebff-49ab-bd0b-c6aaa7e43a57

import Mathlib
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates060
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1896_checked : certificate_1896.Valid 16 8 16 certificate_1896_q certificate_1896_edges 8 4 [] := by decide +kernel
theorem certificate_1896_valid : certificate_1896.Valid 16 8 (patternOrder [[],[],[],[2,2,2,2]]) (patternClique [[],[],[],[2,2,2,2]]) (patternEdges [[],[],[],[2,2,2,2]]) (patternAmount [[],[],[],[2,2,2,2]]) (patternEdgeCount [[],[],[],[2,2,2,2]]) [] := certificate_1896_checked

theorem certificate_1897_checked : certificate_1897.Valid 16 8 16 certificate_1897_q certificate_1897_edges 8 3 [] := by decide +kernel
theorem certificate_1897_valid : certificate_1897.Valid 16 8 (patternOrder [[],[],[],[2,3],[3]]) (patternClique [[],[],[],[2,3],[3]]) (patternEdges [[],[],[],[2,3],[3]]) (patternAmount [[],[],[],[2,3],[3]]) (patternEdgeCount [[],[],[],[2,3],[3]]) [] := certificate_1897_checked

theorem certificate_1898_checked : certificate_1898.Valid 16 8 16 certificate_1898_q certificate_1898_edges 8 4 [] := by decide +kernel
theorem certificate_1898_valid : certificate_1898.Valid 16 8 (patternOrder [[],[],[],[3,1,1,3]]) (patternClique [[],[],[],[3,1,1,3]]) (patternEdges [[],[],[],[3,1,1,3]]) (patternAmount [[],[],[],[3,1,1,3]]) (patternEdgeCount [[],[],[],[3,1,1,3]]) [] := certificate_1898_checked

theorem certificate_1899_checked : certificate_1899.Valid 16 8 11 certificate_1899_q certificate_1899_edges 3 3 [] := by decide +kernel
theorem certificate_1899_valid : certificate_1899.Valid 16 8 (patternOrder [[],[],[1],[1],[1]]) (patternClique [[],[],[1],[1],[1]]) (patternEdges [[],[],[1],[1],[1]]) (patternAmount [[],[],[1],[1],[1]]) (patternEdgeCount [[],[],[1],[1],[1]]) [] := certificate_1899_checked

theorem certificate_1900_checked : certificate_1900.Valid 16 8 12 certificate_1900_q certificate_1900_edges 4 3 [] := by decide +kernel
theorem certificate_1900_valid : certificate_1900.Valid 16 8 (patternOrder [[],[],[1],[1],[2]]) (patternClique [[],[],[1],[1],[2]]) (patternEdges [[],[],[1],[1],[2]]) (patternAmount [[],[],[1],[1],[2]]) (patternEdgeCount [[],[],[1],[1],[2]]) [] := certificate_1900_checked

theorem certificate_1901_checked : certificate_1901.Valid 16 8 13 certificate_1901_q certificate_1901_edges 5 3 [] := by decide +kernel
theorem certificate_1901_valid : certificate_1901.Valid 16 8 (patternOrder [[],[],[1],[1],[3]]) (patternClique [[],[],[1],[1],[3]]) (patternEdges [[],[],[1],[1],[3]]) (patternAmount [[],[],[1],[1],[3]]) (patternEdgeCount [[],[],[1],[1],[3]]) [] := certificate_1901_checked

theorem certificate_1902_checked : certificate_1902.Valid 16 8 14 certificate_1902_q certificate_1902_edges 6 3 [] := by decide +kernel
theorem certificate_1902_valid : certificate_1902.Valid 16 8 (patternOrder [[],[],[1],[1],[4]]) (patternClique [[],[],[1],[1],[4]]) (patternEdges [[],[],[1],[1],[4]]) (patternAmount [[],[],[1],[1],[4]]) (patternEdgeCount [[],[],[1],[1],[4]]) [] := certificate_1902_checked

theorem certificate_1903_checked : certificate_1903.Valid 16 8 15 certificate_1903_q certificate_1903_edges 7 3 [] := by decide +kernel
theorem certificate_1903_valid : certificate_1903.Valid 16 8 (patternOrder [[],[],[1],[1],[5]]) (patternClique [[],[],[1],[1],[5]]) (patternEdges [[],[],[1],[1],[5]]) (patternAmount [[],[],[1],[1],[5]]) (patternEdgeCount [[],[],[1],[1],[5]]) [] := certificate_1903_checked

theorem certificate_1904_checked : certificate_1904.Valid 16 8 16 certificate_1904_q certificate_1904_edges 8 3 [] := by decide +kernel
theorem certificate_1904_valid : certificate_1904.Valid 16 8 (patternOrder [[],[],[1],[1],[6]]) (patternClique [[],[],[1],[1],[6]]) (patternEdges [[],[],[1],[1],[6]]) (patternAmount [[],[],[1],[1],[6]]) (patternEdgeCount [[],[],[1],[1],[6]]) [] := certificate_1904_checked

theorem certificate_1905_checked : certificate_1905.Valid 16 8 12 certificate_1905_q certificate_1905_edges 4 4 [] := by decide +kernel
theorem certificate_1905_valid : certificate_1905.Valid 16 8 (patternOrder [[],[],[1],[1,1,1]]) (patternClique [[],[],[1],[1,1,1]]) (patternEdges [[],[],[1],[1,1,1]]) (patternAmount [[],[],[1],[1,1,1]]) (patternEdgeCount [[],[],[1],[1,1,1]]) [] := certificate_1905_checked

theorem certificate_1906_checked : certificate_1906.Valid 16 8 13 certificate_1906_q certificate_1906_edges 5 4 [] := by decide +kernel
theorem certificate_1906_valid : certificate_1906.Valid 16 8 (patternOrder [[],[],[1],[1,1,2]]) (patternClique [[],[],[1],[1,1,2]]) (patternEdges [[],[],[1],[1,1,2]]) (patternAmount [[],[],[1],[1,1,2]]) (patternEdgeCount [[],[],[1],[1,1,2]]) [] := certificate_1906_checked

theorem certificate_1907_checked : certificate_1907.Valid 16 8 14 certificate_1907_q certificate_1907_edges 6 4 [] := by decide +kernel
theorem certificate_1907_valid : certificate_1907.Valid 16 8 (patternOrder [[],[],[1],[1,1,3]]) (patternClique [[],[],[1],[1,1,3]]) (patternEdges [[],[],[1],[1,1,3]]) (patternAmount [[],[],[1],[1,1,3]]) (patternEdgeCount [[],[],[1],[1,1,3]]) [] := certificate_1907_checked

theorem certificate_1908_checked : certificate_1908.Valid 16 8 15 certificate_1908_q certificate_1908_edges 7 4 [] := by decide +kernel
theorem certificate_1908_valid : certificate_1908.Valid 16 8 (patternOrder [[],[],[1],[1,1,4]]) (patternClique [[],[],[1],[1,1,4]]) (patternEdges [[],[],[1],[1,1,4]]) (patternAmount [[],[],[1],[1,1,4]]) (patternEdgeCount [[],[],[1],[1,1,4]]) [] := certificate_1908_checked

theorem certificate_1909_checked : certificate_1909.Valid 16 8 16 certificate_1909_q certificate_1909_edges 8 4 [] := by decide +kernel
theorem certificate_1909_valid : certificate_1909.Valid 16 8 (patternOrder [[],[],[1],[1,1,5]]) (patternClique [[],[],[1],[1,1,5]]) (patternEdges [[],[],[1],[1,1,5]]) (patternAmount [[],[],[1],[1,1,5]]) (patternEdgeCount [[],[],[1],[1,1,5]]) [] := certificate_1909_checked

theorem certificate_1910_checked : certificate_1910.Valid 16 8 13 certificate_1910_q certificate_1910_edges 5 4 [] := by decide +kernel
theorem certificate_1910_valid : certificate_1910.Valid 16 8 (patternOrder [[],[],[1],[1,2,1]]) (patternClique [[],[],[1],[1,2,1]]) (patternEdges [[],[],[1],[1,2,1]]) (patternAmount [[],[],[1],[1,2,1]]) (patternEdgeCount [[],[],[1],[1,2,1]]) [] := certificate_1910_checked

theorem certificate_1911_checked : certificate_1911.Valid 16 8 14 certificate_1911_q certificate_1911_edges 6 4 [] := by decide +kernel
theorem certificate_1911_valid : certificate_1911.Valid 16 8 (patternOrder [[],[],[1],[1,2,2]]) (patternClique [[],[],[1],[1,2,2]]) (patternEdges [[],[],[1],[1,2,2]]) (patternAmount [[],[],[1],[1,2,2]]) (patternEdgeCount [[],[],[1],[1,2,2]]) [] := certificate_1911_checked

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

theorem patterns_16_8_9_verified_oai : ∀ D ∈ patterns_16_8_9, PatternVerified 16 8 D := by

  simp only [patterns_16_8_9, List.forall_mem_cons]

  exact ⟨⟨certificate_1896, certificate_1896_valid⟩, ⟨⟨certificate_1897, certificate_1897_valid⟩, ⟨⟨certificate_1898, certificate_1898_valid⟩, ⟨⟨certificate_1899, certificate_1899_valid⟩, ⟨⟨certificate_1900, certificate_1900_valid⟩, ⟨⟨certificate_1901, certificate_1901_valid⟩, ⟨⟨certificate_1902, certificate_1902_valid⟩, ⟨⟨certificate_1903, certificate_1903_valid⟩, ⟨⟨certificate_1904, certificate_1904_valid⟩, ⟨⟨certificate_1905, certificate_1905_valid⟩, ⟨⟨certificate_1906, certificate_1906_valid⟩, ⟨⟨certificate_1907, certificate_1907_valid⟩, ⟨⟨certificate_1908, certificate_1908_valid⟩, ⟨⟨certificate_1909, certificate_1909_valid⟩, ⟨⟨certificate_1910, certificate_1910_valid⟩, ⟨⟨certificate_1911, certificate_1911_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_9_verified_oai := @OAI.CycleClique.patterns_16_8_9_verified_oai
