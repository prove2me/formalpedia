-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_10_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:28:22.162988+00:00
-- url     : https://prove2.me/submissions/ced3867e-f544-4522-8c75-907372952428

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

theorem certificate_1912_checked : certificate_1912.Valid 16 8 15 certificate_1912_q certificate_1912_edges 7 4 [] := by decide +kernel
theorem certificate_1912_valid : certificate_1912.Valid 16 8 (patternOrder [[],[],[1],[1,2,3]]) (patternClique [[],[],[1],[1,2,3]]) (patternEdges [[],[],[1],[1,2,3]]) (patternAmount [[],[],[1],[1,2,3]]) (patternEdgeCount [[],[],[1],[1,2,3]]) [] := certificate_1912_checked

theorem certificate_1913_checked : certificate_1913.Valid 16 8 16 certificate_1913_q certificate_1913_edges 8 4 [] := by decide +kernel
theorem certificate_1913_valid : certificate_1913.Valid 16 8 (patternOrder [[],[],[1],[1,2,4]]) (patternClique [[],[],[1],[1,2,4]]) (patternEdges [[],[],[1],[1,2,4]]) (patternAmount [[],[],[1],[1,2,4]]) (patternEdgeCount [[],[],[1],[1,2,4]]) [] := certificate_1913_checked

theorem certificate_1914_checked : certificate_1914.Valid 16 8 14 certificate_1914_q certificate_1914_edges 6 4 [] := by decide +kernel
theorem certificate_1914_valid : certificate_1914.Valid 16 8 (patternOrder [[],[],[1],[1,3,1]]) (patternClique [[],[],[1],[1,3,1]]) (patternEdges [[],[],[1],[1,3,1]]) (patternAmount [[],[],[1],[1,3,1]]) (patternEdgeCount [[],[],[1],[1,3,1]]) [] := certificate_1914_checked

theorem certificate_1915_checked : certificate_1915.Valid 16 8 15 certificate_1915_q certificate_1915_edges 7 4 [] := by decide +kernel
theorem certificate_1915_valid : certificate_1915.Valid 16 8 (patternOrder [[],[],[1],[1,3,2]]) (patternClique [[],[],[1],[1,3,2]]) (patternEdges [[],[],[1],[1,3,2]]) (patternAmount [[],[],[1],[1,3,2]]) (patternEdgeCount [[],[],[1],[1,3,2]]) [] := certificate_1915_checked

theorem certificate_1916_checked : certificate_1916.Valid 16 8 16 certificate_1916_q certificate_1916_edges 8 4 [] := by decide +kernel
theorem certificate_1916_valid : certificate_1916.Valid 16 8 (patternOrder [[],[],[1],[1,3,3]]) (patternClique [[],[],[1],[1,3,3]]) (patternEdges [[],[],[1],[1,3,3]]) (patternAmount [[],[],[1],[1,3,3]]) (patternEdgeCount [[],[],[1],[1,3,3]]) [] := certificate_1916_checked

theorem certificate_1917_checked : certificate_1917.Valid 16 8 15 certificate_1917_q certificate_1917_edges 7 4 [] := by decide +kernel
theorem certificate_1917_valid : certificate_1917.Valid 16 8 (patternOrder [[],[],[1],[1,4,1]]) (patternClique [[],[],[1],[1,4,1]]) (patternEdges [[],[],[1],[1,4,1]]) (patternAmount [[],[],[1],[1,4,1]]) (patternEdgeCount [[],[],[1],[1,4,1]]) [] := certificate_1917_checked

theorem certificate_1918_checked : certificate_1918.Valid 16 8 16 certificate_1918_q certificate_1918_edges 8 4 [] := by decide +kernel
theorem certificate_1918_valid : certificate_1918.Valid 16 8 (patternOrder [[],[],[1],[1,4,2]]) (patternClique [[],[],[1],[1,4,2]]) (patternEdges [[],[],[1],[1,4,2]]) (patternAmount [[],[],[1],[1,4,2]]) (patternEdgeCount [[],[],[1],[1,4,2]]) [] := certificate_1918_checked

theorem certificate_1919_checked : certificate_1919.Valid 16 8 16 certificate_1919_q certificate_1919_edges 8 4 [] := by decide +kernel
theorem certificate_1919_valid : certificate_1919.Valid 16 8 (patternOrder [[],[],[1],[1,5,1]]) (patternClique [[],[],[1],[1,5,1]]) (patternEdges [[],[],[1],[1,5,1]]) (patternAmount [[],[],[1],[1,5,1]]) (patternEdgeCount [[],[],[1],[1,5,1]]) [] := certificate_1919_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates061
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1920_checked : certificate_1920.Valid 16 8 13 certificate_1920_q certificate_1920_edges 5 3 [] := by decide +kernel
theorem certificate_1920_valid : certificate_1920.Valid 16 8 (patternOrder [[],[],[1],[2],[2]]) (patternClique [[],[],[1],[2],[2]]) (patternEdges [[],[],[1],[2],[2]]) (patternAmount [[],[],[1],[2],[2]]) (patternEdgeCount [[],[],[1],[2],[2]]) [] := certificate_1920_checked

theorem certificate_1921_checked : certificate_1921.Valid 16 8 14 certificate_1921_q certificate_1921_edges 6 3 [] := by decide +kernel
theorem certificate_1921_valid : certificate_1921.Valid 16 8 (patternOrder [[],[],[1],[2],[3]]) (patternClique [[],[],[1],[2],[3]]) (patternEdges [[],[],[1],[2],[3]]) (patternAmount [[],[],[1],[2],[3]]) (patternEdgeCount [[],[],[1],[2],[3]]) [] := certificate_1921_checked

theorem certificate_1922_checked : certificate_1922.Valid 16 8 15 certificate_1922_q certificate_1922_edges 7 3 [] := by decide +kernel
theorem certificate_1922_valid : certificate_1922.Valid 16 8 (patternOrder [[],[],[1],[2],[4]]) (patternClique [[],[],[1],[2],[4]]) (patternEdges [[],[],[1],[2],[4]]) (patternAmount [[],[],[1],[2],[4]]) (patternEdgeCount [[],[],[1],[2],[4]]) [] := certificate_1922_checked

theorem certificate_1923_checked : certificate_1923.Valid 16 8 16 certificate_1923_q certificate_1923_edges 8 3 [] := by decide +kernel
theorem certificate_1923_valid : certificate_1923.Valid 16 8 (patternOrder [[],[],[1],[2],[5]]) (patternClique [[],[],[1],[2],[5]]) (patternEdges [[],[],[1],[2],[5]]) (patternAmount [[],[],[1],[2],[5]]) (patternEdgeCount [[],[],[1],[2],[5]]) [] := certificate_1923_checked

theorem certificate_1924_checked : certificate_1924.Valid 16 8 14 certificate_1924_q certificate_1924_edges 6 4 [] := by decide +kernel
theorem certificate_1924_valid : certificate_1924.Valid 16 8 (patternOrder [[],[],[1],[2,1,2]]) (patternClique [[],[],[1],[2,1,2]]) (patternEdges [[],[],[1],[2,1,2]]) (patternAmount [[],[],[1],[2,1,2]]) (patternEdgeCount [[],[],[1],[2,1,2]]) [] := certificate_1924_checked

theorem certificate_1925_checked : certificate_1925.Valid 16 8 15 certificate_1925_q certificate_1925_edges 7 4 [] := by decide +kernel
theorem certificate_1925_valid : certificate_1925.Valid 16 8 (patternOrder [[],[],[1],[2,1,3]]) (patternClique [[],[],[1],[2,1,3]]) (patternEdges [[],[],[1],[2,1,3]]) (patternAmount [[],[],[1],[2,1,3]]) (patternEdgeCount [[],[],[1],[2,1,3]]) [] := certificate_1925_checked

theorem certificate_1926_checked : certificate_1926.Valid 16 8 16 certificate_1926_q certificate_1926_edges 8 4 [] := by decide +kernel
theorem certificate_1926_valid : certificate_1926.Valid 16 8 (patternOrder [[],[],[1],[2,1,4]]) (patternClique [[],[],[1],[2,1,4]]) (patternEdges [[],[],[1],[2,1,4]]) (patternAmount [[],[],[1],[2,1,4]]) (patternEdgeCount [[],[],[1],[2,1,4]]) [] := certificate_1926_checked

theorem certificate_1927_checked : certificate_1927.Valid 16 8 15 certificate_1927_q certificate_1927_edges 7 4 [] := by decide +kernel
theorem certificate_1927_valid : certificate_1927.Valid 16 8 (patternOrder [[],[],[1],[2,2,2]]) (patternClique [[],[],[1],[2,2,2]]) (patternEdges [[],[],[1],[2,2,2]]) (patternAmount [[],[],[1],[2,2,2]]) (patternEdgeCount [[],[],[1],[2,2,2]]) [] := certificate_1927_checked

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

theorem patterns_16_8_10_verified_oai : ∀ D ∈ patterns_16_8_10, PatternVerified 16 8 D := by

  simp only [patterns_16_8_10, List.forall_mem_cons]

  exact ⟨⟨certificate_1912, certificate_1912_valid⟩, ⟨⟨certificate_1913, certificate_1913_valid⟩, ⟨⟨certificate_1914, certificate_1914_valid⟩, ⟨⟨certificate_1915, certificate_1915_valid⟩, ⟨⟨certificate_1916, certificate_1916_valid⟩, ⟨⟨certificate_1917, certificate_1917_valid⟩, ⟨⟨certificate_1918, certificate_1918_valid⟩, ⟨⟨certificate_1919, certificate_1919_valid⟩, ⟨⟨certificate_1920, certificate_1920_valid⟩, ⟨⟨certificate_1921, certificate_1921_valid⟩, ⟨⟨certificate_1922, certificate_1922_valid⟩, ⟨⟨certificate_1923, certificate_1923_valid⟩, ⟨⟨certificate_1924, certificate_1924_valid⟩, ⟨⟨certificate_1925, certificate_1925_valid⟩, ⟨⟨certificate_1926, certificate_1926_valid⟩, ⟨⟨certificate_1927, certificate_1927_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_10_verified_oai := @OAI.CycleClique.patterns_16_8_10_verified_oai
