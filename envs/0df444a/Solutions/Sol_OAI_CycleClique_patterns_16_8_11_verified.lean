-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_11_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:22:52.033997+00:00
-- url     : https://prove2.me/submissions/fd5b2c62-bfbe-4a76-aca8-0683e644d1d4

import Mathlib
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates061
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1928_checked : certificate_1928.Valid 16 8 16 certificate_1928_q certificate_1928_edges 8 4 [] := by decide +kernel
theorem certificate_1928_valid : certificate_1928.Valid 16 8 (patternOrder [[],[],[1],[2,2,3]]) (patternClique [[],[],[1],[2,2,3]]) (patternEdges [[],[],[1],[2,2,3]]) (patternAmount [[],[],[1],[2,2,3]]) (patternEdgeCount [[],[],[1],[2,2,3]]) [] := certificate_1928_checked

theorem certificate_1929_checked : certificate_1929.Valid 16 8 16 certificate_1929_q certificate_1929_edges 8 4 [] := by decide +kernel
theorem certificate_1929_valid : certificate_1929.Valid 16 8 (patternOrder [[],[],[1],[2,3,2]]) (patternClique [[],[],[1],[2,3,2]]) (patternEdges [[],[],[1],[2,3,2]]) (patternAmount [[],[],[1],[2,3,2]]) (patternEdgeCount [[],[],[1],[2,3,2]]) [] := certificate_1929_checked

theorem certificate_1930_checked : certificate_1930.Valid 16 8 15 certificate_1930_q certificate_1930_edges 7 3 [] := by decide +kernel
theorem certificate_1930_valid : certificate_1930.Valid 16 8 (patternOrder [[],[],[1],[3],[3]]) (patternClique [[],[],[1],[3],[3]]) (patternEdges [[],[],[1],[3],[3]]) (patternAmount [[],[],[1],[3],[3]]) (patternEdgeCount [[],[],[1],[3],[3]]) [] := certificate_1930_checked

theorem certificate_1931_checked : certificate_1931.Valid 16 8 16 certificate_1931_q certificate_1931_edges 8 3 [] := by decide +kernel
theorem certificate_1931_valid : certificate_1931.Valid 16 8 (patternOrder [[],[],[1],[3],[4]]) (patternClique [[],[],[1],[3],[4]]) (patternEdges [[],[],[1],[3],[4]]) (patternAmount [[],[],[1],[3],[4]]) (patternEdgeCount [[],[],[1],[3],[4]]) [] := certificate_1931_checked

theorem certificate_1932_checked : certificate_1932.Valid 16 8 16 certificate_1932_q certificate_1932_edges 8 4 [] := by decide +kernel
theorem certificate_1932_valid : certificate_1932.Valid 16 8 (patternOrder [[],[],[1],[3,1,3]]) (patternClique [[],[],[1],[3,1,3]]) (patternEdges [[],[],[1],[3,1,3]]) (patternAmount [[],[],[1],[3,1,3]]) (patternEdgeCount [[],[],[1],[3,1,3]]) [] := certificate_1932_checked

theorem certificate_1933_checked : certificate_1933.Valid 16 8 12 certificate_1933_q certificate_1933_edges 4 4 [] := by decide +kernel
theorem certificate_1933_valid : certificate_1933.Valid 16 8 (patternOrder [[],[],[1,1],[1,1]]) (patternClique [[],[],[1,1],[1,1]]) (patternEdges [[],[],[1,1],[1,1]]) (patternAmount [[],[],[1,1],[1,1]]) (patternEdgeCount [[],[],[1,1],[1,1]]) [] := certificate_1933_checked

theorem certificate_1934_checked : certificate_1934.Valid 16 8 13 certificate_1934_q certificate_1934_edges 5 4 [] := by decide +kernel
theorem certificate_1934_valid : certificate_1934.Valid 16 8 (patternOrder [[],[],[1,1],[1,2]]) (patternClique [[],[],[1,1],[1,2]]) (patternEdges [[],[],[1,1],[1,2]]) (patternAmount [[],[],[1,1],[1,2]]) (patternEdgeCount [[],[],[1,1],[1,2]]) [] := certificate_1934_checked

theorem certificate_1935_checked : certificate_1935.Valid 16 8 14 certificate_1935_q certificate_1935_edges 6 4 [] := by decide +kernel
theorem certificate_1935_valid : certificate_1935.Valid 16 8 (patternOrder [[],[],[1,1],[1,3]]) (patternClique [[],[],[1,1],[1,3]]) (patternEdges [[],[],[1,1],[1,3]]) (patternAmount [[],[],[1,1],[1,3]]) (patternEdgeCount [[],[],[1,1],[1,3]]) [] := certificate_1935_checked

theorem certificate_1936_checked : certificate_1936.Valid 16 8 15 certificate_1936_q certificate_1936_edges 7 4 [] := by decide +kernel
theorem certificate_1936_valid : certificate_1936.Valid 16 8 (patternOrder [[],[],[1,1],[1,4]]) (patternClique [[],[],[1,1],[1,4]]) (patternEdges [[],[],[1,1],[1,4]]) (patternAmount [[],[],[1,1],[1,4]]) (patternEdgeCount [[],[],[1,1],[1,4]]) [] := certificate_1936_checked

theorem certificate_1937_checked : certificate_1937.Valid 16 8 16 certificate_1937_q certificate_1937_edges 8 4 [] := by decide +kernel
theorem certificate_1937_valid : certificate_1937.Valid 16 8 (patternOrder [[],[],[1,1],[1,5]]) (patternClique [[],[],[1,1],[1,5]]) (patternEdges [[],[],[1,1],[1,5]]) (patternAmount [[],[],[1,1],[1,5]]) (patternEdgeCount [[],[],[1,1],[1,5]]) [] := certificate_1937_checked

theorem certificate_1938_checked : certificate_1938.Valid 16 8 14 certificate_1938_q certificate_1938_edges 6 4 [] := by decide +kernel
theorem certificate_1938_valid : certificate_1938.Valid 16 8 (patternOrder [[],[],[1,1],[2,2]]) (patternClique [[],[],[1,1],[2,2]]) (patternEdges [[],[],[1,1],[2,2]]) (patternAmount [[],[],[1,1],[2,2]]) (patternEdgeCount [[],[],[1,1],[2,2]]) [] := certificate_1938_checked

theorem certificate_1939_checked : certificate_1939.Valid 16 8 15 certificate_1939_q certificate_1939_edges 7 4 [] := by decide +kernel
theorem certificate_1939_valid : certificate_1939.Valid 16 8 (patternOrder [[],[],[1,1],[2,3]]) (patternClique [[],[],[1,1],[2,3]]) (patternEdges [[],[],[1,1],[2,3]]) (patternAmount [[],[],[1,1],[2,3]]) (patternEdgeCount [[],[],[1,1],[2,3]]) [] := certificate_1939_checked

theorem certificate_1940_checked : certificate_1940.Valid 16 8 16 certificate_1940_q certificate_1940_edges 8 4 [] := by decide +kernel
theorem certificate_1940_valid : certificate_1940.Valid 16 8 (patternOrder [[],[],[1,1],[2,4]]) (patternClique [[],[],[1,1],[2,4]]) (patternEdges [[],[],[1,1],[2,4]]) (patternAmount [[],[],[1,1],[2,4]]) (patternEdgeCount [[],[],[1,1],[2,4]]) [] := certificate_1940_checked

theorem certificate_1941_checked : certificate_1941.Valid 16 8 16 certificate_1941_q certificate_1941_edges 8 4 [] := by decide +kernel
theorem certificate_1941_valid : certificate_1941.Valid 16 8 (patternOrder [[],[],[1,1],[3,3]]) (patternClique [[],[],[1,1],[3,3]]) (patternEdges [[],[],[1,1],[3,3]]) (patternAmount [[],[],[1,1],[3,3]]) (patternEdgeCount [[],[],[1,1],[3,3]]) [] := certificate_1941_checked

theorem certificate_1942_checked : certificate_1942.Valid 16 8 13 certificate_1942_q certificate_1942_edges 5 4 [] := by decide +kernel
theorem certificate_1942_valid : certificate_1942.Valid 16 8 (patternOrder [[],[],[1,1,1],[2]]) (patternClique [[],[],[1,1,1],[2]]) (patternEdges [[],[],[1,1,1],[2]]) (patternAmount [[],[],[1,1,1],[2]]) (patternEdgeCount [[],[],[1,1,1],[2]]) [] := certificate_1942_checked

theorem certificate_1943_checked : certificate_1943.Valid 16 8 14 certificate_1943_q certificate_1943_edges 6 4 [] := by decide +kernel
theorem certificate_1943_valid : certificate_1943.Valid 16 8 (patternOrder [[],[],[1,1,1],[3]]) (patternClique [[],[],[1,1,1],[3]]) (patternEdges [[],[],[1,1,1],[3]]) (patternAmount [[],[],[1,1,1],[3]]) (patternEdgeCount [[],[],[1,1,1],[3]]) [] := certificate_1943_checked

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

theorem patterns_16_8_11_verified_oai : ∀ D ∈ patterns_16_8_11, PatternVerified 16 8 D := by

  simp only [patterns_16_8_11, List.forall_mem_cons]

  exact ⟨⟨certificate_1928, certificate_1928_valid⟩, ⟨⟨certificate_1929, certificate_1929_valid⟩, ⟨⟨certificate_1930, certificate_1930_valid⟩, ⟨⟨certificate_1931, certificate_1931_valid⟩, ⟨⟨certificate_1932, certificate_1932_valid⟩, ⟨⟨certificate_1933, certificate_1933_valid⟩, ⟨⟨certificate_1934, certificate_1934_valid⟩, ⟨⟨certificate_1935, certificate_1935_valid⟩, ⟨⟨certificate_1936, certificate_1936_valid⟩, ⟨⟨certificate_1937, certificate_1937_valid⟩, ⟨⟨certificate_1938, certificate_1938_valid⟩, ⟨⟨certificate_1939, certificate_1939_valid⟩, ⟨⟨certificate_1940, certificate_1940_valid⟩, ⟨⟨certificate_1941, certificate_1941_valid⟩, ⟨⟨certificate_1942, certificate_1942_valid⟩, ⟨⟨certificate_1943, certificate_1943_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_11_verified_oai := @OAI.CycleClique.patterns_16_8_11_verified_oai
