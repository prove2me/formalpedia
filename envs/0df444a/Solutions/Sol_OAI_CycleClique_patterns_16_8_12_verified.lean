-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_12_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:26:31.352976+00:00
-- url     : https://prove2.me/submissions/2e30da20-91ab-44ed-9ef5-9d76b24f762a

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

theorem certificate_1944_checked : certificate_1944.Valid 16 8 15 certificate_1944_q certificate_1944_edges 7 4 [] := by decide +kernel
theorem certificate_1944_valid : certificate_1944.Valid 16 8 (patternOrder [[],[],[1,1,1],[4]]) (patternClique [[],[],[1,1,1],[4]]) (patternEdges [[],[],[1,1,1],[4]]) (patternAmount [[],[],[1,1,1],[4]]) (patternEdgeCount [[],[],[1,1,1],[4]]) [] := certificate_1944_checked

theorem certificate_1945_checked : certificate_1945.Valid 16 8 16 certificate_1945_q certificate_1945_edges 8 4 [] := by decide +kernel
theorem certificate_1945_valid : certificate_1945.Valid 16 8 (patternOrder [[],[],[1,1,1],[5]]) (patternClique [[],[],[1,1,1],[5]]) (patternEdges [[],[],[1,1,1],[5]]) (patternAmount [[],[],[1,1,1],[5]]) (patternEdgeCount [[],[],[1,1,1],[5]]) [] := certificate_1945_checked

theorem certificate_1946_checked : certificate_1946.Valid 16 8 13 certificate_1946_q certificate_1946_edges 5 5 [] := by decide +kernel
theorem certificate_1946_valid : certificate_1946.Valid 16 8 (patternOrder [[],[],[1,1,1,1,1]]) (patternClique [[],[],[1,1,1,1,1]]) (patternEdges [[],[],[1,1,1,1,1]]) (patternAmount [[],[],[1,1,1,1,1]]) (patternEdgeCount [[],[],[1,1,1,1,1]]) [] := certificate_1946_checked

theorem certificate_1947_checked : certificate_1947.Valid 16 8 14 certificate_1947_q certificate_1947_edges 6 5 [] := by decide +kernel
theorem certificate_1947_valid : certificate_1947.Valid 16 8 (patternOrder [[],[],[1,1,1,1,2]]) (patternClique [[],[],[1,1,1,1,2]]) (patternEdges [[],[],[1,1,1,1,2]]) (patternAmount [[],[],[1,1,1,1,2]]) (patternEdgeCount [[],[],[1,1,1,1,2]]) [] := certificate_1947_checked

theorem certificate_1948_checked : certificate_1948.Valid 16 8 15 certificate_1948_q certificate_1948_edges 7 5 [] := by decide +kernel
theorem certificate_1948_valid : certificate_1948.Valid 16 8 (patternOrder [[],[],[1,1,1,1,3]]) (patternClique [[],[],[1,1,1,1,3]]) (patternEdges [[],[],[1,1,1,1,3]]) (patternAmount [[],[],[1,1,1,1,3]]) (patternEdgeCount [[],[],[1,1,1,1,3]]) [] := certificate_1948_checked

theorem certificate_1949_checked : certificate_1949.Valid 16 8 16 certificate_1949_q certificate_1949_edges 8 5 [] := by decide +kernel
theorem certificate_1949_valid : certificate_1949.Valid 16 8 (patternOrder [[],[],[1,1,1,1,4]]) (patternClique [[],[],[1,1,1,1,4]]) (patternEdges [[],[],[1,1,1,1,4]]) (patternAmount [[],[],[1,1,1,1,4]]) (patternEdgeCount [[],[],[1,1,1,1,4]]) [] := certificate_1949_checked

theorem certificate_1950_checked : certificate_1950.Valid 16 8 14 certificate_1950_q certificate_1950_edges 6 5 [] := by decide +kernel
theorem certificate_1950_valid : certificate_1950.Valid 16 8 (patternOrder [[],[],[1,1,1,2,1]]) (patternClique [[],[],[1,1,1,2,1]]) (patternEdges [[],[],[1,1,1,2,1]]) (patternAmount [[],[],[1,1,1,2,1]]) (patternEdgeCount [[],[],[1,1,1,2,1]]) [] := certificate_1950_checked

theorem certificate_1951_checked : certificate_1951.Valid 16 8 15 certificate_1951_q certificate_1951_edges 7 5 [] := by decide +kernel
theorem certificate_1951_valid : certificate_1951.Valid 16 8 (patternOrder [[],[],[1,1,1,2,2]]) (patternClique [[],[],[1,1,1,2,2]]) (patternEdges [[],[],[1,1,1,2,2]]) (patternAmount [[],[],[1,1,1,2,2]]) (patternEdgeCount [[],[],[1,1,1,2,2]]) [] := certificate_1951_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates062
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1952_checked : certificate_1952.Valid 16 8 16 certificate_1952_q certificate_1952_edges 8 5 [] := by decide +kernel
theorem certificate_1952_valid : certificate_1952.Valid 16 8 (patternOrder [[],[],[1,1,1,2,3]]) (patternClique [[],[],[1,1,1,2,3]]) (patternEdges [[],[],[1,1,1,2,3]]) (patternAmount [[],[],[1,1,1,2,3]]) (patternEdgeCount [[],[],[1,1,1,2,3]]) [] := certificate_1952_checked

theorem certificate_1953_checked : certificate_1953.Valid 16 8 15 certificate_1953_q certificate_1953_edges 7 5 [] := by decide +kernel
theorem certificate_1953_valid : certificate_1953.Valid 16 8 (patternOrder [[],[],[1,1,1,3,1]]) (patternClique [[],[],[1,1,1,3,1]]) (patternEdges [[],[],[1,1,1,3,1]]) (patternAmount [[],[],[1,1,1,3,1]]) (patternEdgeCount [[],[],[1,1,1,3,1]]) [] := certificate_1953_checked

theorem certificate_1954_checked : certificate_1954.Valid 16 8 16 certificate_1954_q certificate_1954_edges 8 5 [] := by decide +kernel
theorem certificate_1954_valid : certificate_1954.Valid 16 8 (patternOrder [[],[],[1,1,1,3,2]]) (patternClique [[],[],[1,1,1,3,2]]) (patternEdges [[],[],[1,1,1,3,2]]) (patternAmount [[],[],[1,1,1,3,2]]) (patternEdgeCount [[],[],[1,1,1,3,2]]) [] := certificate_1954_checked

theorem certificate_1955_checked : certificate_1955.Valid 16 8 16 certificate_1955_q certificate_1955_edges 8 5 [] := by decide +kernel
theorem certificate_1955_valid : certificate_1955.Valid 16 8 (patternOrder [[],[],[1,1,1,4,1]]) (patternClique [[],[],[1,1,1,4,1]]) (patternEdges [[],[],[1,1,1,4,1]]) (patternAmount [[],[],[1,1,1,4,1]]) (patternEdgeCount [[],[],[1,1,1,4,1]]) [] := certificate_1955_checked

theorem certificate_1956_checked : certificate_1956.Valid 16 8 14 certificate_1956_q certificate_1956_edges 6 4 [] := by decide +kernel
theorem certificate_1956_valid : certificate_1956.Valid 16 8 (patternOrder [[],[],[1,1,2],[2]]) (patternClique [[],[],[1,1,2],[2]]) (patternEdges [[],[],[1,1,2],[2]]) (patternAmount [[],[],[1,1,2],[2]]) (patternEdgeCount [[],[],[1,1,2],[2]]) [] := certificate_1956_checked

theorem certificate_1957_checked : certificate_1957.Valid 16 8 15 certificate_1957_q certificate_1957_edges 7 4 [] := by decide +kernel
theorem certificate_1957_valid : certificate_1957.Valid 16 8 (patternOrder [[],[],[1,1,2],[3]]) (patternClique [[],[],[1,1,2],[3]]) (patternEdges [[],[],[1,1,2],[3]]) (patternAmount [[],[],[1,1,2],[3]]) (patternEdgeCount [[],[],[1,1,2],[3]]) [] := certificate_1957_checked

theorem certificate_1958_checked : certificate_1958.Valid 16 8 16 certificate_1958_q certificate_1958_edges 8 4 [] := by decide +kernel
theorem certificate_1958_valid : certificate_1958.Valid 16 8 (patternOrder [[],[],[1,1,2],[4]]) (patternClique [[],[],[1,1,2],[4]]) (patternEdges [[],[],[1,1,2],[4]]) (patternAmount [[],[],[1,1,2],[4]]) (patternEdgeCount [[],[],[1,1,2],[4]]) [] := certificate_1958_checked

theorem certificate_1959_checked : certificate_1959.Valid 16 8 14 certificate_1959_q certificate_1959_edges 6 5 [] := by decide +kernel
theorem certificate_1959_valid : certificate_1959.Valid 16 8 (patternOrder [[],[],[1,1,2,1,1]]) (patternClique [[],[],[1,1,2,1,1]]) (patternEdges [[],[],[1,1,2,1,1]]) (patternAmount [[],[],[1,1,2,1,1]]) (patternEdgeCount [[],[],[1,1,2,1,1]]) [] := certificate_1959_checked

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

theorem patterns_16_8_12_verified_oai : ∀ D ∈ patterns_16_8_12, PatternVerified 16 8 D := by

  simp only [patterns_16_8_12, List.forall_mem_cons]

  exact ⟨⟨certificate_1944, certificate_1944_valid⟩, ⟨⟨certificate_1945, certificate_1945_valid⟩, ⟨⟨certificate_1946, certificate_1946_valid⟩, ⟨⟨certificate_1947, certificate_1947_valid⟩, ⟨⟨certificate_1948, certificate_1948_valid⟩, ⟨⟨certificate_1949, certificate_1949_valid⟩, ⟨⟨certificate_1950, certificate_1950_valid⟩, ⟨⟨certificate_1951, certificate_1951_valid⟩, ⟨⟨certificate_1952, certificate_1952_valid⟩, ⟨⟨certificate_1953, certificate_1953_valid⟩, ⟨⟨certificate_1954, certificate_1954_valid⟩, ⟨⟨certificate_1955, certificate_1955_valid⟩, ⟨⟨certificate_1956, certificate_1956_valid⟩, ⟨⟨certificate_1957, certificate_1957_valid⟩, ⟨⟨certificate_1958, certificate_1958_valid⟩, ⟨⟨certificate_1959, certificate_1959_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_12_verified_oai := @OAI.CycleClique.patterns_16_8_12_verified_oai
