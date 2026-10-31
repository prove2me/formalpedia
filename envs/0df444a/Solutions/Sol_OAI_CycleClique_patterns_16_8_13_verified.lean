-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_13_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:35:22.648759+00:00
-- url     : https://prove2.me/submissions/c0c5d53a-0e9c-4c1b-9551-7931b5f9df15

import Mathlib
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates062
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1960_checked : certificate_1960.Valid 16 8 15 certificate_1960_q certificate_1960_edges 7 5 [] := by decide +kernel
theorem certificate_1960_valid : certificate_1960.Valid 16 8 (patternOrder [[],[],[1,1,2,1,2]]) (patternClique [[],[],[1,1,2,1,2]]) (patternEdges [[],[],[1,1,2,1,2]]) (patternAmount [[],[],[1,1,2,1,2]]) (patternEdgeCount [[],[],[1,1,2,1,2]]) [] := certificate_1960_checked

theorem certificate_1961_checked : certificate_1961.Valid 16 8 16 certificate_1961_q certificate_1961_edges 8 5 [] := by decide +kernel
theorem certificate_1961_valid : certificate_1961.Valid 16 8 (patternOrder [[],[],[1,1,2,1,3]]) (patternClique [[],[],[1,1,2,1,3]]) (patternEdges [[],[],[1,1,2,1,3]]) (patternAmount [[],[],[1,1,2,1,3]]) (patternEdgeCount [[],[],[1,1,2,1,3]]) [] := certificate_1961_checked

theorem certificate_1962_checked : certificate_1962.Valid 16 8 15 certificate_1962_q certificate_1962_edges 7 5 [] := by decide +kernel
theorem certificate_1962_valid : certificate_1962.Valid 16 8 (patternOrder [[],[],[1,1,2,2,1]]) (patternClique [[],[],[1,1,2,2,1]]) (patternEdges [[],[],[1,1,2,2,1]]) (patternAmount [[],[],[1,1,2,2,1]]) (patternEdgeCount [[],[],[1,1,2,2,1]]) [] := certificate_1962_checked

theorem certificate_1963_checked : certificate_1963.Valid 16 8 16 certificate_1963_q certificate_1963_edges 8 5 [] := by decide +kernel
theorem certificate_1963_valid : certificate_1963.Valid 16 8 (patternOrder [[],[],[1,1,2,2,2]]) (patternClique [[],[],[1,1,2,2,2]]) (patternEdges [[],[],[1,1,2,2,2]]) (patternAmount [[],[],[1,1,2,2,2]]) (patternEdgeCount [[],[],[1,1,2,2,2]]) [] := certificate_1963_checked

theorem certificate_1964_checked : certificate_1964.Valid 16 8 16 certificate_1964_q certificate_1964_edges 8 5 [] := by decide +kernel
theorem certificate_1964_valid : certificate_1964.Valid 16 8 (patternOrder [[],[],[1,1,2,3,1]]) (patternClique [[],[],[1,1,2,3,1]]) (patternEdges [[],[],[1,1,2,3,1]]) (patternAmount [[],[],[1,1,2,3,1]]) (patternEdgeCount [[],[],[1,1,2,3,1]]) [] := certificate_1964_checked

theorem certificate_1965_checked : certificate_1965.Valid 16 8 15 certificate_1965_q certificate_1965_edges 7 4 [] := by decide +kernel
theorem certificate_1965_valid : certificate_1965.Valid 16 8 (patternOrder [[],[],[1,1,3],[2]]) (patternClique [[],[],[1,1,3],[2]]) (patternEdges [[],[],[1,1,3],[2]]) (patternAmount [[],[],[1,1,3],[2]]) (patternEdgeCount [[],[],[1,1,3],[2]]) [] := certificate_1965_checked

theorem certificate_1966_checked : certificate_1966.Valid 16 8 16 certificate_1966_q certificate_1966_edges 8 4 [] := by decide +kernel
theorem certificate_1966_valid : certificate_1966.Valid 16 8 (patternOrder [[],[],[1,1,3],[3]]) (patternClique [[],[],[1,1,3],[3]]) (patternEdges [[],[],[1,1,3],[3]]) (patternAmount [[],[],[1,1,3],[3]]) (patternEdgeCount [[],[],[1,1,3],[3]]) [] := certificate_1966_checked

theorem certificate_1967_checked : certificate_1967.Valid 16 8 15 certificate_1967_q certificate_1967_edges 7 5 [] := by decide +kernel
theorem certificate_1967_valid : certificate_1967.Valid 16 8 (patternOrder [[],[],[1,1,3,1,1]]) (patternClique [[],[],[1,1,3,1,1]]) (patternEdges [[],[],[1,1,3,1,1]]) (patternAmount [[],[],[1,1,3,1,1]]) (patternEdgeCount [[],[],[1,1,3,1,1]]) [] := certificate_1967_checked

theorem certificate_1968_checked : certificate_1968.Valid 16 8 16 certificate_1968_q certificate_1968_edges 8 5 [] := by decide +kernel
theorem certificate_1968_valid : certificate_1968.Valid 16 8 (patternOrder [[],[],[1,1,3,1,2]]) (patternClique [[],[],[1,1,3,1,2]]) (patternEdges [[],[],[1,1,3,1,2]]) (patternAmount [[],[],[1,1,3,1,2]]) (patternEdgeCount [[],[],[1,1,3,1,2]]) [] := certificate_1968_checked

theorem certificate_1969_checked : certificate_1969.Valid 16 8 16 certificate_1969_q certificate_1969_edges 8 5 [] := by decide +kernel
theorem certificate_1969_valid : certificate_1969.Valid 16 8 (patternOrder [[],[],[1,1,3,2,1]]) (patternClique [[],[],[1,1,3,2,1]]) (patternEdges [[],[],[1,1,3,2,1]]) (patternAmount [[],[],[1,1,3,2,1]]) (patternEdgeCount [[],[],[1,1,3,2,1]]) [] := certificate_1969_checked

theorem certificate_1970_checked : certificate_1970.Valid 16 8 16 certificate_1970_q certificate_1970_edges 8 4 [] := by decide +kernel
theorem certificate_1970_valid : certificate_1970.Valid 16 8 (patternOrder [[],[],[1,1,4],[2]]) (patternClique [[],[],[1,1,4],[2]]) (patternEdges [[],[],[1,1,4],[2]]) (patternAmount [[],[],[1,1,4],[2]]) (patternEdgeCount [[],[],[1,1,4],[2]]) [] := certificate_1970_checked

theorem certificate_1971_checked : certificate_1971.Valid 16 8 16 certificate_1971_q certificate_1971_edges 8 5 [] := by decide +kernel
theorem certificate_1971_valid : certificate_1971.Valid 16 8 (patternOrder [[],[],[1,1,4,1,1]]) (patternClique [[],[],[1,1,4,1,1]]) (patternEdges [[],[],[1,1,4,1,1]]) (patternAmount [[],[],[1,1,4,1,1]]) (patternEdgeCount [[],[],[1,1,4,1,1]]) [] := certificate_1971_checked

theorem certificate_1972_checked : certificate_1972.Valid 16 8 14 certificate_1972_q certificate_1972_edges 6 4 [] := by decide +kernel
theorem certificate_1972_valid : certificate_1972.Valid 16 8 (patternOrder [[],[],[1,2],[1,2]]) (patternClique [[],[],[1,2],[1,2]]) (patternEdges [[],[],[1,2],[1,2]]) (patternAmount [[],[],[1,2],[1,2]]) (patternEdgeCount [[],[],[1,2],[1,2]]) [] := certificate_1972_checked

theorem certificate_1973_checked : certificate_1973.Valid 16 8 15 certificate_1973_q certificate_1973_edges 7 4 [] := by decide +kernel
theorem certificate_1973_valid : certificate_1973.Valid 16 8 (patternOrder [[],[],[1,2],[1,3]]) (patternClique [[],[],[1,2],[1,3]]) (patternEdges [[],[],[1,2],[1,3]]) (patternAmount [[],[],[1,2],[1,3]]) (patternEdgeCount [[],[],[1,2],[1,3]]) [] := certificate_1973_checked

theorem certificate_1974_checked : certificate_1974.Valid 16 8 16 certificate_1974_q certificate_1974_edges 8 4 [] := by decide +kernel
theorem certificate_1974_valid : certificate_1974.Valid 16 8 (patternOrder [[],[],[1,2],[1,4]]) (patternClique [[],[],[1,2],[1,4]]) (patternEdges [[],[],[1,2],[1,4]]) (patternAmount [[],[],[1,2],[1,4]]) (patternEdgeCount [[],[],[1,2],[1,4]]) [] := certificate_1974_checked

theorem certificate_1975_checked : certificate_1975.Valid 16 8 15 certificate_1975_q certificate_1975_edges 7 4 [] := by decide +kernel
theorem certificate_1975_valid : certificate_1975.Valid 16 8 (patternOrder [[],[],[1,2],[2,2]]) (patternClique [[],[],[1,2],[2,2]]) (patternEdges [[],[],[1,2],[2,2]]) (patternAmount [[],[],[1,2],[2,2]]) (patternEdgeCount [[],[],[1,2],[2,2]]) [] := certificate_1975_checked

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

theorem patterns_16_8_13_verified_oai : ∀ D ∈ patterns_16_8_13, PatternVerified 16 8 D := by

  simp only [patterns_16_8_13, List.forall_mem_cons]

  exact ⟨⟨certificate_1960, certificate_1960_valid⟩, ⟨⟨certificate_1961, certificate_1961_valid⟩, ⟨⟨certificate_1962, certificate_1962_valid⟩, ⟨⟨certificate_1963, certificate_1963_valid⟩, ⟨⟨certificate_1964, certificate_1964_valid⟩, ⟨⟨certificate_1965, certificate_1965_valid⟩, ⟨⟨certificate_1966, certificate_1966_valid⟩, ⟨⟨certificate_1967, certificate_1967_valid⟩, ⟨⟨certificate_1968, certificate_1968_valid⟩, ⟨⟨certificate_1969, certificate_1969_valid⟩, ⟨⟨certificate_1970, certificate_1970_valid⟩, ⟨⟨certificate_1971, certificate_1971_valid⟩, ⟨⟨certificate_1972, certificate_1972_valid⟩, ⟨⟨certificate_1973, certificate_1973_valid⟩, ⟨⟨certificate_1974, certificate_1974_valid⟩, ⟨⟨certificate_1975, certificate_1975_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_13_verified_oai := @OAI.CycleClique.patterns_16_8_13_verified_oai
