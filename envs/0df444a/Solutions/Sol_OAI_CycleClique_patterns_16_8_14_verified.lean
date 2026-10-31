-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_14_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:30:56.667984+00:00
-- url     : https://prove2.me/submissions/76a7ae5c-7c44-4abd-a567-8de4584a3d47

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

theorem certificate_1976_checked : certificate_1976.Valid 16 8 16 certificate_1976_q certificate_1976_edges 8 4 [] := by decide +kernel
theorem certificate_1976_valid : certificate_1976.Valid 16 8 (patternOrder [[],[],[1,2],[2,3]]) (patternClique [[],[],[1,2],[2,3]]) (patternEdges [[],[],[1,2],[2,3]]) (patternAmount [[],[],[1,2],[2,3]]) (patternEdgeCount [[],[],[1,2],[2,3]]) [] := certificate_1976_checked

theorem certificate_1977_checked : certificate_1977.Valid 16 8 14 certificate_1977_q certificate_1977_edges 6 4 [] := by decide +kernel
theorem certificate_1977_valid : certificate_1977.Valid 16 8 (patternOrder [[],[],[1,2,1],[2]]) (patternClique [[],[],[1,2,1],[2]]) (patternEdges [[],[],[1,2,1],[2]]) (patternAmount [[],[],[1,2,1],[2]]) (patternEdgeCount [[],[],[1,2,1],[2]]) [] := certificate_1977_checked

theorem certificate_1978_checked : certificate_1978.Valid 16 8 15 certificate_1978_q certificate_1978_edges 7 4 [] := by decide +kernel
theorem certificate_1978_valid : certificate_1978.Valid 16 8 (patternOrder [[],[],[1,2,1],[3]]) (patternClique [[],[],[1,2,1],[3]]) (patternEdges [[],[],[1,2,1],[3]]) (patternAmount [[],[],[1,2,1],[3]]) (patternEdgeCount [[],[],[1,2,1],[3]]) [] := certificate_1978_checked

theorem certificate_1979_checked : certificate_1979.Valid 16 8 16 certificate_1979_q certificate_1979_edges 8 4 [] := by decide +kernel
theorem certificate_1979_valid : certificate_1979.Valid 16 8 (patternOrder [[],[],[1,2,1],[4]]) (patternClique [[],[],[1,2,1],[4]]) (patternEdges [[],[],[1,2,1],[4]]) (patternAmount [[],[],[1,2,1],[4]]) (patternEdgeCount [[],[],[1,2,1],[4]]) [] := certificate_1979_checked

theorem certificate_1980_checked : certificate_1980.Valid 16 8 15 certificate_1980_q certificate_1980_edges 7 5 [] := by decide +kernel
theorem certificate_1980_valid : certificate_1980.Valid 16 8 (patternOrder [[],[],[1,2,1,1,2]]) (patternClique [[],[],[1,2,1,1,2]]) (patternEdges [[],[],[1,2,1,1,2]]) (patternAmount [[],[],[1,2,1,1,2]]) (patternEdgeCount [[],[],[1,2,1,1,2]]) [] := certificate_1980_checked

theorem certificate_1981_checked : certificate_1981.Valid 16 8 16 certificate_1981_q certificate_1981_edges 8 5 [] := by decide +kernel
theorem certificate_1981_valid : certificate_1981.Valid 16 8 (patternOrder [[],[],[1,2,1,1,3]]) (patternClique [[],[],[1,2,1,1,3]]) (patternEdges [[],[],[1,2,1,1,3]]) (patternAmount [[],[],[1,2,1,1,3]]) (patternEdgeCount [[],[],[1,2,1,1,3]]) [] := certificate_1981_checked

theorem certificate_1982_checked : certificate_1982.Valid 16 8 15 certificate_1982_q certificate_1982_edges 7 5 [] := by decide +kernel
theorem certificate_1982_valid : certificate_1982.Valid 16 8 (patternOrder [[],[],[1,2,1,2,1]]) (patternClique [[],[],[1,2,1,2,1]]) (patternEdges [[],[],[1,2,1,2,1]]) (patternAmount [[],[],[1,2,1,2,1]]) (patternEdgeCount [[],[],[1,2,1,2,1]]) [] := certificate_1982_checked

theorem certificate_1983_checked : certificate_1983.Valid 16 8 16 certificate_1983_q certificate_1983_edges 8 5 [] := by decide +kernel
theorem certificate_1983_valid : certificate_1983.Valid 16 8 (patternOrder [[],[],[1,2,1,2,2]]) (patternClique [[],[],[1,2,1,2,2]]) (patternEdges [[],[],[1,2,1,2,2]]) (patternAmount [[],[],[1,2,1,2,2]]) (patternEdgeCount [[],[],[1,2,1,2,2]]) [] := certificate_1983_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates063
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1984_checked : certificate_1984.Valid 16 8 16 certificate_1984_q certificate_1984_edges 8 5 [] := by decide +kernel
theorem certificate_1984_valid : certificate_1984.Valid 16 8 (patternOrder [[],[],[1,2,1,3,1]]) (patternClique [[],[],[1,2,1,3,1]]) (patternEdges [[],[],[1,2,1,3,1]]) (patternAmount [[],[],[1,2,1,3,1]]) (patternEdgeCount [[],[],[1,2,1,3,1]]) [] := certificate_1984_checked

theorem certificate_1985_checked : certificate_1985.Valid 16 8 15 certificate_1985_q certificate_1985_edges 7 4 [] := by decide +kernel
theorem certificate_1985_valid : certificate_1985.Valid 16 8 (patternOrder [[],[],[1,2,2],[2]]) (patternClique [[],[],[1,2,2],[2]]) (patternEdges [[],[],[1,2,2],[2]]) (patternAmount [[],[],[1,2,2],[2]]) (patternEdgeCount [[],[],[1,2,2],[2]]) [] := certificate_1985_checked

theorem certificate_1986_checked : certificate_1986.Valid 16 8 16 certificate_1986_q certificate_1986_edges 8 4 [] := by decide +kernel
theorem certificate_1986_valid : certificate_1986.Valid 16 8 (patternOrder [[],[],[1,2,2],[3]]) (patternClique [[],[],[1,2,2],[3]]) (patternEdges [[],[],[1,2,2],[3]]) (patternAmount [[],[],[1,2,2],[3]]) (patternEdgeCount [[],[],[1,2,2],[3]]) [] := certificate_1986_checked

theorem certificate_1987_checked : certificate_1987.Valid 16 8 16 certificate_1987_q certificate_1987_edges 8 5 [] := by decide +kernel
theorem certificate_1987_valid : certificate_1987.Valid 16 8 (patternOrder [[],[],[1,2,2,1,2]]) (patternClique [[],[],[1,2,2,1,2]]) (patternEdges [[],[],[1,2,2,1,2]]) (patternAmount [[],[],[1,2,2,1,2]]) (patternEdgeCount [[],[],[1,2,2,1,2]]) [] := certificate_1987_checked

theorem certificate_1988_checked : certificate_1988.Valid 16 8 16 certificate_1988_q certificate_1988_edges 8 5 [] := by decide +kernel
theorem certificate_1988_valid : certificate_1988.Valid 16 8 (patternOrder [[],[],[1,2,2,2,1]]) (patternClique [[],[],[1,2,2,2,1]]) (patternEdges [[],[],[1,2,2,2,1]]) (patternAmount [[],[],[1,2,2,2,1]]) (patternEdgeCount [[],[],[1,2,2,2,1]]) [] := certificate_1988_checked

theorem certificate_1989_checked : certificate_1989.Valid 16 8 16 certificate_1989_q certificate_1989_edges 8 4 [] := by decide +kernel
theorem certificate_1989_valid : certificate_1989.Valid 16 8 (patternOrder [[],[],[1,2,3],[2]]) (patternClique [[],[],[1,2,3],[2]]) (patternEdges [[],[],[1,2,3],[2]]) (patternAmount [[],[],[1,2,3],[2]]) (patternEdgeCount [[],[],[1,2,3],[2]]) [] := certificate_1989_checked

theorem certificate_1990_checked : certificate_1990.Valid 16 8 16 certificate_1990_q certificate_1990_edges 8 4 [] := by decide +kernel
theorem certificate_1990_valid : certificate_1990.Valid 16 8 (patternOrder [[],[],[1,3],[1,3]]) (patternClique [[],[],[1,3],[1,3]]) (patternEdges [[],[],[1,3],[1,3]]) (patternAmount [[],[],[1,3],[1,3]]) (patternEdgeCount [[],[],[1,3],[1,3]]) [] := certificate_1990_checked

theorem certificate_1991_checked : certificate_1991.Valid 16 8 16 certificate_1991_q certificate_1991_edges 8 4 [] := by decide +kernel
theorem certificate_1991_valid : certificate_1991.Valid 16 8 (patternOrder [[],[],[1,3],[2,2]]) (patternClique [[],[],[1,3],[2,2]]) (patternEdges [[],[],[1,3],[2,2]]) (patternAmount [[],[],[1,3],[2,2]]) (patternEdgeCount [[],[],[1,3],[2,2]]) [] := certificate_1991_checked

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

theorem patterns_16_8_14_verified_oai : ∀ D ∈ patterns_16_8_14, PatternVerified 16 8 D := by

  simp only [patterns_16_8_14, List.forall_mem_cons]

  exact ⟨⟨certificate_1976, certificate_1976_valid⟩, ⟨⟨certificate_1977, certificate_1977_valid⟩, ⟨⟨certificate_1978, certificate_1978_valid⟩, ⟨⟨certificate_1979, certificate_1979_valid⟩, ⟨⟨certificate_1980, certificate_1980_valid⟩, ⟨⟨certificate_1981, certificate_1981_valid⟩, ⟨⟨certificate_1982, certificate_1982_valid⟩, ⟨⟨certificate_1983, certificate_1983_valid⟩, ⟨⟨certificate_1984, certificate_1984_valid⟩, ⟨⟨certificate_1985, certificate_1985_valid⟩, ⟨⟨certificate_1986, certificate_1986_valid⟩, ⟨⟨certificate_1987, certificate_1987_valid⟩, ⟨⟨certificate_1988, certificate_1988_valid⟩, ⟨⟨certificate_1989, certificate_1989_valid⟩, ⟨⟨certificate_1990, certificate_1990_valid⟩, ⟨⟨certificate_1991, certificate_1991_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_14_verified_oai := @OAI.CycleClique.patterns_16_8_14_verified_oai
