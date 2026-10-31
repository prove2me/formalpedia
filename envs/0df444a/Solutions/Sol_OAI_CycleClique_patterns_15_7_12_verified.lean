-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_12_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:18:02.675655+00:00
-- url     : https://prove2.me/submissions/c3fe9e37-1359-435f-bc86-30d47f3e50dd

import Mathlib
import Definitions.Def_OAIQ107D133
import Definitions.Def_OAIQ107D134

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates042
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1343_checked : certificate_1343.Valid 15 7 14 certificate_1343_q certificate_1343_edges 7 4 [] := by decide +kernel
theorem certificate_1343_valid : certificate_1343.Valid 15 7 (patternOrder [[],[1,1,1],[4]]) (patternClique [[],[1,1,1],[4]]) (patternEdges [[],[1,1,1],[4]]) (patternAmount [[],[1,1,1],[4]]) (patternEdgeCount [[],[1,1,1],[4]]) [] := certificate_1343_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates043
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1344_checked : certificate_1344.Valid 15 7 15 certificate_1344_q certificate_1344_edges 8 4 [] := by decide +kernel
theorem certificate_1344_valid : certificate_1344.Valid 15 7 (patternOrder [[],[1,1,1],[5]]) (patternClique [[],[1,1,1],[5]]) (patternEdges [[],[1,1,1],[5]]) (patternAmount [[],[1,1,1],[5]]) (patternEdgeCount [[],[1,1,1],[5]]) [] := certificate_1344_checked

theorem certificate_1345_checked : certificate_1345.Valid 15 7 12 certificate_1345_q certificate_1345_edges 5 5 [] := by decide +kernel
theorem certificate_1345_valid : certificate_1345.Valid 15 7 (patternOrder [[],[1,1,1,1,1]]) (patternClique [[],[1,1,1,1,1]]) (patternEdges [[],[1,1,1,1,1]]) (patternAmount [[],[1,1,1,1,1]]) (patternEdgeCount [[],[1,1,1,1,1]]) [] := certificate_1345_checked

theorem certificate_1346_checked : certificate_1346.Valid 15 7 13 certificate_1346_q certificate_1346_edges 6 5 [] := by decide +kernel
theorem certificate_1346_valid : certificate_1346.Valid 15 7 (patternOrder [[],[1,1,1,1,2]]) (patternClique [[],[1,1,1,1,2]]) (patternEdges [[],[1,1,1,1,2]]) (patternAmount [[],[1,1,1,1,2]]) (patternEdgeCount [[],[1,1,1,1,2]]) [] := certificate_1346_checked

theorem certificate_1347_checked : certificate_1347.Valid 15 7 14 certificate_1347_q certificate_1347_edges 7 5 [] := by decide +kernel
theorem certificate_1347_valid : certificate_1347.Valid 15 7 (patternOrder [[],[1,1,1,1,3]]) (patternClique [[],[1,1,1,1,3]]) (patternEdges [[],[1,1,1,1,3]]) (patternAmount [[],[1,1,1,1,3]]) (patternEdgeCount [[],[1,1,1,1,3]]) [] := certificate_1347_checked

theorem certificate_1348_checked : certificate_1348.Valid 15 7 15 certificate_1348_q certificate_1348_edges 8 5 [] := by decide +kernel
theorem certificate_1348_valid : certificate_1348.Valid 15 7 (patternOrder [[],[1,1,1,1,4]]) (patternClique [[],[1,1,1,1,4]]) (patternEdges [[],[1,1,1,1,4]]) (patternAmount [[],[1,1,1,1,4]]) (patternEdgeCount [[],[1,1,1,1,4]]) [] := certificate_1348_checked

theorem certificate_1349_checked : certificate_1349.Valid 15 7 13 certificate_1349_q certificate_1349_edges 6 5 [] := by decide +kernel
theorem certificate_1349_valid : certificate_1349.Valid 15 7 (patternOrder [[],[1,1,1,2,1]]) (patternClique [[],[1,1,1,2,1]]) (patternEdges [[],[1,1,1,2,1]]) (patternAmount [[],[1,1,1,2,1]]) (patternEdgeCount [[],[1,1,1,2,1]]) [] := certificate_1349_checked

theorem certificate_1350_checked : certificate_1350.Valid 15 7 14 certificate_1350_q certificate_1350_edges 7 5 [] := by decide +kernel
theorem certificate_1350_valid : certificate_1350.Valid 15 7 (patternOrder [[],[1,1,1,2,2]]) (patternClique [[],[1,1,1,2,2]]) (patternEdges [[],[1,1,1,2,2]]) (patternAmount [[],[1,1,1,2,2]]) (patternEdgeCount [[],[1,1,1,2,2]]) [] := certificate_1350_checked

theorem certificate_1351_checked : certificate_1351.Valid 15 7 15 certificate_1351_q certificate_1351_edges 8 5 [] := by decide +kernel
theorem certificate_1351_valid : certificate_1351.Valid 15 7 (patternOrder [[],[1,1,1,2,3]]) (patternClique [[],[1,1,1,2,3]]) (patternEdges [[],[1,1,1,2,3]]) (patternAmount [[],[1,1,1,2,3]]) (patternEdgeCount [[],[1,1,1,2,3]]) [] := certificate_1351_checked

theorem certificate_1352_checked : certificate_1352.Valid 15 7 14 certificate_1352_q certificate_1352_edges 7 5 [] := by decide +kernel
theorem certificate_1352_valid : certificate_1352.Valid 15 7 (patternOrder [[],[1,1,1,3,1]]) (patternClique [[],[1,1,1,3,1]]) (patternEdges [[],[1,1,1,3,1]]) (patternAmount [[],[1,1,1,3,1]]) (patternEdgeCount [[],[1,1,1,3,1]]) [] := certificate_1352_checked

theorem certificate_1353_checked : certificate_1353.Valid 15 7 15 certificate_1353_q certificate_1353_edges 8 5 [] := by decide +kernel
theorem certificate_1353_valid : certificate_1353.Valid 15 7 (patternOrder [[],[1,1,1,3,2]]) (patternClique [[],[1,1,1,3,2]]) (patternEdges [[],[1,1,1,3,2]]) (patternAmount [[],[1,1,1,3,2]]) (patternEdgeCount [[],[1,1,1,3,2]]) [] := certificate_1353_checked

theorem certificate_1354_checked : certificate_1354.Valid 15 7 15 certificate_1354_q certificate_1354_edges 8 5 [] := by decide +kernel
theorem certificate_1354_valid : certificate_1354.Valid 15 7 (patternOrder [[],[1,1,1,4,1]]) (patternClique [[],[1,1,1,4,1]]) (patternEdges [[],[1,1,1,4,1]]) (patternAmount [[],[1,1,1,4,1]]) (patternEdgeCount [[],[1,1,1,4,1]]) [] := certificate_1354_checked

theorem certificate_1355_checked : certificate_1355.Valid 15 7 13 certificate_1355_q certificate_1355_edges 6 4 [] := by decide +kernel
theorem certificate_1355_valid : certificate_1355.Valid 15 7 (patternOrder [[],[1,1,2],[2]]) (patternClique [[],[1,1,2],[2]]) (patternEdges [[],[1,1,2],[2]]) (patternAmount [[],[1,1,2],[2]]) (patternEdgeCount [[],[1,1,2],[2]]) [] := certificate_1355_checked

theorem certificate_1356_checked : certificate_1356.Valid 15 7 14 certificate_1356_q certificate_1356_edges 7 4 [] := by decide +kernel
theorem certificate_1356_valid : certificate_1356.Valid 15 7 (patternOrder [[],[1,1,2],[3]]) (patternClique [[],[1,1,2],[3]]) (patternEdges [[],[1,1,2],[3]]) (patternAmount [[],[1,1,2],[3]]) (patternEdgeCount [[],[1,1,2],[3]]) [] := certificate_1356_checked

theorem certificate_1357_checked : certificate_1357.Valid 15 7 15 certificate_1357_q certificate_1357_edges 8 4 [] := by decide +kernel
theorem certificate_1357_valid : certificate_1357.Valid 15 7 (patternOrder [[],[1,1,2],[4]]) (patternClique [[],[1,1,2],[4]]) (patternEdges [[],[1,1,2],[4]]) (patternAmount [[],[1,1,2],[4]]) (patternEdgeCount [[],[1,1,2],[4]]) [] := certificate_1357_checked

theorem certificate_1358_checked : certificate_1358.Valid 15 7 13 certificate_1358_q certificate_1358_edges 6 5 [] := by decide +kernel
theorem certificate_1358_valid : certificate_1358.Valid 15 7 (patternOrder [[],[1,1,2,1,1]]) (patternClique [[],[1,1,2,1,1]]) (patternEdges [[],[1,1,2,1,1]]) (patternAmount [[],[1,1,2,1,1]]) (patternEdgeCount [[],[1,1,2,1,1]]) [] := certificate_1358_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns15x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_15_7_12_verified_oai : ∀ D ∈ patterns_15_7_12, PatternVerified 15 7 D := by

  simp only [patterns_15_7_12, List.forall_mem_cons]

  exact ⟨⟨certificate_1343, certificate_1343_valid⟩, ⟨⟨certificate_1344, certificate_1344_valid⟩, ⟨⟨certificate_1345, certificate_1345_valid⟩, ⟨⟨certificate_1346, certificate_1346_valid⟩, ⟨⟨certificate_1347, certificate_1347_valid⟩, ⟨⟨certificate_1348, certificate_1348_valid⟩, ⟨⟨certificate_1349, certificate_1349_valid⟩, ⟨⟨certificate_1350, certificate_1350_valid⟩, ⟨⟨certificate_1351, certificate_1351_valid⟩, ⟨⟨certificate_1352, certificate_1352_valid⟩, ⟨⟨certificate_1353, certificate_1353_valid⟩, ⟨⟨certificate_1354, certificate_1354_valid⟩, ⟨⟨certificate_1355, certificate_1355_valid⟩, ⟨⟨certificate_1356, certificate_1356_valid⟩, ⟨⟨certificate_1357, certificate_1357_valid⟩, ⟨⟨certificate_1358, certificate_1358_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_12_verified_oai := @OAI.CycleClique.patterns_15_7_12_verified_oai
