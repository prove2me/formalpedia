-- Prove2me | solution 1 for OAI.CycleClique.patterns_15_7_11_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:30:48.546908+00:00
-- url     : https://prove2.me/submissions/c59cffc7-80b6-433f-ab4a-de3a3d55c888

import Mathlib
import Definitions.Def_OAIQ107D126
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates042
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1327_checked : certificate_1327.Valid 15 7 15 certificate_1327_q certificate_1327_edges 8 4 [] := by decide +kernel
theorem certificate_1327_valid : certificate_1327.Valid 15 7 (patternOrder [[],[1],[2,2,3]]) (patternClique [[],[1],[2,2,3]]) (patternEdges [[],[1],[2,2,3]]) (patternAmount [[],[1],[2,2,3]]) (patternEdgeCount [[],[1],[2,2,3]]) [] := certificate_1327_checked

theorem certificate_1328_checked : certificate_1328.Valid 15 7 15 certificate_1328_q certificate_1328_edges 8 4 [] := by decide +kernel
theorem certificate_1328_valid : certificate_1328.Valid 15 7 (patternOrder [[],[1],[2,3,2]]) (patternClique [[],[1],[2,3,2]]) (patternEdges [[],[1],[2,3,2]]) (patternAmount [[],[1],[2,3,2]]) (patternEdgeCount [[],[1],[2,3,2]]) [] := certificate_1328_checked

theorem certificate_1329_checked : certificate_1329.Valid 15 7 14 certificate_1329_q certificate_1329_edges 7 3 [] := by decide +kernel
theorem certificate_1329_valid : certificate_1329.Valid 15 7 (patternOrder [[],[1],[3],[3]]) (patternClique [[],[1],[3],[3]]) (patternEdges [[],[1],[3],[3]]) (patternAmount [[],[1],[3],[3]]) (patternEdgeCount [[],[1],[3],[3]]) [] := certificate_1329_checked

theorem certificate_1330_checked : certificate_1330.Valid 15 7 15 certificate_1330_q certificate_1330_edges 8 3 [] := by decide +kernel
theorem certificate_1330_valid : certificate_1330.Valid 15 7 (patternOrder [[],[1],[3],[4]]) (patternClique [[],[1],[3],[4]]) (patternEdges [[],[1],[3],[4]]) (patternAmount [[],[1],[3],[4]]) (patternEdgeCount [[],[1],[3],[4]]) [] := certificate_1330_checked

theorem certificate_1331_checked : certificate_1331.Valid 15 7 15 certificate_1331_q certificate_1331_edges 8 4 [] := by decide +kernel
theorem certificate_1331_valid : certificate_1331.Valid 15 7 (patternOrder [[],[1],[3,1,3]]) (patternClique [[],[1],[3,1,3]]) (patternEdges [[],[1],[3,1,3]]) (patternAmount [[],[1],[3,1,3]]) (patternEdgeCount [[],[1],[3,1,3]]) [] := certificate_1331_checked

theorem certificate_1332_checked : certificate_1332.Valid 15 7 11 certificate_1332_q certificate_1332_edges 4 4 [] := by decide +kernel
theorem certificate_1332_valid : certificate_1332.Valid 15 7 (patternOrder [[],[1,1],[1,1]]) (patternClique [[],[1,1],[1,1]]) (patternEdges [[],[1,1],[1,1]]) (patternAmount [[],[1,1],[1,1]]) (patternEdgeCount [[],[1,1],[1,1]]) [] := certificate_1332_checked

theorem certificate_1333_checked : certificate_1333.Valid 15 7 12 certificate_1333_q certificate_1333_edges 5 4 [] := by decide +kernel
theorem certificate_1333_valid : certificate_1333.Valid 15 7 (patternOrder [[],[1,1],[1,2]]) (patternClique [[],[1,1],[1,2]]) (patternEdges [[],[1,1],[1,2]]) (patternAmount [[],[1,1],[1,2]]) (patternEdgeCount [[],[1,1],[1,2]]) [] := certificate_1333_checked

theorem certificate_1334_checked : certificate_1334.Valid 15 7 13 certificate_1334_q certificate_1334_edges 6 4 [] := by decide +kernel
theorem certificate_1334_valid : certificate_1334.Valid 15 7 (patternOrder [[],[1,1],[1,3]]) (patternClique [[],[1,1],[1,3]]) (patternEdges [[],[1,1],[1,3]]) (patternAmount [[],[1,1],[1,3]]) (patternEdgeCount [[],[1,1],[1,3]]) [] := certificate_1334_checked

theorem certificate_1335_checked : certificate_1335.Valid 15 7 14 certificate_1335_q certificate_1335_edges 7 4 [] := by decide +kernel
theorem certificate_1335_valid : certificate_1335.Valid 15 7 (patternOrder [[],[1,1],[1,4]]) (patternClique [[],[1,1],[1,4]]) (patternEdges [[],[1,1],[1,4]]) (patternAmount [[],[1,1],[1,4]]) (patternEdgeCount [[],[1,1],[1,4]]) [] := certificate_1335_checked

theorem certificate_1336_checked : certificate_1336.Valid 15 7 15 certificate_1336_q certificate_1336_edges 8 4 [] := by decide +kernel
theorem certificate_1336_valid : certificate_1336.Valid 15 7 (patternOrder [[],[1,1],[1,5]]) (patternClique [[],[1,1],[1,5]]) (patternEdges [[],[1,1],[1,5]]) (patternAmount [[],[1,1],[1,5]]) (patternEdgeCount [[],[1,1],[1,5]]) [] := certificate_1336_checked

theorem certificate_1337_checked : certificate_1337.Valid 15 7 13 certificate_1337_q certificate_1337_edges 6 4 [] := by decide +kernel
theorem certificate_1337_valid : certificate_1337.Valid 15 7 (patternOrder [[],[1,1],[2,2]]) (patternClique [[],[1,1],[2,2]]) (patternEdges [[],[1,1],[2,2]]) (patternAmount [[],[1,1],[2,2]]) (patternEdgeCount [[],[1,1],[2,2]]) [] := certificate_1337_checked

theorem certificate_1338_checked : certificate_1338.Valid 15 7 14 certificate_1338_q certificate_1338_edges 7 4 [] := by decide +kernel
theorem certificate_1338_valid : certificate_1338.Valid 15 7 (patternOrder [[],[1,1],[2,3]]) (patternClique [[],[1,1],[2,3]]) (patternEdges [[],[1,1],[2,3]]) (patternAmount [[],[1,1],[2,3]]) (patternEdgeCount [[],[1,1],[2,3]]) [] := certificate_1338_checked

theorem certificate_1339_checked : certificate_1339.Valid 15 7 15 certificate_1339_q certificate_1339_edges 8 4 [] := by decide +kernel
theorem certificate_1339_valid : certificate_1339.Valid 15 7 (patternOrder [[],[1,1],[2,4]]) (patternClique [[],[1,1],[2,4]]) (patternEdges [[],[1,1],[2,4]]) (patternAmount [[],[1,1],[2,4]]) (patternEdgeCount [[],[1,1],[2,4]]) [] := certificate_1339_checked

theorem certificate_1340_checked : certificate_1340.Valid 15 7 15 certificate_1340_q certificate_1340_edges 8 4 [] := by decide +kernel
theorem certificate_1340_valid : certificate_1340.Valid 15 7 (patternOrder [[],[1,1],[3,3]]) (patternClique [[],[1,1],[3,3]]) (patternEdges [[],[1,1],[3,3]]) (patternAmount [[],[1,1],[3,3]]) (patternEdgeCount [[],[1,1],[3,3]]) [] := certificate_1340_checked

theorem certificate_1341_checked : certificate_1341.Valid 15 7 12 certificate_1341_q certificate_1341_edges 5 4 [] := by decide +kernel
theorem certificate_1341_valid : certificate_1341.Valid 15 7 (patternOrder [[],[1,1,1],[2]]) (patternClique [[],[1,1,1],[2]]) (patternEdges [[],[1,1,1],[2]]) (patternAmount [[],[1,1,1],[2]]) (patternEdgeCount [[],[1,1,1],[2]]) [] := certificate_1341_checked

theorem certificate_1342_checked : certificate_1342.Valid 15 7 13 certificate_1342_q certificate_1342_edges 6 4 [] := by decide +kernel
theorem certificate_1342_valid : certificate_1342.Valid 15 7 (patternOrder [[],[1,1,1],[3]]) (patternClique [[],[1,1,1],[3]]) (patternEdges [[],[1,1,1],[3]]) (patternAmount [[],[1,1,1],[3]]) (patternEdgeCount [[],[1,1,1],[3]]) [] := certificate_1342_checked

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

theorem patterns_15_7_11_verified_oai : ∀ D ∈ patterns_15_7_11, PatternVerified 15 7 D := by

  simp only [patterns_15_7_11, List.forall_mem_cons]

  exact ⟨⟨certificate_1327, certificate_1327_valid⟩, ⟨⟨certificate_1328, certificate_1328_valid⟩, ⟨⟨certificate_1329, certificate_1329_valid⟩, ⟨⟨certificate_1330, certificate_1330_valid⟩, ⟨⟨certificate_1331, certificate_1331_valid⟩, ⟨⟨certificate_1332, certificate_1332_valid⟩, ⟨⟨certificate_1333, certificate_1333_valid⟩, ⟨⟨certificate_1334, certificate_1334_valid⟩, ⟨⟨certificate_1335, certificate_1335_valid⟩, ⟨⟨certificate_1336, certificate_1336_valid⟩, ⟨⟨certificate_1337, certificate_1337_valid⟩, ⟨⟨certificate_1338, certificate_1338_valid⟩, ⟨⟨certificate_1339, certificate_1339_valid⟩, ⟨⟨certificate_1340, certificate_1340_valid⟩, ⟨⟨certificate_1341, certificate_1341_valid⟩, ⟨⟨certificate_1342, certificate_1342_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_15_7_11_verified_oai := @OAI.CycleClique.patterns_15_7_11_verified_oai
