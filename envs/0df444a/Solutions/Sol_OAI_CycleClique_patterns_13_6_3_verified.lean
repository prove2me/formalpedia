-- Prove2me | solution 1 for OAI.CycleClique.patterns_13_6_3_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:05:55.281629+00:00
-- url     : https://prove2.me/submissions/a3cfb30e-cfd1-4ff5-bd84-00b025109fda

import Mathlib
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates018
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_573_checked : certificate_573.Valid 13 6 12 certificate_573_q certificate_573_edges 6 3 [] := by decide +kernel
theorem certificate_573_valid : certificate_573.Valid 13 6 (patternOrder [[],[],[2,2,2]]) (patternClique [[],[],[2,2,2]]) (patternEdges [[],[],[2,2,2]]) (patternAmount [[],[],[2,2,2]]) (patternEdgeCount [[],[],[2,2,2]]) [] := certificate_573_checked

theorem certificate_574_checked : certificate_574.Valid 13 6 13 certificate_574_q certificate_574_edges 7 3 [] := by decide +kernel
theorem certificate_574_valid : certificate_574.Valid 13 6 (patternOrder [[],[],[2,2,3]]) (patternClique [[],[],[2,2,3]]) (patternEdges [[],[],[2,2,3]]) (patternAmount [[],[],[2,2,3]]) (patternEdgeCount [[],[],[2,2,3]]) [] := certificate_574_checked

theorem certificate_575_checked : certificate_575.Valid 13 6 13 certificate_575_q certificate_575_edges 7 3 [] := by decide +kernel
theorem certificate_575_valid : certificate_575.Valid 13 6 (patternOrder [[],[],[2,3,2]]) (patternClique [[],[],[2,3,2]]) (patternEdges [[],[],[2,3,2]]) (patternAmount [[],[],[2,3,2]]) (patternEdgeCount [[],[],[2,3,2]]) [] := certificate_575_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates019
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_576_checked : certificate_576.Valid 13 6 12 certificate_576_q certificate_576_edges 6 2 [] := by decide +kernel
theorem certificate_576_valid : certificate_576.Valid 13 6 (patternOrder [[],[],[3],[3]]) (patternClique [[],[],[3],[3]]) (patternEdges [[],[],[3],[3]]) (patternAmount [[],[],[3],[3]]) (patternEdgeCount [[],[],[3],[3]]) [] := certificate_576_checked

theorem certificate_577_part_8_checked : certificate_577_part_8.Valid 13 6 13 certificate_577_q certificate_577_part_8_E 7 2 certificate_577_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_14_checked : certificate_577_part_14.Valid 13 6 13 certificate_577_q certificate_577_part_14_E 7 2 certificate_577_part_14_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_577_part_19_checked : certificate_577_part_19.Valid 13 6 14 certificate_577_q certificate_577_part_19_E 7 2 certificate_577_part_19_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_577_part_21_checked : certificate_577_part_21.Valid 13 6 13 certificate_577_q certificate_577_part_21_E 7 2 certificate_577_part_21_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_577_part_20_checked : certificate_577_part_20.Valid 13 6 13 certificate_577_q certificate_577_part_20_E 7 2 certificate_577_part_20_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_21_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_26_checked : certificate_577_part_26.Valid 13 6 13 certificate_577_q certificate_577_part_26_E 7 2 certificate_577_part_26_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_577_part_27_checked : certificate_577_part_27.Valid 13 6 13 certificate_577_q certificate_577_part_27_E 7 2 certificate_577_part_27_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_577_part_28_checked : certificate_577_part_28.Valid 13 6 13 certificate_577_q certificate_577_part_28_E 7 2 certificate_577_part_28_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_29_checked : certificate_577_part_29.Valid 13 6 13 certificate_577_q certificate_577_part_29_E 7 2 certificate_577_part_29_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_31_checked : certificate_577_part_31.Valid 13 6 13 certificate_577_q certificate_577_part_31_E 7 2 certificate_577_part_31_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

theorem certificate_577_part_36_checked : certificate_577_part_36.Valid 13 6 13 certificate_577_q certificate_577_part_36_E 7 2 certificate_577_part_36_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_577_part_38_checked : certificate_577_part_38.Valid 13 6 13 certificate_577_q certificate_577_part_38_E 7 2 certificate_577_part_38_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

theorem certificate_577_part_42_checked : certificate_577_part_42.Valid 13 6 14 certificate_577_q certificate_577_part_42_E 7 2 certificate_577_part_42_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_577_part_41_checked : certificate_577_part_41.Valid 13 6 14 certificate_577_q certificate_577_part_41_E 7 2 certificate_577_part_41_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_42_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_40_checked : certificate_577_part_40.Valid 13 6 14 certificate_577_q certificate_577_part_40_E 7 2 certificate_577_part_40_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_41_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_43_checked : certificate_577_part_43.Valid 13 6 13 certificate_577_q certificate_577_part_43_E 7 2 certificate_577_part_43_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_577_part_44_checked : certificate_577_part_44.Valid 13 6 13 certificate_577_q certificate_577_part_44_E 7 2 certificate_577_part_44_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_46_checked : certificate_577_part_46.Valid 13 6 13 certificate_577_q certificate_577_part_46_E 7 2 certificate_577_part_46_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_577_part_47_checked : certificate_577_part_47.Valid 13 6 13 certificate_577_q certificate_577_part_47_E 7 2 certificate_577_part_47_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_577_part_50_checked : certificate_577_part_50.Valid 13 6 13 certificate_577_q certificate_577_part_50_E 7 2 certificate_577_part_50_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_577_part_49_checked : certificate_577_part_49.Valid 13 6 13 certificate_577_q certificate_577_part_49_E 7 2 certificate_577_part_49_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_50_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_48_checked : certificate_577_part_48.Valid 13 6 13 certificate_577_q certificate_577_part_48_E 7 2 certificate_577_part_48_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_49_checked⟩, by decide +kernel⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_45_checked : certificate_577_part_45.Valid 13 6 13 certificate_577_q certificate_577_part_45_E 7 2 certificate_577_part_45_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_46_checked⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_47_checked⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_48_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_39_checked : certificate_577_part_39.Valid 13 6 13 certificate_577_q certificate_577_part_39_E 7 2 certificate_577_part_39_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_40_checked⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_43_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_44_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_45_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_37_checked : certificate_577_part_37.Valid 13 6 13 certificate_577_q certificate_577_part_37_E 7 2 certificate_577_part_37_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_38_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_39_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_35_checked : certificate_577_part_35.Valid 13 6 13 certificate_577_q certificate_577_part_35_E 7 2 certificate_577_part_35_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_577_part_36_checked, certificate_577_part_37_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_34_checked : certificate_577_part_34.Valid 13 6 13 certificate_577_q certificate_577_part_34_E 7 2 certificate_577_part_34_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_35_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_33_checked : certificate_577_part_33.Valid 13 6 13 certificate_577_q certificate_577_part_33_E 7 2 certificate_577_part_33_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_34_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_32_checked : certificate_577_part_32.Valid 13 6 13 certificate_577_q certificate_577_part_32_E 7 2 certificate_577_part_32_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_33_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_30_checked : certificate_577_part_30.Valid 13 6 13 certificate_577_q certificate_577_part_30_E 7 2 certificate_577_part_30_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_31_checked⟩⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_32_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_25_checked : certificate_577_part_25.Valid 13 6 13 certificate_577_q certificate_577_part_25_E 7 2 certificate_577_part_25_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_26_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_27_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_28_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_577_part_29_checked, certificate_577_part_30_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_24_checked : certificate_577_part_24.Valid 13 6 13 certificate_577_q certificate_577_part_24_E 7 2 certificate_577_part_24_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_25_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_23_checked : certificate_577_part_23.Valid 13 6 13 certificate_577_q certificate_577_part_23_E 7 2 certificate_577_part_23_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_24_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_22_checked : certificate_577_part_22.Valid 13 6 13 certificate_577_q certificate_577_part_22_E 7 2 certificate_577_part_22_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_23_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_18_checked : certificate_577_part_18.Valid 13 6 13 certificate_577_q certificate_577_part_18_E 7 2 certificate_577_part_18_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_19_checked⟩⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_20_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_22_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_17_checked : certificate_577_part_17.Valid 13 6 13 certificate_577_q certificate_577_part_17_E 7 2 certificate_577_part_17_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_18_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_16_checked : certificate_577_part_16.Valid 13 6 13 certificate_577_q certificate_577_part_16_E 7 2 certificate_577_part_16_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_17_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_15_checked : certificate_577_part_15.Valid 13 6 13 certificate_577_q certificate_577_part_15_E 7 2 certificate_577_part_15_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_16_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_13_checked : certificate_577_part_13.Valid 13 6 13 certificate_577_q certificate_577_part_13_E 7 2 certificate_577_part_13_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_14_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_15_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_12_checked : certificate_577_part_12.Valid 13 6 13 certificate_577_q certificate_577_part_12_E 7 2 certificate_577_part_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_13_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_11_checked : certificate_577_part_11.Valid 13 6 13 certificate_577_q certificate_577_part_11_E 7 2 certificate_577_part_11_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_12_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_10_checked : certificate_577_part_10.Valid 13 6 13 certificate_577_q certificate_577_part_10_E 7 2 certificate_577_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_11_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_9_checked : certificate_577_part_9.Valid 13 6 13 certificate_577_q certificate_577_part_9_E 7 2 certificate_577_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_10_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_7_checked : certificate_577_part_7.Valid 13 6 13 certificate_577_q certificate_577_part_7_E 7 2 certificate_577_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_8_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_9_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_6_checked : certificate_577_part_6.Valid 13 6 13 certificate_577_q certificate_577_part_6_E 7 2 certificate_577_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_5_checked : certificate_577_part_5.Valid 13 6 13 certificate_577_q certificate_577_part_5_E 7 2 certificate_577_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_4_checked : certificate_577_part_4.Valid 13 6 13 certificate_577_q certificate_577_part_4_E 7 2 certificate_577_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_3_checked : certificate_577_part_3.Valid 13 6 13 certificate_577_q certificate_577_part_3_E 7 2 certificate_577_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_2_checked : certificate_577_part_2.Valid 13 6 13 certificate_577_q certificate_577_part_2_E 7 2 certificate_577_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_part_1_checked : certificate_577_part_1.Valid 13 6 13 certificate_577_q certificate_577_part_1_E 7 2 certificate_577_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_checked : certificate_577.Valid 13 6 13 certificate_577_q certificate_577_E 7 2 certificate_577_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_577_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_577_valid : certificate_577.Valid 13 6 (patternOrder [[],[],[3],[4]]) (patternClique [[],[],[3],[4]]) (patternEdges [[],[],[3],[4]]) (patternAmount [[],[],[3],[4]]) (patternEdgeCount [[],[],[3],[4]]) [] := certificate_577_checked

theorem certificate_578_checked : certificate_578.Valid 13 6 13 certificate_578_q certificate_578_edges 7 3 [] := by decide +kernel
theorem certificate_578_valid : certificate_578.Valid 13 6 (patternOrder [[],[],[3,1,3]]) (patternClique [[],[],[3,1,3]]) (patternEdges [[],[],[3,1,3]]) (patternAmount [[],[],[3,1,3]]) (patternEdgeCount [[],[],[3,1,3]]) [] := certificate_578_checked

theorem certificate_579_checked : certificate_579.Valid 13 6 9 certificate_579_q certificate_579_edges 3 3 [] := by decide +kernel
theorem certificate_579_valid : certificate_579.Valid 13 6 (patternOrder [[],[1],[1,1]]) (patternClique [[],[1],[1,1]]) (patternEdges [[],[1],[1,1]]) (patternAmount [[],[1],[1,1]]) (patternEdgeCount [[],[1],[1,1]]) [] := certificate_579_checked

theorem certificate_580_checked : certificate_580.Valid 13 6 10 certificate_580_q certificate_580_edges 4 3 [] := by decide +kernel
theorem certificate_580_valid : certificate_580.Valid 13 6 (patternOrder [[],[1],[1,2]]) (patternClique [[],[1],[1,2]]) (patternEdges [[],[1],[1,2]]) (patternAmount [[],[1],[1,2]]) (patternEdgeCount [[],[1],[1,2]]) [] := certificate_580_checked

theorem certificate_581_checked : certificate_581.Valid 13 6 11 certificate_581_q certificate_581_edges 5 3 [] := by decide +kernel
theorem certificate_581_valid : certificate_581.Valid 13 6 (patternOrder [[],[1],[1,3]]) (patternClique [[],[1],[1,3]]) (patternEdges [[],[1],[1,3]]) (patternAmount [[],[1],[1,3]]) (patternEdgeCount [[],[1],[1,3]]) [] := certificate_581_checked

theorem certificate_582_checked : certificate_582.Valid 13 6 12 certificate_582_q certificate_582_edges 6 3 [] := by decide +kernel
theorem certificate_582_valid : certificate_582.Valid 13 6 (patternOrder [[],[1],[1,4]]) (patternClique [[],[1],[1,4]]) (patternEdges [[],[1],[1,4]]) (patternAmount [[],[1],[1,4]]) (patternEdgeCount [[],[1],[1,4]]) [] := certificate_582_checked

theorem certificate_583_checked : certificate_583.Valid 13 6 13 certificate_583_q certificate_583_edges 7 3 [] := by decide +kernel
theorem certificate_583_valid : certificate_583.Valid 13 6 (patternOrder [[],[1],[1,5]]) (patternClique [[],[1],[1,5]]) (patternEdges [[],[1],[1,5]]) (patternAmount [[],[1],[1,5]]) (patternEdgeCount [[],[1],[1,5]]) [] := certificate_583_checked

theorem certificate_584_checked : certificate_584.Valid 13 6 11 certificate_584_q certificate_584_edges 5 3 [] := by decide +kernel
theorem certificate_584_valid : certificate_584.Valid 13 6 (patternOrder [[],[1],[2,2]]) (patternClique [[],[1],[2,2]]) (patternEdges [[],[1],[2,2]]) (patternAmount [[],[1],[2,2]]) (patternEdgeCount [[],[1],[2,2]]) [] := certificate_584_checked

theorem certificate_585_checked : certificate_585.Valid 13 6 12 certificate_585_q certificate_585_edges 6 3 [] := by decide +kernel
theorem certificate_585_valid : certificate_585.Valid 13 6 (patternOrder [[],[1],[2,3]]) (patternClique [[],[1],[2,3]]) (patternEdges [[],[1],[2,3]]) (patternAmount [[],[1],[2,3]]) (patternEdgeCount [[],[1],[2,3]]) [] := certificate_585_checked

theorem certificate_586_checked : certificate_586.Valid 13 6 13 certificate_586_q certificate_586_edges 7 3 [] := by decide +kernel
theorem certificate_586_valid : certificate_586.Valid 13 6 (patternOrder [[],[1],[2,4]]) (patternClique [[],[1],[2,4]]) (patternEdges [[],[1],[2,4]]) (patternAmount [[],[1],[2,4]]) (patternEdgeCount [[],[1],[2,4]]) [] := certificate_586_checked

theorem certificate_587_checked : certificate_587.Valid 13 6 13 certificate_587_q certificate_587_edges 7 3 [] := by decide +kernel
theorem certificate_587_valid : certificate_587.Valid 13 6 (patternOrder [[],[1],[3,3]]) (patternClique [[],[1],[3,3]]) (patternEdges [[],[1],[3,3]]) (patternAmount [[],[1],[3,3]]) (patternEdgeCount [[],[1],[3,3]]) [] := certificate_587_checked

theorem certificate_588_checked : certificate_588.Valid 13 6 10 certificate_588_q certificate_588_edges 4 3 [] := by decide +kernel
theorem certificate_588_valid : certificate_588.Valid 13 6 (patternOrder [[],[1,1],[2]]) (patternClique [[],[1,1],[2]]) (patternEdges [[],[1,1],[2]]) (patternAmount [[],[1,1],[2]]) (patternEdgeCount [[],[1,1],[2]]) [] := certificate_588_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns13x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_13_6_3_verified_oai : ∀ D ∈ patterns_13_6_3, PatternVerified 13 6 D := by

  simp only [patterns_13_6_3, List.forall_mem_cons]

  exact ⟨⟨certificate_573, certificate_573_valid⟩, ⟨⟨certificate_574, certificate_574_valid⟩, ⟨⟨certificate_575, certificate_575_valid⟩, ⟨⟨certificate_576, certificate_576_valid⟩, ⟨⟨certificate_577, certificate_577_valid⟩, ⟨⟨certificate_578, certificate_578_valid⟩, ⟨⟨certificate_579, certificate_579_valid⟩, ⟨⟨certificate_580, certificate_580_valid⟩, ⟨⟨certificate_581, certificate_581_valid⟩, ⟨⟨certificate_582, certificate_582_valid⟩, ⟨⟨certificate_583, certificate_583_valid⟩, ⟨⟨certificate_584, certificate_584_valid⟩, ⟨⟨certificate_585, certificate_585_valid⟩, ⟨⟨certificate_586, certificate_586_valid⟩, ⟨⟨certificate_587, certificate_587_valid⟩, ⟨⟨certificate_588, certificate_588_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_13_6_3_verified_oai := @OAI.CycleClique.patterns_13_6_3_verified_oai
