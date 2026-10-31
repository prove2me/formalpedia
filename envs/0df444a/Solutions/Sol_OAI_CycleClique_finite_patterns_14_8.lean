-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_14_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:31:00.873974+00:00
-- url     : https://prove2.me/submissions/7d269e58-9999-41f7-84a7-785669df7ca5

import Mathlib
import Definitions.Def_OAIQ107D126
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates033
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1033_checked : certificate_1033.Valid 14 8 8 certificate_1033_q certificate_1033_edges 0 0 [] := by decide +kernel
theorem certificate_1033_valid : certificate_1033.Valid 14 8 (patternOrder [[],[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[],[]]) [] := certificate_1033_checked

theorem certificate_1034_checked : certificate_1034.Valid 14 8 9 certificate_1034_q certificate_1034_edges 1 1 [] := by decide +kernel
theorem certificate_1034_valid : certificate_1034.Valid 14 8 (patternOrder [[],[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[],[1]]) [] := certificate_1034_checked

theorem certificate_1035_checked : certificate_1035.Valid 14 8 10 certificate_1035_q certificate_1035_edges 2 1 [] := by decide +kernel
theorem certificate_1035_valid : certificate_1035.Valid 14 8 (patternOrder [[],[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[],[2]]) [] := certificate_1035_checked

theorem certificate_1036_checked : certificate_1036.Valid 14 8 11 certificate_1036_q certificate_1036_edges 3 1 [] := by decide +kernel
theorem certificate_1036_valid : certificate_1036.Valid 14 8 (patternOrder [[],[],[],[],[],[],[3]]) (patternClique [[],[],[],[],[],[],[3]]) (patternEdges [[],[],[],[],[],[],[3]]) (patternAmount [[],[],[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[],[],[3]]) [] := certificate_1036_checked

theorem certificate_1037_checked : certificate_1037.Valid 14 8 12 certificate_1037_q certificate_1037_edges 4 1 [] := by decide +kernel
theorem certificate_1037_valid : certificate_1037.Valid 14 8 (patternOrder [[],[],[],[],[],[],[4]]) (patternClique [[],[],[],[],[],[],[4]]) (patternEdges [[],[],[],[],[],[],[4]]) (patternAmount [[],[],[],[],[],[],[4]]) (patternEdgeCount [[],[],[],[],[],[],[4]]) [] := certificate_1037_checked

theorem certificate_1038_checked : certificate_1038.Valid 14 8 13 certificate_1038_q certificate_1038_edges 5 1 [] := by decide +kernel
theorem certificate_1038_valid : certificate_1038.Valid 14 8 (patternOrder [[],[],[],[],[],[],[5]]) (patternClique [[],[],[],[],[],[],[5]]) (patternEdges [[],[],[],[],[],[],[5]]) (patternAmount [[],[],[],[],[],[],[5]]) (patternEdgeCount [[],[],[],[],[],[],[5]]) [] := certificate_1038_checked

theorem certificate_1039_checked : certificate_1039.Valid 14 8 14 certificate_1039_q certificate_1039_edges 6 1 [] := by decide +kernel
theorem certificate_1039_valid : certificate_1039.Valid 14 8 (patternOrder [[],[],[],[],[],[],[6]]) (patternClique [[],[],[],[],[],[],[6]]) (patternEdges [[],[],[],[],[],[],[6]]) (patternAmount [[],[],[],[],[],[],[6]]) (patternEdgeCount [[],[],[],[],[],[],[6]]) [] := certificate_1039_checked

theorem certificate_1040_checked : certificate_1040.Valid 14 8 10 certificate_1040_q certificate_1040_edges 2 2 [] := by decide +kernel
theorem certificate_1040_valid : certificate_1040.Valid 14 8 (patternOrder [[],[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[],[1,1]]) [] := certificate_1040_checked

theorem certificate_1041_checked : certificate_1041.Valid 14 8 11 certificate_1041_q certificate_1041_edges 3 2 [] := by decide +kernel
theorem certificate_1041_valid : certificate_1041.Valid 14 8 (patternOrder [[],[],[],[],[],[1,2]]) (patternClique [[],[],[],[],[],[1,2]]) (patternEdges [[],[],[],[],[],[1,2]]) (patternAmount [[],[],[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[],[],[1,2]]) [] := certificate_1041_checked

theorem certificate_1042_checked : certificate_1042.Valid 14 8 12 certificate_1042_q certificate_1042_edges 4 2 [] := by decide +kernel
theorem certificate_1042_valid : certificate_1042.Valid 14 8 (patternOrder [[],[],[],[],[],[1,3]]) (patternClique [[],[],[],[],[],[1,3]]) (patternEdges [[],[],[],[],[],[1,3]]) (patternAmount [[],[],[],[],[],[1,3]]) (patternEdgeCount [[],[],[],[],[],[1,3]]) [] := certificate_1042_checked

theorem certificate_1043_checked : certificate_1043.Valid 14 8 13 certificate_1043_q certificate_1043_edges 5 2 [] := by decide +kernel
theorem certificate_1043_valid : certificate_1043.Valid 14 8 (patternOrder [[],[],[],[],[],[1,4]]) (patternClique [[],[],[],[],[],[1,4]]) (patternEdges [[],[],[],[],[],[1,4]]) (patternAmount [[],[],[],[],[],[1,4]]) (patternEdgeCount [[],[],[],[],[],[1,4]]) [] := certificate_1043_checked

theorem certificate_1044_checked : certificate_1044.Valid 14 8 14 certificate_1044_q certificate_1044_edges 6 2 [] := by decide +kernel
theorem certificate_1044_valid : certificate_1044.Valid 14 8 (patternOrder [[],[],[],[],[],[1,5]]) (patternClique [[],[],[],[],[],[1,5]]) (patternEdges [[],[],[],[],[],[1,5]]) (patternAmount [[],[],[],[],[],[1,5]]) (patternEdgeCount [[],[],[],[],[],[1,5]]) [] := certificate_1044_checked

theorem certificate_1045_checked : certificate_1045.Valid 14 8 12 certificate_1045_q certificate_1045_edges 4 2 [] := by decide +kernel
theorem certificate_1045_valid : certificate_1045.Valid 14 8 (patternOrder [[],[],[],[],[],[2,2]]) (patternClique [[],[],[],[],[],[2,2]]) (patternEdges [[],[],[],[],[],[2,2]]) (patternAmount [[],[],[],[],[],[2,2]]) (patternEdgeCount [[],[],[],[],[],[2,2]]) [] := certificate_1045_checked

theorem certificate_1046_checked : certificate_1046.Valid 14 8 13 certificate_1046_q certificate_1046_edges 5 2 [] := by decide +kernel
theorem certificate_1046_valid : certificate_1046.Valid 14 8 (patternOrder [[],[],[],[],[],[2,3]]) (patternClique [[],[],[],[],[],[2,3]]) (patternEdges [[],[],[],[],[],[2,3]]) (patternAmount [[],[],[],[],[],[2,3]]) (patternEdgeCount [[],[],[],[],[],[2,3]]) [] := certificate_1046_checked

theorem certificate_1047_checked : certificate_1047.Valid 14 8 14 certificate_1047_q certificate_1047_edges 6 2 [] := by decide +kernel
theorem certificate_1047_valid : certificate_1047.Valid 14 8 (patternOrder [[],[],[],[],[],[2,4]]) (patternClique [[],[],[],[],[],[2,4]]) (patternEdges [[],[],[],[],[],[2,4]]) (patternAmount [[],[],[],[],[],[2,4]]) (patternEdgeCount [[],[],[],[],[],[2,4]]) [] := certificate_1047_checked

theorem certificate_1048_checked : certificate_1048.Valid 14 8 14 certificate_1048_q certificate_1048_edges 6 2 [] := by decide +kernel
theorem certificate_1048_valid : certificate_1048.Valid 14 8 (patternOrder [[],[],[],[],[],[3,3]]) (patternClique [[],[],[],[],[],[3,3]]) (patternEdges [[],[],[],[],[],[3,3]]) (patternAmount [[],[],[],[],[],[3,3]]) (patternEdgeCount [[],[],[],[],[],[3,3]]) [] := certificate_1048_checked

theorem certificate_1049_checked : certificate_1049.Valid 14 8 10 certificate_1049_q certificate_1049_edges 2 2 [] := by decide +kernel
theorem certificate_1049_valid : certificate_1049.Valid 14 8 (patternOrder [[],[],[],[],[1],[1]]) (patternClique [[],[],[],[],[1],[1]]) (patternEdges [[],[],[],[],[1],[1]]) (patternAmount [[],[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[],[1],[1]]) [] := certificate_1049_checked

theorem certificate_1050_checked : certificate_1050.Valid 14 8 11 certificate_1050_q certificate_1050_edges 3 2 [] := by decide +kernel
theorem certificate_1050_valid : certificate_1050.Valid 14 8 (patternOrder [[],[],[],[],[1],[2]]) (patternClique [[],[],[],[],[1],[2]]) (patternEdges [[],[],[],[],[1],[2]]) (patternAmount [[],[],[],[],[1],[2]]) (patternEdgeCount [[],[],[],[],[1],[2]]) [] := certificate_1050_checked

theorem certificate_1051_checked : certificate_1051.Valid 14 8 12 certificate_1051_q certificate_1051_edges 4 2 [] := by decide +kernel
theorem certificate_1051_valid : certificate_1051.Valid 14 8 (patternOrder [[],[],[],[],[1],[3]]) (patternClique [[],[],[],[],[1],[3]]) (patternEdges [[],[],[],[],[1],[3]]) (patternAmount [[],[],[],[],[1],[3]]) (patternEdgeCount [[],[],[],[],[1],[3]]) [] := certificate_1051_checked

theorem certificate_1052_checked : certificate_1052.Valid 14 8 13 certificate_1052_q certificate_1052_edges 5 2 [] := by decide +kernel
theorem certificate_1052_valid : certificate_1052.Valid 14 8 (patternOrder [[],[],[],[],[1],[4]]) (patternClique [[],[],[],[],[1],[4]]) (patternEdges [[],[],[],[],[1],[4]]) (patternAmount [[],[],[],[],[1],[4]]) (patternEdgeCount [[],[],[],[],[1],[4]]) [] := certificate_1052_checked

theorem certificate_1053_checked : certificate_1053.Valid 14 8 14 certificate_1053_q certificate_1053_edges 6 2 [] := by decide +kernel
theorem certificate_1053_valid : certificate_1053.Valid 14 8 (patternOrder [[],[],[],[],[1],[5]]) (patternClique [[],[],[],[],[1],[5]]) (patternEdges [[],[],[],[],[1],[5]]) (patternAmount [[],[],[],[],[1],[5]]) (patternEdgeCount [[],[],[],[],[1],[5]]) [] := certificate_1053_checked

theorem certificate_1054_checked : certificate_1054.Valid 14 8 11 certificate_1054_q certificate_1054_edges 3 3 [] := by decide +kernel
theorem certificate_1054_valid : certificate_1054.Valid 14 8 (patternOrder [[],[],[],[],[1,1,1]]) (patternClique [[],[],[],[],[1,1,1]]) (patternEdges [[],[],[],[],[1,1,1]]) (patternAmount [[],[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[],[1,1,1]]) [] := certificate_1054_checked

theorem certificate_1055_checked : certificate_1055.Valid 14 8 12 certificate_1055_q certificate_1055_edges 4 3 [] := by decide +kernel
theorem certificate_1055_valid : certificate_1055.Valid 14 8 (patternOrder [[],[],[],[],[1,1,2]]) (patternClique [[],[],[],[],[1,1,2]]) (patternEdges [[],[],[],[],[1,1,2]]) (patternAmount [[],[],[],[],[1,1,2]]) (patternEdgeCount [[],[],[],[],[1,1,2]]) [] := certificate_1055_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates034
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1056_checked : certificate_1056.Valid 14 8 13 certificate_1056_q certificate_1056_edges 5 3 [] := by decide +kernel
theorem certificate_1056_valid : certificate_1056.Valid 14 8 (patternOrder [[],[],[],[],[1,1,3]]) (patternClique [[],[],[],[],[1,1,3]]) (patternEdges [[],[],[],[],[1,1,3]]) (patternAmount [[],[],[],[],[1,1,3]]) (patternEdgeCount [[],[],[],[],[1,1,3]]) [] := certificate_1056_checked

theorem certificate_1057_checked : certificate_1057.Valid 14 8 14 certificate_1057_q certificate_1057_edges 6 3 [] := by decide +kernel
theorem certificate_1057_valid : certificate_1057.Valid 14 8 (patternOrder [[],[],[],[],[1,1,4]]) (patternClique [[],[],[],[],[1,1,4]]) (patternEdges [[],[],[],[],[1,1,4]]) (patternAmount [[],[],[],[],[1,1,4]]) (patternEdgeCount [[],[],[],[],[1,1,4]]) [] := certificate_1057_checked

theorem certificate_1058_checked : certificate_1058.Valid 14 8 12 certificate_1058_q certificate_1058_edges 4 3 [] := by decide +kernel
theorem certificate_1058_valid : certificate_1058.Valid 14 8 (patternOrder [[],[],[],[],[1,2,1]]) (patternClique [[],[],[],[],[1,2,1]]) (patternEdges [[],[],[],[],[1,2,1]]) (patternAmount [[],[],[],[],[1,2,1]]) (patternEdgeCount [[],[],[],[],[1,2,1]]) [] := certificate_1058_checked

theorem certificate_1059_checked : certificate_1059.Valid 14 8 13 certificate_1059_q certificate_1059_edges 5 3 [] := by decide +kernel
theorem certificate_1059_valid : certificate_1059.Valid 14 8 (patternOrder [[],[],[],[],[1,2,2]]) (patternClique [[],[],[],[],[1,2,2]]) (patternEdges [[],[],[],[],[1,2,2]]) (patternAmount [[],[],[],[],[1,2,2]]) (patternEdgeCount [[],[],[],[],[1,2,2]]) [] := certificate_1059_checked

theorem certificate_1060_checked : certificate_1060.Valid 14 8 14 certificate_1060_q certificate_1060_edges 6 3 [] := by decide +kernel
theorem certificate_1060_valid : certificate_1060.Valid 14 8 (patternOrder [[],[],[],[],[1,2,3]]) (patternClique [[],[],[],[],[1,2,3]]) (patternEdges [[],[],[],[],[1,2,3]]) (patternAmount [[],[],[],[],[1,2,3]]) (patternEdgeCount [[],[],[],[],[1,2,3]]) [] := certificate_1060_checked

theorem certificate_1061_checked : certificate_1061.Valid 14 8 13 certificate_1061_q certificate_1061_edges 5 3 [] := by decide +kernel
theorem certificate_1061_valid : certificate_1061.Valid 14 8 (patternOrder [[],[],[],[],[1,3,1]]) (patternClique [[],[],[],[],[1,3,1]]) (patternEdges [[],[],[],[],[1,3,1]]) (patternAmount [[],[],[],[],[1,3,1]]) (patternEdgeCount [[],[],[],[],[1,3,1]]) [] := certificate_1061_checked

theorem certificate_1062_checked : certificate_1062.Valid 14 8 14 certificate_1062_q certificate_1062_edges 6 3 [] := by decide +kernel
theorem certificate_1062_valid : certificate_1062.Valid 14 8 (patternOrder [[],[],[],[],[1,3,2]]) (patternClique [[],[],[],[],[1,3,2]]) (patternEdges [[],[],[],[],[1,3,2]]) (patternAmount [[],[],[],[],[1,3,2]]) (patternEdgeCount [[],[],[],[],[1,3,2]]) [] := certificate_1062_checked

theorem certificate_1063_checked : certificate_1063.Valid 14 8 14 certificate_1063_q certificate_1063_edges 6 3 [] := by decide +kernel
theorem certificate_1063_valid : certificate_1063.Valid 14 8 (patternOrder [[],[],[],[],[1,4,1]]) (patternClique [[],[],[],[],[1,4,1]]) (patternEdges [[],[],[],[],[1,4,1]]) (patternAmount [[],[],[],[],[1,4,1]]) (patternEdgeCount [[],[],[],[],[1,4,1]]) [] := certificate_1063_checked

theorem certificate_1064_checked : certificate_1064.Valid 14 8 12 certificate_1064_q certificate_1064_edges 4 2 [] := by decide +kernel
theorem certificate_1064_valid : certificate_1064.Valid 14 8 (patternOrder [[],[],[],[],[2],[2]]) (patternClique [[],[],[],[],[2],[2]]) (patternEdges [[],[],[],[],[2],[2]]) (patternAmount [[],[],[],[],[2],[2]]) (patternEdgeCount [[],[],[],[],[2],[2]]) [] := certificate_1064_checked

theorem certificate_1065_checked : certificate_1065.Valid 14 8 13 certificate_1065_q certificate_1065_edges 5 2 [] := by decide +kernel
theorem certificate_1065_valid : certificate_1065.Valid 14 8 (patternOrder [[],[],[],[],[2],[3]]) (patternClique [[],[],[],[],[2],[3]]) (patternEdges [[],[],[],[],[2],[3]]) (patternAmount [[],[],[],[],[2],[3]]) (patternEdgeCount [[],[],[],[],[2],[3]]) [] := certificate_1065_checked

theorem certificate_1066_checked : certificate_1066.Valid 14 8 14 certificate_1066_q certificate_1066_edges 6 2 [] := by decide +kernel
theorem certificate_1066_valid : certificate_1066.Valid 14 8 (patternOrder [[],[],[],[],[2],[4]]) (patternClique [[],[],[],[],[2],[4]]) (patternEdges [[],[],[],[],[2],[4]]) (patternAmount [[],[],[],[],[2],[4]]) (patternEdgeCount [[],[],[],[],[2],[4]]) [] := certificate_1066_checked

theorem certificate_1067_checked : certificate_1067.Valid 14 8 13 certificate_1067_q certificate_1067_edges 5 3 [] := by decide +kernel
theorem certificate_1067_valid : certificate_1067.Valid 14 8 (patternOrder [[],[],[],[],[2,1,2]]) (patternClique [[],[],[],[],[2,1,2]]) (patternEdges [[],[],[],[],[2,1,2]]) (patternAmount [[],[],[],[],[2,1,2]]) (patternEdgeCount [[],[],[],[],[2,1,2]]) [] := certificate_1067_checked

theorem certificate_1068_checked : certificate_1068.Valid 14 8 14 certificate_1068_q certificate_1068_edges 6 3 [] := by decide +kernel
theorem certificate_1068_valid : certificate_1068.Valid 14 8 (patternOrder [[],[],[],[],[2,1,3]]) (patternClique [[],[],[],[],[2,1,3]]) (patternEdges [[],[],[],[],[2,1,3]]) (patternAmount [[],[],[],[],[2,1,3]]) (patternEdgeCount [[],[],[],[],[2,1,3]]) [] := certificate_1068_checked

theorem certificate_1069_checked : certificate_1069.Valid 14 8 14 certificate_1069_q certificate_1069_edges 6 3 [] := by decide +kernel
theorem certificate_1069_valid : certificate_1069.Valid 14 8 (patternOrder [[],[],[],[],[2,2,2]]) (patternClique [[],[],[],[],[2,2,2]]) (patternEdges [[],[],[],[],[2,2,2]]) (patternAmount [[],[],[],[],[2,2,2]]) (patternEdgeCount [[],[],[],[],[2,2,2]]) [] := certificate_1069_checked

theorem certificate_1070_checked : certificate_1070.Valid 14 8 14 certificate_1070_q certificate_1070_edges 6 2 [] := by decide +kernel
theorem certificate_1070_valid : certificate_1070.Valid 14 8 (patternOrder [[],[],[],[],[3],[3]]) (patternClique [[],[],[],[],[3],[3]]) (patternEdges [[],[],[],[],[3],[3]]) (patternAmount [[],[],[],[],[3],[3]]) (patternEdgeCount [[],[],[],[],[3],[3]]) [] := certificate_1070_checked

theorem certificate_1071_checked : certificate_1071.Valid 14 8 11 certificate_1071_q certificate_1071_edges 3 3 [] := by decide +kernel
theorem certificate_1071_valid : certificate_1071.Valid 14 8 (patternOrder [[],[],[],[1],[1,1]]) (patternClique [[],[],[],[1],[1,1]]) (patternEdges [[],[],[],[1],[1,1]]) (patternAmount [[],[],[],[1],[1,1]]) (patternEdgeCount [[],[],[],[1],[1,1]]) [] := certificate_1071_checked

theorem certificate_1072_checked : certificate_1072.Valid 14 8 12 certificate_1072_q certificate_1072_edges 4 3 [] := by decide +kernel
theorem certificate_1072_valid : certificate_1072.Valid 14 8 (patternOrder [[],[],[],[1],[1,2]]) (patternClique [[],[],[],[1],[1,2]]) (patternEdges [[],[],[],[1],[1,2]]) (patternAmount [[],[],[],[1],[1,2]]) (patternEdgeCount [[],[],[],[1],[1,2]]) [] := certificate_1072_checked

theorem certificate_1073_checked : certificate_1073.Valid 14 8 13 certificate_1073_q certificate_1073_edges 5 3 [] := by decide +kernel
theorem certificate_1073_valid : certificate_1073.Valid 14 8 (patternOrder [[],[],[],[1],[1,3]]) (patternClique [[],[],[],[1],[1,3]]) (patternEdges [[],[],[],[1],[1,3]]) (patternAmount [[],[],[],[1],[1,3]]) (patternEdgeCount [[],[],[],[1],[1,3]]) [] := certificate_1073_checked

theorem certificate_1074_checked : certificate_1074.Valid 14 8 14 certificate_1074_q certificate_1074_edges 6 3 [] := by decide +kernel
theorem certificate_1074_valid : certificate_1074.Valid 14 8 (patternOrder [[],[],[],[1],[1,4]]) (patternClique [[],[],[],[1],[1,4]]) (patternEdges [[],[],[],[1],[1,4]]) (patternAmount [[],[],[],[1],[1,4]]) (patternEdgeCount [[],[],[],[1],[1,4]]) [] := certificate_1074_checked

theorem certificate_1075_checked : certificate_1075.Valid 14 8 13 certificate_1075_q certificate_1075_edges 5 3 [] := by decide +kernel
theorem certificate_1075_valid : certificate_1075.Valid 14 8 (patternOrder [[],[],[],[1],[2,2]]) (patternClique [[],[],[],[1],[2,2]]) (patternEdges [[],[],[],[1],[2,2]]) (patternAmount [[],[],[],[1],[2,2]]) (patternEdgeCount [[],[],[],[1],[2,2]]) [] := certificate_1075_checked

theorem certificate_1076_checked : certificate_1076.Valid 14 8 14 certificate_1076_q certificate_1076_edges 6 3 [] := by decide +kernel
theorem certificate_1076_valid : certificate_1076.Valid 14 8 (patternOrder [[],[],[],[1],[2,3]]) (patternClique [[],[],[],[1],[2,3]]) (patternEdges [[],[],[],[1],[2,3]]) (patternAmount [[],[],[],[1],[2,3]]) (patternEdgeCount [[],[],[],[1],[2,3]]) [] := certificate_1076_checked

theorem certificate_1077_checked : certificate_1077.Valid 14 8 12 certificate_1077_q certificate_1077_edges 4 3 [] := by decide +kernel
theorem certificate_1077_valid : certificate_1077.Valid 14 8 (patternOrder [[],[],[],[1,1],[2]]) (patternClique [[],[],[],[1,1],[2]]) (patternEdges [[],[],[],[1,1],[2]]) (patternAmount [[],[],[],[1,1],[2]]) (patternEdgeCount [[],[],[],[1,1],[2]]) [] := certificate_1077_checked

theorem certificate_1078_checked : certificate_1078.Valid 14 8 13 certificate_1078_q certificate_1078_edges 5 3 [] := by decide +kernel
theorem certificate_1078_valid : certificate_1078.Valid 14 8 (patternOrder [[],[],[],[1,1],[3]]) (patternClique [[],[],[],[1,1],[3]]) (patternEdges [[],[],[],[1,1],[3]]) (patternAmount [[],[],[],[1,1],[3]]) (patternEdgeCount [[],[],[],[1,1],[3]]) [] := certificate_1078_checked

theorem certificate_1079_checked : certificate_1079.Valid 14 8 14 certificate_1079_q certificate_1079_edges 6 3 [] := by decide +kernel
theorem certificate_1079_valid : certificate_1079.Valid 14 8 (patternOrder [[],[],[],[1,1],[4]]) (patternClique [[],[],[],[1,1],[4]]) (patternEdges [[],[],[],[1,1],[4]]) (patternAmount [[],[],[],[1,1],[4]]) (patternEdgeCount [[],[],[],[1,1],[4]]) [] := certificate_1079_checked

theorem certificate_1080_checked : certificate_1080.Valid 14 8 12 certificate_1080_q certificate_1080_edges 4 4 [] := by decide +kernel
theorem certificate_1080_valid : certificate_1080.Valid 14 8 (patternOrder [[],[],[],[1,1,1,1]]) (patternClique [[],[],[],[1,1,1,1]]) (patternEdges [[],[],[],[1,1,1,1]]) (patternAmount [[],[],[],[1,1,1,1]]) (patternEdgeCount [[],[],[],[1,1,1,1]]) [] := certificate_1080_checked

theorem certificate_1081_checked : certificate_1081.Valid 14 8 13 certificate_1081_q certificate_1081_edges 5 4 [] := by decide +kernel
theorem certificate_1081_valid : certificate_1081.Valid 14 8 (patternOrder [[],[],[],[1,1,1,2]]) (patternClique [[],[],[],[1,1,1,2]]) (patternEdges [[],[],[],[1,1,1,2]]) (patternAmount [[],[],[],[1,1,1,2]]) (patternEdgeCount [[],[],[],[1,1,1,2]]) [] := certificate_1081_checked

theorem certificate_1082_checked : certificate_1082.Valid 14 8 14 certificate_1082_q certificate_1082_edges 6 4 [] := by decide +kernel
theorem certificate_1082_valid : certificate_1082.Valid 14 8 (patternOrder [[],[],[],[1,1,1,3]]) (patternClique [[],[],[],[1,1,1,3]]) (patternEdges [[],[],[],[1,1,1,3]]) (patternAmount [[],[],[],[1,1,1,3]]) (patternEdgeCount [[],[],[],[1,1,1,3]]) [] := certificate_1082_checked

theorem certificate_1083_checked : certificate_1083.Valid 14 8 13 certificate_1083_q certificate_1083_edges 5 4 [] := by decide +kernel
theorem certificate_1083_valid : certificate_1083.Valid 14 8 (patternOrder [[],[],[],[1,1,2,1]]) (patternClique [[],[],[],[1,1,2,1]]) (patternEdges [[],[],[],[1,1,2,1]]) (patternAmount [[],[],[],[1,1,2,1]]) (patternEdgeCount [[],[],[],[1,1,2,1]]) [] := certificate_1083_checked

theorem certificate_1084_checked : certificate_1084.Valid 14 8 14 certificate_1084_q certificate_1084_edges 6 4 [] := by decide +kernel
theorem certificate_1084_valid : certificate_1084.Valid 14 8 (patternOrder [[],[],[],[1,1,2,2]]) (patternClique [[],[],[],[1,1,2,2]]) (patternEdges [[],[],[],[1,1,2,2]]) (patternAmount [[],[],[],[1,1,2,2]]) (patternEdgeCount [[],[],[],[1,1,2,2]]) [] := certificate_1084_checked

theorem certificate_1085_checked : certificate_1085.Valid 14 8 14 certificate_1085_q certificate_1085_edges 6 4 [] := by decide +kernel
theorem certificate_1085_valid : certificate_1085.Valid 14 8 (patternOrder [[],[],[],[1,1,3,1]]) (patternClique [[],[],[],[1,1,3,1]]) (patternEdges [[],[],[],[1,1,3,1]]) (patternAmount [[],[],[],[1,1,3,1]]) (patternEdgeCount [[],[],[],[1,1,3,1]]) [] := certificate_1085_checked

theorem certificate_1086_checked : certificate_1086.Valid 14 8 13 certificate_1086_q certificate_1086_edges 5 3 [] := by decide +kernel
theorem certificate_1086_valid : certificate_1086.Valid 14 8 (patternOrder [[],[],[],[1,2],[2]]) (patternClique [[],[],[],[1,2],[2]]) (patternEdges [[],[],[],[1,2],[2]]) (patternAmount [[],[],[],[1,2],[2]]) (patternEdgeCount [[],[],[],[1,2],[2]]) [] := certificate_1086_checked

theorem certificate_1087_checked : certificate_1087.Valid 14 8 14 certificate_1087_q certificate_1087_edges 6 3 [] := by decide +kernel
theorem certificate_1087_valid : certificate_1087.Valid 14 8 (patternOrder [[],[],[],[1,2],[3]]) (patternClique [[],[],[],[1,2],[3]]) (patternEdges [[],[],[],[1,2],[3]]) (patternAmount [[],[],[],[1,2],[3]]) (patternEdgeCount [[],[],[],[1,2],[3]]) [] := certificate_1087_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates035
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1088_checked : certificate_1088.Valid 14 8 14 certificate_1088_q certificate_1088_edges 6 4 [] := by decide +kernel
theorem certificate_1088_valid : certificate_1088.Valid 14 8 (patternOrder [[],[],[],[1,2,1,2]]) (patternClique [[],[],[],[1,2,1,2]]) (patternEdges [[],[],[],[1,2,1,2]]) (patternAmount [[],[],[],[1,2,1,2]]) (patternEdgeCount [[],[],[],[1,2,1,2]]) [] := certificate_1088_checked

theorem certificate_1089_checked : certificate_1089.Valid 14 8 14 certificate_1089_q certificate_1089_edges 6 4 [] := by decide +kernel
theorem certificate_1089_valid : certificate_1089.Valid 14 8 (patternOrder [[],[],[],[1,2,2,1]]) (patternClique [[],[],[],[1,2,2,1]]) (patternEdges [[],[],[],[1,2,2,1]]) (patternAmount [[],[],[],[1,2,2,1]]) (patternEdgeCount [[],[],[],[1,2,2,1]]) [] := certificate_1089_checked

theorem certificate_1090_checked : certificate_1090.Valid 14 8 14 certificate_1090_q certificate_1090_edges 6 3 [] := by decide +kernel
theorem certificate_1090_valid : certificate_1090.Valid 14 8 (patternOrder [[],[],[],[1,3],[2]]) (patternClique [[],[],[],[1,3],[2]]) (patternEdges [[],[],[],[1,3],[2]]) (patternAmount [[],[],[],[1,3],[2]]) (patternEdgeCount [[],[],[],[1,3],[2]]) [] := certificate_1090_checked

theorem certificate_1091_checked : certificate_1091.Valid 14 8 14 certificate_1091_q certificate_1091_edges 6 3 [] := by decide +kernel
theorem certificate_1091_valid : certificate_1091.Valid 14 8 (patternOrder [[],[],[],[2],[2,2]]) (patternClique [[],[],[],[2],[2,2]]) (patternEdges [[],[],[],[2],[2,2]]) (patternAmount [[],[],[],[2],[2,2]]) (patternEdgeCount [[],[],[],[2],[2,2]]) [] := certificate_1091_checked

theorem certificate_1092_checked : certificate_1092.Valid 14 8 14 certificate_1092_q certificate_1092_edges 6 4 [] := by decide +kernel
theorem certificate_1092_valid : certificate_1092.Valid 14 8 (patternOrder [[],[],[],[2,1,1,2]]) (patternClique [[],[],[],[2,1,1,2]]) (patternEdges [[],[],[],[2,1,1,2]]) (patternAmount [[],[],[],[2,1,1,2]]) (patternEdgeCount [[],[],[],[2,1,1,2]]) [] := certificate_1092_checked

theorem certificate_1093_checked : certificate_1093.Valid 14 8 11 certificate_1093_q certificate_1093_edges 3 3 [] := by decide +kernel
theorem certificate_1093_valid : certificate_1093.Valid 14 8 (patternOrder [[],[],[1],[1],[1]]) (patternClique [[],[],[1],[1],[1]]) (patternEdges [[],[],[1],[1],[1]]) (patternAmount [[],[],[1],[1],[1]]) (patternEdgeCount [[],[],[1],[1],[1]]) [] := certificate_1093_checked

theorem certificate_1094_checked : certificate_1094.Valid 14 8 12 certificate_1094_q certificate_1094_edges 4 3 [] := by decide +kernel
theorem certificate_1094_valid : certificate_1094.Valid 14 8 (patternOrder [[],[],[1],[1],[2]]) (patternClique [[],[],[1],[1],[2]]) (patternEdges [[],[],[1],[1],[2]]) (patternAmount [[],[],[1],[1],[2]]) (patternEdgeCount [[],[],[1],[1],[2]]) [] := certificate_1094_checked

theorem certificate_1095_checked : certificate_1095.Valid 14 8 13 certificate_1095_q certificate_1095_edges 5 3 [] := by decide +kernel
theorem certificate_1095_valid : certificate_1095.Valid 14 8 (patternOrder [[],[],[1],[1],[3]]) (patternClique [[],[],[1],[1],[3]]) (patternEdges [[],[],[1],[1],[3]]) (patternAmount [[],[],[1],[1],[3]]) (patternEdgeCount [[],[],[1],[1],[3]]) [] := certificate_1095_checked

theorem certificate_1096_checked : certificate_1096.Valid 14 8 14 certificate_1096_q certificate_1096_edges 6 3 [] := by decide +kernel
theorem certificate_1096_valid : certificate_1096.Valid 14 8 (patternOrder [[],[],[1],[1],[4]]) (patternClique [[],[],[1],[1],[4]]) (patternEdges [[],[],[1],[1],[4]]) (patternAmount [[],[],[1],[1],[4]]) (patternEdgeCount [[],[],[1],[1],[4]]) [] := certificate_1096_checked

theorem certificate_1097_checked : certificate_1097.Valid 14 8 12 certificate_1097_q certificate_1097_edges 4 4 [] := by decide +kernel
theorem certificate_1097_valid : certificate_1097.Valid 14 8 (patternOrder [[],[],[1],[1,1,1]]) (patternClique [[],[],[1],[1,1,1]]) (patternEdges [[],[],[1],[1,1,1]]) (patternAmount [[],[],[1],[1,1,1]]) (patternEdgeCount [[],[],[1],[1,1,1]]) [] := certificate_1097_checked

theorem certificate_1098_checked : certificate_1098.Valid 14 8 13 certificate_1098_q certificate_1098_edges 5 4 [] := by decide +kernel
theorem certificate_1098_valid : certificate_1098.Valid 14 8 (patternOrder [[],[],[1],[1,1,2]]) (patternClique [[],[],[1],[1,1,2]]) (patternEdges [[],[],[1],[1,1,2]]) (patternAmount [[],[],[1],[1,1,2]]) (patternEdgeCount [[],[],[1],[1,1,2]]) [] := certificate_1098_checked

theorem certificate_1099_checked : certificate_1099.Valid 14 8 14 certificate_1099_q certificate_1099_edges 6 4 [] := by decide +kernel
theorem certificate_1099_valid : certificate_1099.Valid 14 8 (patternOrder [[],[],[1],[1,1,3]]) (patternClique [[],[],[1],[1,1,3]]) (patternEdges [[],[],[1],[1,1,3]]) (patternAmount [[],[],[1],[1,1,3]]) (patternEdgeCount [[],[],[1],[1,1,3]]) [] := certificate_1099_checked

theorem certificate_1100_checked : certificate_1100.Valid 14 8 13 certificate_1100_q certificate_1100_edges 5 4 [] := by decide +kernel
theorem certificate_1100_valid : certificate_1100.Valid 14 8 (patternOrder [[],[],[1],[1,2,1]]) (patternClique [[],[],[1],[1,2,1]]) (patternEdges [[],[],[1],[1,2,1]]) (patternAmount [[],[],[1],[1,2,1]]) (patternEdgeCount [[],[],[1],[1,2,1]]) [] := certificate_1100_checked

theorem certificate_1101_checked : certificate_1101.Valid 14 8 14 certificate_1101_q certificate_1101_edges 6 4 [] := by decide +kernel
theorem certificate_1101_valid : certificate_1101.Valid 14 8 (patternOrder [[],[],[1],[1,2,2]]) (patternClique [[],[],[1],[1,2,2]]) (patternEdges [[],[],[1],[1,2,2]]) (patternAmount [[],[],[1],[1,2,2]]) (patternEdgeCount [[],[],[1],[1,2,2]]) [] := certificate_1101_checked

theorem certificate_1102_checked : certificate_1102.Valid 14 8 14 certificate_1102_q certificate_1102_edges 6 4 [] := by decide +kernel
theorem certificate_1102_valid : certificate_1102.Valid 14 8 (patternOrder [[],[],[1],[1,3,1]]) (patternClique [[],[],[1],[1,3,1]]) (patternEdges [[],[],[1],[1,3,1]]) (patternAmount [[],[],[1],[1,3,1]]) (patternEdgeCount [[],[],[1],[1,3,1]]) [] := certificate_1102_checked

theorem certificate_1103_checked : certificate_1103.Valid 14 8 13 certificate_1103_q certificate_1103_edges 5 3 [] := by decide +kernel
theorem certificate_1103_valid : certificate_1103.Valid 14 8 (patternOrder [[],[],[1],[2],[2]]) (patternClique [[],[],[1],[2],[2]]) (patternEdges [[],[],[1],[2],[2]]) (patternAmount [[],[],[1],[2],[2]]) (patternEdgeCount [[],[],[1],[2],[2]]) [] := certificate_1103_checked

theorem certificate_1104_checked : certificate_1104.Valid 14 8 14 certificate_1104_q certificate_1104_edges 6 3 [] := by decide +kernel
theorem certificate_1104_valid : certificate_1104.Valid 14 8 (patternOrder [[],[],[1],[2],[3]]) (patternClique [[],[],[1],[2],[3]]) (patternEdges [[],[],[1],[2],[3]]) (patternAmount [[],[],[1],[2],[3]]) (patternEdgeCount [[],[],[1],[2],[3]]) [] := certificate_1104_checked

theorem certificate_1105_checked : certificate_1105.Valid 14 8 14 certificate_1105_q certificate_1105_edges 6 4 [] := by decide +kernel
theorem certificate_1105_valid : certificate_1105.Valid 14 8 (patternOrder [[],[],[1],[2,1,2]]) (patternClique [[],[],[1],[2,1,2]]) (patternEdges [[],[],[1],[2,1,2]]) (patternAmount [[],[],[1],[2,1,2]]) (patternEdgeCount [[],[],[1],[2,1,2]]) [] := certificate_1105_checked

theorem certificate_1106_checked : certificate_1106.Valid 14 8 12 certificate_1106_q certificate_1106_edges 4 4 [] := by decide +kernel
theorem certificate_1106_valid : certificate_1106.Valid 14 8 (patternOrder [[],[],[1,1],[1,1]]) (patternClique [[],[],[1,1],[1,1]]) (patternEdges [[],[],[1,1],[1,1]]) (patternAmount [[],[],[1,1],[1,1]]) (patternEdgeCount [[],[],[1,1],[1,1]]) [] := certificate_1106_checked

theorem certificate_1107_checked : certificate_1107.Valid 14 8 13 certificate_1107_q certificate_1107_edges 5 4 [] := by decide +kernel
theorem certificate_1107_valid : certificate_1107.Valid 14 8 (patternOrder [[],[],[1,1],[1,2]]) (patternClique [[],[],[1,1],[1,2]]) (patternEdges [[],[],[1,1],[1,2]]) (patternAmount [[],[],[1,1],[1,2]]) (patternEdgeCount [[],[],[1,1],[1,2]]) [] := certificate_1107_checked

theorem certificate_1108_checked : certificate_1108.Valid 14 8 14 certificate_1108_q certificate_1108_edges 6 4 [] := by decide +kernel
theorem certificate_1108_valid : certificate_1108.Valid 14 8 (patternOrder [[],[],[1,1],[1,3]]) (patternClique [[],[],[1,1],[1,3]]) (patternEdges [[],[],[1,1],[1,3]]) (patternAmount [[],[],[1,1],[1,3]]) (patternEdgeCount [[],[],[1,1],[1,3]]) [] := certificate_1108_checked

theorem certificate_1109_checked : certificate_1109.Valid 14 8 14 certificate_1109_q certificate_1109_edges 6 4 [] := by decide +kernel
theorem certificate_1109_valid : certificate_1109.Valid 14 8 (patternOrder [[],[],[1,1],[2,2]]) (patternClique [[],[],[1,1],[2,2]]) (patternEdges [[],[],[1,1],[2,2]]) (patternAmount [[],[],[1,1],[2,2]]) (patternEdgeCount [[],[],[1,1],[2,2]]) [] := certificate_1109_checked

theorem certificate_1110_checked : certificate_1110.Valid 14 8 13 certificate_1110_q certificate_1110_edges 5 4 [] := by decide +kernel
theorem certificate_1110_valid : certificate_1110.Valid 14 8 (patternOrder [[],[],[1,1,1],[2]]) (patternClique [[],[],[1,1,1],[2]]) (patternEdges [[],[],[1,1,1],[2]]) (patternAmount [[],[],[1,1,1],[2]]) (patternEdgeCount [[],[],[1,1,1],[2]]) [] := certificate_1110_checked

theorem certificate_1111_checked : certificate_1111.Valid 14 8 14 certificate_1111_q certificate_1111_edges 6 4 [] := by decide +kernel
theorem certificate_1111_valid : certificate_1111.Valid 14 8 (patternOrder [[],[],[1,1,1],[3]]) (patternClique [[],[],[1,1,1],[3]]) (patternEdges [[],[],[1,1,1],[3]]) (patternAmount [[],[],[1,1,1],[3]]) (patternEdgeCount [[],[],[1,1,1],[3]]) [] := certificate_1111_checked

theorem certificate_1112_checked : certificate_1112.Valid 14 8 13 certificate_1112_q certificate_1112_edges 5 5 [] := by decide +kernel
theorem certificate_1112_valid : certificate_1112.Valid 14 8 (patternOrder [[],[],[1,1,1,1,1]]) (patternClique [[],[],[1,1,1,1,1]]) (patternEdges [[],[],[1,1,1,1,1]]) (patternAmount [[],[],[1,1,1,1,1]]) (patternEdgeCount [[],[],[1,1,1,1,1]]) [] := certificate_1112_checked

theorem certificate_1113_checked : certificate_1113.Valid 14 8 14 certificate_1113_q certificate_1113_edges 6 5 [] := by decide +kernel
theorem certificate_1113_valid : certificate_1113.Valid 14 8 (patternOrder [[],[],[1,1,1,1,2]]) (patternClique [[],[],[1,1,1,1,2]]) (patternEdges [[],[],[1,1,1,1,2]]) (patternAmount [[],[],[1,1,1,1,2]]) (patternEdgeCount [[],[],[1,1,1,1,2]]) [] := certificate_1113_checked

theorem certificate_1114_checked : certificate_1114.Valid 14 8 14 certificate_1114_q certificate_1114_edges 6 5 [] := by decide +kernel
theorem certificate_1114_valid : certificate_1114.Valid 14 8 (patternOrder [[],[],[1,1,1,2,1]]) (patternClique [[],[],[1,1,1,2,1]]) (patternEdges [[],[],[1,1,1,2,1]]) (patternAmount [[],[],[1,1,1,2,1]]) (patternEdgeCount [[],[],[1,1,1,2,1]]) [] := certificate_1114_checked

theorem certificate_1115_checked : certificate_1115.Valid 14 8 14 certificate_1115_q certificate_1115_edges 6 4 [] := by decide +kernel
theorem certificate_1115_valid : certificate_1115.Valid 14 8 (patternOrder [[],[],[1,1,2],[2]]) (patternClique [[],[],[1,1,2],[2]]) (patternEdges [[],[],[1,1,2],[2]]) (patternAmount [[],[],[1,1,2],[2]]) (patternEdgeCount [[],[],[1,1,2],[2]]) [] := certificate_1115_checked

theorem certificate_1116_checked : certificate_1116.Valid 14 8 14 certificate_1116_q certificate_1116_edges 6 5 [] := by decide +kernel
theorem certificate_1116_valid : certificate_1116.Valid 14 8 (patternOrder [[],[],[1,1,2,1,1]]) (patternClique [[],[],[1,1,2,1,1]]) (patternEdges [[],[],[1,1,2,1,1]]) (patternAmount [[],[],[1,1,2,1,1]]) (patternEdgeCount [[],[],[1,1,2,1,1]]) [] := certificate_1116_checked

theorem certificate_1117_checked : certificate_1117.Valid 14 8 14 certificate_1117_q certificate_1117_edges 6 4 [] := by decide +kernel
theorem certificate_1117_valid : certificate_1117.Valid 14 8 (patternOrder [[],[],[1,2],[1,2]]) (patternClique [[],[],[1,2],[1,2]]) (patternEdges [[],[],[1,2],[1,2]]) (patternAmount [[],[],[1,2],[1,2]]) (patternEdgeCount [[],[],[1,2],[1,2]]) [] := certificate_1117_checked

theorem certificate_1118_checked : certificate_1118.Valid 14 8 14 certificate_1118_q certificate_1118_edges 6 4 [] := by decide +kernel
theorem certificate_1118_valid : certificate_1118.Valid 14 8 (patternOrder [[],[],[1,2,1],[2]]) (patternClique [[],[],[1,2,1],[2]]) (patternEdges [[],[],[1,2,1],[2]]) (patternAmount [[],[],[1,2,1],[2]]) (patternEdgeCount [[],[],[1,2,1],[2]]) [] := certificate_1118_checked

theorem certificate_1119_checked : certificate_1119.Valid 14 8 14 certificate_1119_q certificate_1119_edges 6 3 [] := by decide +kernel
theorem certificate_1119_valid : certificate_1119.Valid 14 8 (patternOrder [[],[],[2],[2],[2]]) (patternClique [[],[],[2],[2],[2]]) (patternEdges [[],[],[2],[2],[2]]) (patternAmount [[],[],[2],[2],[2]]) (patternEdgeCount [[],[],[2],[2],[2]]) [] := certificate_1119_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates036
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1120_checked : certificate_1120.Valid 14 8 12 certificate_1120_q certificate_1120_edges 4 4 [] := by decide +kernel
theorem certificate_1120_valid : certificate_1120.Valid 14 8 (patternOrder [[],[1],[1],[1,1]]) (patternClique [[],[1],[1],[1,1]]) (patternEdges [[],[1],[1],[1,1]]) (patternAmount [[],[1],[1],[1,1]]) (patternEdgeCount [[],[1],[1],[1,1]]) [] := certificate_1120_checked

theorem certificate_1121_checked : certificate_1121.Valid 14 8 13 certificate_1121_q certificate_1121_edges 5 4 [] := by decide +kernel
theorem certificate_1121_valid : certificate_1121.Valid 14 8 (patternOrder [[],[1],[1],[1,2]]) (patternClique [[],[1],[1],[1,2]]) (patternEdges [[],[1],[1],[1,2]]) (patternAmount [[],[1],[1],[1,2]]) (patternEdgeCount [[],[1],[1],[1,2]]) [] := certificate_1121_checked

theorem certificate_1122_checked : certificate_1122.Valid 14 8 14 certificate_1122_q certificate_1122_edges 6 4 [] := by decide +kernel
theorem certificate_1122_valid : certificate_1122.Valid 14 8 (patternOrder [[],[1],[1],[1,3]]) (patternClique [[],[1],[1],[1,3]]) (patternEdges [[],[1],[1],[1,3]]) (patternAmount [[],[1],[1],[1,3]]) (patternEdgeCount [[],[1],[1],[1,3]]) [] := certificate_1122_checked

theorem certificate_1123_checked : certificate_1123.Valid 14 8 14 certificate_1123_q certificate_1123_edges 6 4 [] := by decide +kernel
theorem certificate_1123_valid : certificate_1123.Valid 14 8 (patternOrder [[],[1],[1],[2,2]]) (patternClique [[],[1],[1],[2,2]]) (patternEdges [[],[1],[1],[2,2]]) (patternAmount [[],[1],[1],[2,2]]) (patternEdgeCount [[],[1],[1],[2,2]]) [] := certificate_1123_checked

theorem certificate_1124_checked : certificate_1124.Valid 14 8 13 certificate_1124_q certificate_1124_edges 5 4 [] := by decide +kernel
theorem certificate_1124_valid : certificate_1124.Valid 14 8 (patternOrder [[],[1],[1,1],[2]]) (patternClique [[],[1],[1,1],[2]]) (patternEdges [[],[1],[1,1],[2]]) (patternAmount [[],[1],[1,1],[2]]) (patternEdgeCount [[],[1],[1,1],[2]]) [] := certificate_1124_checked

theorem certificate_1125_checked : certificate_1125.Valid 14 8 14 certificate_1125_q certificate_1125_edges 6 4 [] := by decide +kernel
theorem certificate_1125_valid : certificate_1125.Valid 14 8 (patternOrder [[],[1],[1,1],[3]]) (patternClique [[],[1],[1,1],[3]]) (patternEdges [[],[1],[1,1],[3]]) (patternAmount [[],[1],[1,1],[3]]) (patternEdgeCount [[],[1],[1,1],[3]]) [] := certificate_1125_checked

theorem certificate_1126_checked : certificate_1126.Valid 14 8 13 certificate_1126_q certificate_1126_edges 5 5 [] := by decide +kernel
theorem certificate_1126_valid : certificate_1126.Valid 14 8 (patternOrder [[],[1],[1,1,1,1]]) (patternClique [[],[1],[1,1,1,1]]) (patternEdges [[],[1],[1,1,1,1]]) (patternAmount [[],[1],[1,1,1,1]]) (patternEdgeCount [[],[1],[1,1,1,1]]) [] := certificate_1126_checked

theorem certificate_1127_checked : certificate_1127.Valid 14 8 14 certificate_1127_q certificate_1127_edges 6 5 [] := by decide +kernel
theorem certificate_1127_valid : certificate_1127.Valid 14 8 (patternOrder [[],[1],[1,1,1,2]]) (patternClique [[],[1],[1,1,1,2]]) (patternEdges [[],[1],[1,1,1,2]]) (patternAmount [[],[1],[1,1,1,2]]) (patternEdgeCount [[],[1],[1,1,1,2]]) [] := certificate_1127_checked

theorem certificate_1128_checked : certificate_1128.Valid 14 8 14 certificate_1128_q certificate_1128_edges 6 5 [] := by decide +kernel
theorem certificate_1128_valid : certificate_1128.Valid 14 8 (patternOrder [[],[1],[1,1,2,1]]) (patternClique [[],[1],[1,1,2,1]]) (patternEdges [[],[1],[1,1,2,1]]) (patternAmount [[],[1],[1,1,2,1]]) (patternEdgeCount [[],[1],[1,1,2,1]]) [] := certificate_1128_checked

theorem certificate_1129_checked : certificate_1129.Valid 14 8 14 certificate_1129_q certificate_1129_edges 6 4 [] := by decide +kernel
theorem certificate_1129_valid : certificate_1129.Valid 14 8 (patternOrder [[],[1],[1,2],[2]]) (patternClique [[],[1],[1,2],[2]]) (patternEdges [[],[1],[1,2],[2]]) (patternAmount [[],[1],[1,2],[2]]) (patternEdgeCount [[],[1],[1,2],[2]]) [] := certificate_1129_checked

theorem certificate_1130_checked : certificate_1130.Valid 14 8 13 certificate_1130_q certificate_1130_edges 5 5 [] := by decide +kernel
theorem certificate_1130_valid : certificate_1130.Valid 14 8 (patternOrder [[],[1,1],[1,1,1]]) (patternClique [[],[1,1],[1,1,1]]) (patternEdges [[],[1,1],[1,1,1]]) (patternAmount [[],[1,1],[1,1,1]]) (patternEdgeCount [[],[1,1],[1,1,1]]) [] := certificate_1130_checked

theorem certificate_1131_checked : certificate_1131.Valid 14 8 14 certificate_1131_q certificate_1131_edges 6 5 [] := by decide +kernel
theorem certificate_1131_valid : certificate_1131.Valid 14 8 (patternOrder [[],[1,1],[1,1,2]]) (patternClique [[],[1,1],[1,1,2]]) (patternEdges [[],[1,1],[1,1,2]]) (patternAmount [[],[1,1],[1,1,2]]) (patternEdgeCount [[],[1,1],[1,1,2]]) [] := certificate_1131_checked

theorem certificate_1132_checked : certificate_1132.Valid 14 8 14 certificate_1132_q certificate_1132_edges 6 5 [] := by decide +kernel
theorem certificate_1132_valid : certificate_1132.Valid 14 8 (patternOrder [[],[1,1],[1,2,1]]) (patternClique [[],[1,1],[1,2,1]]) (patternEdges [[],[1,1],[1,2,1]]) (patternAmount [[],[1,1],[1,2,1]]) (patternEdgeCount [[],[1,1],[1,2,1]]) [] := certificate_1132_checked

theorem certificate_1133_checked : certificate_1133.Valid 14 8 14 certificate_1133_q certificate_1133_edges 6 4 [] := by decide +kernel
theorem certificate_1133_valid : certificate_1133.Valid 14 8 (patternOrder [[],[1,1],[2],[2]]) (patternClique [[],[1,1],[2],[2]]) (patternEdges [[],[1,1],[2],[2]]) (patternAmount [[],[1,1],[2],[2]]) (patternEdgeCount [[],[1,1],[2],[2]]) [] := certificate_1133_checked

theorem certificate_1134_checked : certificate_1134.Valid 14 8 14 certificate_1134_q certificate_1134_edges 6 5 [] := by decide +kernel
theorem certificate_1134_valid : certificate_1134.Valid 14 8 (patternOrder [[],[1,1,1],[1,2]]) (patternClique [[],[1,1,1],[1,2]]) (patternEdges [[],[1,1,1],[1,2]]) (patternAmount [[],[1,1,1],[1,2]]) (patternEdgeCount [[],[1,1,1],[1,2]]) [] := certificate_1134_checked

theorem certificate_1135_checked : certificate_1135.Valid 14 8 14 certificate_1135_q certificate_1135_edges 6 5 [] := by decide +kernel
theorem certificate_1135_valid : certificate_1135.Valid 14 8 (patternOrder [[],[1,1,1,1],[2]]) (patternClique [[],[1,1,1,1],[2]]) (patternEdges [[],[1,1,1,1],[2]]) (patternAmount [[],[1,1,1,1],[2]]) (patternEdgeCount [[],[1,1,1,1],[2]]) [] := certificate_1135_checked

theorem certificate_1136_checked : certificate_1136.Valid 14 8 14 certificate_1136_q certificate_1136_edges 6 6 [] := by decide +kernel
theorem certificate_1136_valid : certificate_1136.Valid 14 8 (patternOrder [[],[1,1,1,1,1,1]]) (patternClique [[],[1,1,1,1,1,1]]) (patternEdges [[],[1,1,1,1,1,1]]) (patternAmount [[],[1,1,1,1,1,1]]) (patternEdgeCount [[],[1,1,1,1,1,1]]) [] := certificate_1136_checked

theorem certificate_1137_checked : certificate_1137.Valid 14 8 12 certificate_1137_q certificate_1137_edges 4 4 [] := by decide +kernel
theorem certificate_1137_valid : certificate_1137.Valid 14 8 (patternOrder [[1],[1],[1],[1]]) (patternClique [[1],[1],[1],[1]]) (patternEdges [[1],[1],[1],[1]]) (patternAmount [[1],[1],[1],[1]]) (patternEdgeCount [[1],[1],[1],[1]]) [] := certificate_1137_checked

theorem certificate_1138_checked : certificate_1138.Valid 14 8 13 certificate_1138_q certificate_1138_edges 5 4 [] := by decide +kernel
theorem certificate_1138_valid : certificate_1138.Valid 14 8 (patternOrder [[1],[1],[1],[2]]) (patternClique [[1],[1],[1],[2]]) (patternEdges [[1],[1],[1],[2]]) (patternAmount [[1],[1],[1],[2]]) (patternEdgeCount [[1],[1],[1],[2]]) [] := certificate_1138_checked

theorem certificate_1139_checked : certificate_1139.Valid 14 8 14 certificate_1139_q certificate_1139_edges 6 4 [] := by decide +kernel
theorem certificate_1139_valid : certificate_1139.Valid 14 8 (patternOrder [[1],[1],[1],[3]]) (patternClique [[1],[1],[1],[3]]) (patternEdges [[1],[1],[1],[3]]) (patternAmount [[1],[1],[1],[3]]) (patternEdgeCount [[1],[1],[1],[3]]) [] := certificate_1139_checked

theorem certificate_1140_checked : certificate_1140.Valid 14 8 13 certificate_1140_q certificate_1140_edges 5 5 [] := by decide +kernel
theorem certificate_1140_valid : certificate_1140.Valid 14 8 (patternOrder [[1],[1],[1,1,1]]) (patternClique [[1],[1],[1,1,1]]) (patternEdges [[1],[1],[1,1,1]]) (patternAmount [[1],[1],[1,1,1]]) (patternEdgeCount [[1],[1],[1,1,1]]) [] := certificate_1140_checked

theorem certificate_1141_checked : certificate_1141.Valid 14 8 14 certificate_1141_q certificate_1141_edges 6 5 [] := by decide +kernel
theorem certificate_1141_valid : certificate_1141.Valid 14 8 (patternOrder [[1],[1],[1,1,2]]) (patternClique [[1],[1],[1,1,2]]) (patternEdges [[1],[1],[1,1,2]]) (patternAmount [[1],[1],[1,1,2]]) (patternEdgeCount [[1],[1],[1,1,2]]) [] := certificate_1141_checked

theorem certificate_1142_checked : certificate_1142.Valid 14 8 14 certificate_1142_q certificate_1142_edges 6 5 [] := by decide +kernel
theorem certificate_1142_valid : certificate_1142.Valid 14 8 (patternOrder [[1],[1],[1,2,1]]) (patternClique [[1],[1],[1,2,1]]) (patternEdges [[1],[1],[1,2,1]]) (patternAmount [[1],[1],[1,2,1]]) (patternEdgeCount [[1],[1],[1,2,1]]) [] := certificate_1142_checked

theorem certificate_1143_checked : certificate_1143.Valid 14 8 14 certificate_1143_q certificate_1143_edges 6 4 [] := by decide +kernel
theorem certificate_1143_valid : certificate_1143.Valid 14 8 (patternOrder [[1],[1],[2],[2]]) (patternClique [[1],[1],[2],[2]]) (patternEdges [[1],[1],[2],[2]]) (patternAmount [[1],[1],[2],[2]]) (patternEdgeCount [[1],[1],[2],[2]]) [] := certificate_1143_checked

theorem certificate_1144_checked : certificate_1144.Valid 14 8 13 certificate_1144_q certificate_1144_edges 5 5 [] := by decide +kernel
theorem certificate_1144_valid : certificate_1144.Valid 14 8 (patternOrder [[1],[1,1],[1,1]]) (patternClique [[1],[1,1],[1,1]]) (patternEdges [[1],[1,1],[1,1]]) (patternAmount [[1],[1,1],[1,1]]) (patternEdgeCount [[1],[1,1],[1,1]]) [] := certificate_1144_checked

theorem certificate_1145_checked : certificate_1145.Valid 14 8 14 certificate_1145_q certificate_1145_edges 6 5 [] := by decide +kernel
theorem certificate_1145_valid : certificate_1145.Valid 14 8 (patternOrder [[1],[1,1],[1,2]]) (patternClique [[1],[1,1],[1,2]]) (patternEdges [[1],[1,1],[1,2]]) (patternAmount [[1],[1,1],[1,2]]) (patternEdgeCount [[1],[1,1],[1,2]]) [] := certificate_1145_checked

theorem certificate_1146_checked : certificate_1146.Valid 14 8 14 certificate_1146_q certificate_1146_edges 6 5 [] := by decide +kernel
theorem certificate_1146_valid : certificate_1146.Valid 14 8 (patternOrder [[1],[1,1,1],[2]]) (patternClique [[1],[1,1,1],[2]]) (patternEdges [[1],[1,1,1],[2]]) (patternAmount [[1],[1,1,1],[2]]) (patternEdgeCount [[1],[1,1,1],[2]]) [] := certificate_1146_checked

theorem certificate_1147_checked : certificate_1147.Valid 14 8 14 certificate_1147_q certificate_1147_edges 6 6 [] := by decide +kernel
theorem certificate_1147_valid : certificate_1147.Valid 14 8 (patternOrder [[1],[1,1,1,1,1]]) (patternClique [[1],[1,1,1,1,1]]) (patternEdges [[1],[1,1,1,1,1]]) (patternAmount [[1],[1,1,1,1,1]]) (patternEdgeCount [[1],[1,1,1,1,1]]) [] := certificate_1147_checked

theorem certificate_1148_checked : certificate_1148.Valid 14 8 14 certificate_1148_q certificate_1148_edges 6 5 [] := by decide +kernel
theorem certificate_1148_valid : certificate_1148.Valid 14 8 (patternOrder [[1,1],[1,1],[2]]) (patternClique [[1,1],[1,1],[2]]) (patternEdges [[1,1],[1,1],[2]]) (patternAmount [[1,1],[1,1],[2]]) (patternEdgeCount [[1,1],[1,1],[2]]) [] := certificate_1148_checked

theorem certificate_1149_checked : certificate_1149.Valid 14 8 14 certificate_1149_q certificate_1149_edges 6 6 [] := by decide +kernel
theorem certificate_1149_valid : certificate_1149.Valid 14 8 (patternOrder [[1,1],[1,1,1,1]]) (patternClique [[1,1],[1,1,1,1]]) (patternEdges [[1,1],[1,1,1,1]]) (patternAmount [[1,1],[1,1,1,1]]) (patternEdgeCount [[1,1],[1,1,1,1]]) [] := certificate_1149_checked

theorem certificate_1150_checked : certificate_1150.Valid 14 8 14 certificate_1150_q certificate_1150_edges 6 6 [] := by decide +kernel
theorem certificate_1150_valid : certificate_1150.Valid 14 8 (patternOrder [[1,1,1],[1,1,1]]) (patternClique [[1,1,1],[1,1,1]]) (patternEdges [[1,1,1],[1,1,1]]) (patternAmount [[1,1,1],[1,1,1]]) (patternEdgeCount [[1,1,1],[1,1,1]]) [] := certificate_1150_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns14x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_14_8_0_verified : ∀ D ∈ patterns_14_8_0, PatternVerified 14 8 D := by

  simp only [patterns_14_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_1033, certificate_1033_valid⟩, ⟨⟨certificate_1034, certificate_1034_valid⟩, ⟨⟨certificate_1035, certificate_1035_valid⟩, ⟨⟨certificate_1036, certificate_1036_valid⟩, ⟨⟨certificate_1037, certificate_1037_valid⟩, ⟨⟨certificate_1038, certificate_1038_valid⟩, ⟨⟨certificate_1039, certificate_1039_valid⟩, ⟨⟨certificate_1040, certificate_1040_valid⟩, ⟨⟨certificate_1041, certificate_1041_valid⟩, ⟨⟨certificate_1042, certificate_1042_valid⟩, ⟨⟨certificate_1043, certificate_1043_valid⟩, ⟨⟨certificate_1044, certificate_1044_valid⟩, ⟨⟨certificate_1045, certificate_1045_valid⟩, ⟨⟨certificate_1046, certificate_1046_valid⟩, ⟨⟨certificate_1047, certificate_1047_valid⟩, ⟨⟨certificate_1048, certificate_1048_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_8_1_verified : ∀ D ∈ patterns_14_8_1, PatternVerified 14 8 D := by

  simp only [patterns_14_8_1, List.forall_mem_cons]

  exact ⟨⟨certificate_1049, certificate_1049_valid⟩, ⟨⟨certificate_1050, certificate_1050_valid⟩, ⟨⟨certificate_1051, certificate_1051_valid⟩, ⟨⟨certificate_1052, certificate_1052_valid⟩, ⟨⟨certificate_1053, certificate_1053_valid⟩, ⟨⟨certificate_1054, certificate_1054_valid⟩, ⟨⟨certificate_1055, certificate_1055_valid⟩, ⟨⟨certificate_1056, certificate_1056_valid⟩, ⟨⟨certificate_1057, certificate_1057_valid⟩, ⟨⟨certificate_1058, certificate_1058_valid⟩, ⟨⟨certificate_1059, certificate_1059_valid⟩, ⟨⟨certificate_1060, certificate_1060_valid⟩, ⟨⟨certificate_1061, certificate_1061_valid⟩, ⟨⟨certificate_1062, certificate_1062_valid⟩, ⟨⟨certificate_1063, certificate_1063_valid⟩, ⟨⟨certificate_1064, certificate_1064_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_8_2_verified : ∀ D ∈ patterns_14_8_2, PatternVerified 14 8 D := by

  simp only [patterns_14_8_2, List.forall_mem_cons]

  exact ⟨⟨certificate_1065, certificate_1065_valid⟩, ⟨⟨certificate_1066, certificate_1066_valid⟩, ⟨⟨certificate_1067, certificate_1067_valid⟩, ⟨⟨certificate_1068, certificate_1068_valid⟩, ⟨⟨certificate_1069, certificate_1069_valid⟩, ⟨⟨certificate_1070, certificate_1070_valid⟩, ⟨⟨certificate_1071, certificate_1071_valid⟩, ⟨⟨certificate_1072, certificate_1072_valid⟩, ⟨⟨certificate_1073, certificate_1073_valid⟩, ⟨⟨certificate_1074, certificate_1074_valid⟩, ⟨⟨certificate_1075, certificate_1075_valid⟩, ⟨⟨certificate_1076, certificate_1076_valid⟩, ⟨⟨certificate_1077, certificate_1077_valid⟩, ⟨⟨certificate_1078, certificate_1078_valid⟩, ⟨⟨certificate_1079, certificate_1079_valid⟩, ⟨⟨certificate_1080, certificate_1080_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_8_3_verified : ∀ D ∈ patterns_14_8_3, PatternVerified 14 8 D := by

  simp only [patterns_14_8_3, List.forall_mem_cons]

  exact ⟨⟨certificate_1081, certificate_1081_valid⟩, ⟨⟨certificate_1082, certificate_1082_valid⟩, ⟨⟨certificate_1083, certificate_1083_valid⟩, ⟨⟨certificate_1084, certificate_1084_valid⟩, ⟨⟨certificate_1085, certificate_1085_valid⟩, ⟨⟨certificate_1086, certificate_1086_valid⟩, ⟨⟨certificate_1087, certificate_1087_valid⟩, ⟨⟨certificate_1088, certificate_1088_valid⟩, ⟨⟨certificate_1089, certificate_1089_valid⟩, ⟨⟨certificate_1090, certificate_1090_valid⟩, ⟨⟨certificate_1091, certificate_1091_valid⟩, ⟨⟨certificate_1092, certificate_1092_valid⟩, ⟨⟨certificate_1093, certificate_1093_valid⟩, ⟨⟨certificate_1094, certificate_1094_valid⟩, ⟨⟨certificate_1095, certificate_1095_valid⟩, ⟨⟨certificate_1096, certificate_1096_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_8_4_verified : ∀ D ∈ patterns_14_8_4, PatternVerified 14 8 D := by

  simp only [patterns_14_8_4, List.forall_mem_cons]

  exact ⟨⟨certificate_1097, certificate_1097_valid⟩, ⟨⟨certificate_1098, certificate_1098_valid⟩, ⟨⟨certificate_1099, certificate_1099_valid⟩, ⟨⟨certificate_1100, certificate_1100_valid⟩, ⟨⟨certificate_1101, certificate_1101_valid⟩, ⟨⟨certificate_1102, certificate_1102_valid⟩, ⟨⟨certificate_1103, certificate_1103_valid⟩, ⟨⟨certificate_1104, certificate_1104_valid⟩, ⟨⟨certificate_1105, certificate_1105_valid⟩, ⟨⟨certificate_1106, certificate_1106_valid⟩, ⟨⟨certificate_1107, certificate_1107_valid⟩, ⟨⟨certificate_1108, certificate_1108_valid⟩, ⟨⟨certificate_1109, certificate_1109_valid⟩, ⟨⟨certificate_1110, certificate_1110_valid⟩, ⟨⟨certificate_1111, certificate_1111_valid⟩, ⟨⟨certificate_1112, certificate_1112_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_8_5_verified : ∀ D ∈ patterns_14_8_5, PatternVerified 14 8 D := by

  simp only [patterns_14_8_5, List.forall_mem_cons]

  exact ⟨⟨certificate_1113, certificate_1113_valid⟩, ⟨⟨certificate_1114, certificate_1114_valid⟩, ⟨⟨certificate_1115, certificate_1115_valid⟩, ⟨⟨certificate_1116, certificate_1116_valid⟩, ⟨⟨certificate_1117, certificate_1117_valid⟩, ⟨⟨certificate_1118, certificate_1118_valid⟩, ⟨⟨certificate_1119, certificate_1119_valid⟩, ⟨⟨certificate_1120, certificate_1120_valid⟩, ⟨⟨certificate_1121, certificate_1121_valid⟩, ⟨⟨certificate_1122, certificate_1122_valid⟩, ⟨⟨certificate_1123, certificate_1123_valid⟩, ⟨⟨certificate_1124, certificate_1124_valid⟩, ⟨⟨certificate_1125, certificate_1125_valid⟩, ⟨⟨certificate_1126, certificate_1126_valid⟩, ⟨⟨certificate_1127, certificate_1127_valid⟩, ⟨⟨certificate_1128, certificate_1128_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_8_6_verified : ∀ D ∈ patterns_14_8_6, PatternVerified 14 8 D := by

  simp only [patterns_14_8_6, List.forall_mem_cons]

  exact ⟨⟨certificate_1129, certificate_1129_valid⟩, ⟨⟨certificate_1130, certificate_1130_valid⟩, ⟨⟨certificate_1131, certificate_1131_valid⟩, ⟨⟨certificate_1132, certificate_1132_valid⟩, ⟨⟨certificate_1133, certificate_1133_valid⟩, ⟨⟨certificate_1134, certificate_1134_valid⟩, ⟨⟨certificate_1135, certificate_1135_valid⟩, ⟨⟨certificate_1136, certificate_1136_valid⟩, ⟨⟨certificate_1137, certificate_1137_valid⟩, ⟨⟨certificate_1138, certificate_1138_valid⟩, ⟨⟨certificate_1139, certificate_1139_valid⟩, ⟨⟨certificate_1140, certificate_1140_valid⟩, ⟨⟨certificate_1141, certificate_1141_valid⟩, ⟨⟨certificate_1142, certificate_1142_valid⟩, ⟨⟨certificate_1143, certificate_1143_valid⟩, ⟨⟨certificate_1144, certificate_1144_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_8_7_verified : ∀ D ∈ patterns_14_8_7, PatternVerified 14 8 D := by

  simp only [patterns_14_8_7, List.forall_mem_cons]

  exact ⟨⟨certificate_1145, certificate_1145_valid⟩, ⟨⟨certificate_1146, certificate_1146_valid⟩, ⟨⟨certificate_1147, certificate_1147_valid⟩, ⟨⟨certificate_1148, certificate_1148_valid⟩, ⟨⟨certificate_1149, certificate_1149_valid⟩, ⟨⟨certificate_1150, certificate_1150_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩

theorem patterns_14_8_verified : ∀ D ∈ patterns_14_8, PatternVerified 14 8 D := by

  simp only [patterns_14_8, List.forall_mem_append]

  exact ⟨patterns_14_8_0_verified, ⟨patterns_14_8_1_verified, ⟨patterns_14_8_2_verified, ⟨patterns_14_8_3_verified, ⟨patterns_14_8_4_verified, ⟨patterns_14_8_5_verified, ⟨patterns_14_8_6_verified, ⟨patterns_14_8_7_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_8_coverage : patternChoices 8 6 [] = patterns_14_8 := by decide +kernel

theorem finite_patterns_14_8_oai : ∀ D ∈ patternChoices 8 (14-8) [], PatternVerified 14 8 D := by

  rw [patterns_14_8_coverage]

  exact patterns_14_8_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_14_8_oai := @OAI.CycleClique.finite_patterns_14_8_oai
