-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_15_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:51:15.030661+00:00
-- url     : https://prove2.me/submissions/938ea4fd-5e10-442e-ae49-3770f4675af2

import Mathlib
import Definitions.Def_OAIQ107D126
import Definitions.Def_OAIQ107D133
import Theorems.Thm_OAI_CycleClique_patterns_15_7_0_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_10_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_11_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_12_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_13_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_14_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_15_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_16_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_17_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_18_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_19_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_1_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_20_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_21_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_22_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_4_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_8_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_7_9_verified

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates037
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1183_checked : certificate_1183.Valid 15 7 10 certificate_1183_q certificate_1183_edges 3 3 [] := by decide +kernel
theorem certificate_1183_valid : certificate_1183.Valid 15 7 (patternOrder [[],[],[],[1,1,1]]) (patternClique [[],[],[],[1,1,1]]) (patternEdges [[],[],[],[1,1,1]]) (patternAmount [[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[1,1,1]]) [] := certificate_1183_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates038
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1184_checked : certificate_1184.Valid 15 7 11 certificate_1184_q certificate_1184_edges 4 3 [] := by decide +kernel
theorem certificate_1184_valid : certificate_1184.Valid 15 7 (patternOrder [[],[],[],[1,1,2]]) (patternClique [[],[],[],[1,1,2]]) (patternEdges [[],[],[],[1,1,2]]) (patternAmount [[],[],[],[1,1,2]]) (patternEdgeCount [[],[],[],[1,1,2]]) [] := certificate_1184_checked

theorem certificate_1185_checked : certificate_1185.Valid 15 7 12 certificate_1185_q certificate_1185_edges 5 3 [] := by decide +kernel
theorem certificate_1185_valid : certificate_1185.Valid 15 7 (patternOrder [[],[],[],[1,1,3]]) (patternClique [[],[],[],[1,1,3]]) (patternEdges [[],[],[],[1,1,3]]) (patternAmount [[],[],[],[1,1,3]]) (patternEdgeCount [[],[],[],[1,1,3]]) [] := certificate_1185_checked

theorem certificate_1186_checked : certificate_1186.Valid 15 7 13 certificate_1186_q certificate_1186_edges 6 3 [] := by decide +kernel
theorem certificate_1186_valid : certificate_1186.Valid 15 7 (patternOrder [[],[],[],[1,1,4]]) (patternClique [[],[],[],[1,1,4]]) (patternEdges [[],[],[],[1,1,4]]) (patternAmount [[],[],[],[1,1,4]]) (patternEdgeCount [[],[],[],[1,1,4]]) [] := certificate_1186_checked

theorem certificate_1187_checked : certificate_1187.Valid 15 7 14 certificate_1187_q certificate_1187_edges 7 3 [] := by decide +kernel
theorem certificate_1187_valid : certificate_1187.Valid 15 7 (patternOrder [[],[],[],[1,1,5]]) (patternClique [[],[],[],[1,1,5]]) (patternEdges [[],[],[],[1,1,5]]) (patternAmount [[],[],[],[1,1,5]]) (patternEdgeCount [[],[],[],[1,1,5]]) [] := certificate_1187_checked

theorem certificate_1188_checked : certificate_1188.Valid 15 7 15 certificate_1188_q certificate_1188_edges 8 3 [] := by decide +kernel
theorem certificate_1188_valid : certificate_1188.Valid 15 7 (patternOrder [[],[],[],[1,1,6]]) (patternClique [[],[],[],[1,1,6]]) (patternEdges [[],[],[],[1,1,6]]) (patternAmount [[],[],[],[1,1,6]]) (patternEdgeCount [[],[],[],[1,1,6]]) [] := certificate_1188_checked

theorem certificate_1189_checked : certificate_1189.Valid 15 7 11 certificate_1189_q certificate_1189_edges 4 3 [] := by decide +kernel
theorem certificate_1189_valid : certificate_1189.Valid 15 7 (patternOrder [[],[],[],[1,2,1]]) (patternClique [[],[],[],[1,2,1]]) (patternEdges [[],[],[],[1,2,1]]) (patternAmount [[],[],[],[1,2,1]]) (patternEdgeCount [[],[],[],[1,2,1]]) [] := certificate_1189_checked

theorem certificate_1190_checked : certificate_1190.Valid 15 7 12 certificate_1190_q certificate_1190_edges 5 3 [] := by decide +kernel
theorem certificate_1190_valid : certificate_1190.Valid 15 7 (patternOrder [[],[],[],[1,2,2]]) (patternClique [[],[],[],[1,2,2]]) (patternEdges [[],[],[],[1,2,2]]) (patternAmount [[],[],[],[1,2,2]]) (patternEdgeCount [[],[],[],[1,2,2]]) [] := certificate_1190_checked

theorem certificate_1191_checked : certificate_1191.Valid 15 7 13 certificate_1191_q certificate_1191_edges 6 3 [] := by decide +kernel
theorem certificate_1191_valid : certificate_1191.Valid 15 7 (patternOrder [[],[],[],[1,2,3]]) (patternClique [[],[],[],[1,2,3]]) (patternEdges [[],[],[],[1,2,3]]) (patternAmount [[],[],[],[1,2,3]]) (patternEdgeCount [[],[],[],[1,2,3]]) [] := certificate_1191_checked

theorem certificate_1192_checked : certificate_1192.Valid 15 7 14 certificate_1192_q certificate_1192_edges 7 3 [] := by decide +kernel
theorem certificate_1192_valid : certificate_1192.Valid 15 7 (patternOrder [[],[],[],[1,2,4]]) (patternClique [[],[],[],[1,2,4]]) (patternEdges [[],[],[],[1,2,4]]) (patternAmount [[],[],[],[1,2,4]]) (patternEdgeCount [[],[],[],[1,2,4]]) [] := certificate_1192_checked

theorem certificate_1193_checked : certificate_1193.Valid 15 7 15 certificate_1193_q certificate_1193_edges 8 3 [] := by decide +kernel
theorem certificate_1193_valid : certificate_1193.Valid 15 7 (patternOrder [[],[],[],[1,2,5]]) (patternClique [[],[],[],[1,2,5]]) (patternEdges [[],[],[],[1,2,5]]) (patternAmount [[],[],[],[1,2,5]]) (patternEdgeCount [[],[],[],[1,2,5]]) [] := certificate_1193_checked

theorem certificate_1194_checked : certificate_1194.Valid 15 7 12 certificate_1194_q certificate_1194_edges 5 3 [] := by decide +kernel
theorem certificate_1194_valid : certificate_1194.Valid 15 7 (patternOrder [[],[],[],[1,3,1]]) (patternClique [[],[],[],[1,3,1]]) (patternEdges [[],[],[],[1,3,1]]) (patternAmount [[],[],[],[1,3,1]]) (patternEdgeCount [[],[],[],[1,3,1]]) [] := certificate_1194_checked

theorem certificate_1195_checked : certificate_1195.Valid 15 7 13 certificate_1195_q certificate_1195_edges 6 3 [] := by decide +kernel
theorem certificate_1195_valid : certificate_1195.Valid 15 7 (patternOrder [[],[],[],[1,3,2]]) (patternClique [[],[],[],[1,3,2]]) (patternEdges [[],[],[],[1,3,2]]) (patternAmount [[],[],[],[1,3,2]]) (patternEdgeCount [[],[],[],[1,3,2]]) [] := certificate_1195_checked

theorem certificate_1196_checked : certificate_1196.Valid 15 7 14 certificate_1196_q certificate_1196_edges 7 3 [] := by decide +kernel
theorem certificate_1196_valid : certificate_1196.Valid 15 7 (patternOrder [[],[],[],[1,3,3]]) (patternClique [[],[],[],[1,3,3]]) (patternEdges [[],[],[],[1,3,3]]) (patternAmount [[],[],[],[1,3,3]]) (patternEdgeCount [[],[],[],[1,3,3]]) [] := certificate_1196_checked

theorem certificate_1197_checked : certificate_1197.Valid 15 7 15 certificate_1197_q certificate_1197_edges 8 3 [] := by decide +kernel
theorem certificate_1197_valid : certificate_1197.Valid 15 7 (patternOrder [[],[],[],[1,3,4]]) (patternClique [[],[],[],[1,3,4]]) (patternEdges [[],[],[],[1,3,4]]) (patternAmount [[],[],[],[1,3,4]]) (patternEdgeCount [[],[],[],[1,3,4]]) [] := certificate_1197_checked

theorem certificate_1198_checked : certificate_1198.Valid 15 7 13 certificate_1198_q certificate_1198_edges 6 3 [] := by decide +kernel
theorem certificate_1198_valid : certificate_1198.Valid 15 7 (patternOrder [[],[],[],[1,4,1]]) (patternClique [[],[],[],[1,4,1]]) (patternEdges [[],[],[],[1,4,1]]) (patternAmount [[],[],[],[1,4,1]]) (patternEdgeCount [[],[],[],[1,4,1]]) [] := certificate_1198_checked

theorem certificate_1199_checked : certificate_1199.Valid 15 7 14 certificate_1199_q certificate_1199_edges 7 3 [] := by decide +kernel
theorem certificate_1199_valid : certificate_1199.Valid 15 7 (patternOrder [[],[],[],[1,4,2]]) (patternClique [[],[],[],[1,4,2]]) (patternEdges [[],[],[],[1,4,2]]) (patternAmount [[],[],[],[1,4,2]]) (patternEdgeCount [[],[],[],[1,4,2]]) [] := certificate_1199_checked

theorem certificate_1200_checked : certificate_1200.Valid 15 7 15 certificate_1200_q certificate_1200_edges 8 3 [] := by decide +kernel
theorem certificate_1200_valid : certificate_1200.Valid 15 7 (patternOrder [[],[],[],[1,4,3]]) (patternClique [[],[],[],[1,4,3]]) (patternEdges [[],[],[],[1,4,3]]) (patternAmount [[],[],[],[1,4,3]]) (patternEdgeCount [[],[],[],[1,4,3]]) [] := certificate_1200_checked

theorem certificate_1201_checked : certificate_1201.Valid 15 7 14 certificate_1201_q certificate_1201_edges 7 3 [] := by decide +kernel
theorem certificate_1201_valid : certificate_1201.Valid 15 7 (patternOrder [[],[],[],[1,5,1]]) (patternClique [[],[],[],[1,5,1]]) (patternEdges [[],[],[],[1,5,1]]) (patternAmount [[],[],[],[1,5,1]]) (patternEdgeCount [[],[],[],[1,5,1]]) [] := certificate_1201_checked

theorem certificate_1202_checked : certificate_1202.Valid 15 7 15 certificate_1202_q certificate_1202_edges 8 3 [] := by decide +kernel
theorem certificate_1202_valid : certificate_1202.Valid 15 7 (patternOrder [[],[],[],[1,5,2]]) (patternClique [[],[],[],[1,5,2]]) (patternEdges [[],[],[],[1,5,2]]) (patternAmount [[],[],[],[1,5,2]]) (patternEdgeCount [[],[],[],[1,5,2]]) [] := certificate_1202_checked

theorem certificate_1203_checked : certificate_1203.Valid 15 7 15 certificate_1203_q certificate_1203_edges 8 3 [] := by decide +kernel
theorem certificate_1203_valid : certificate_1203.Valid 15 7 (patternOrder [[],[],[],[1,6,1]]) (patternClique [[],[],[],[1,6,1]]) (patternEdges [[],[],[],[1,6,1]]) (patternAmount [[],[],[],[1,6,1]]) (patternEdgeCount [[],[],[],[1,6,1]]) [] := certificate_1203_checked

theorem certificate_1204_checked : certificate_1204.Valid 15 7 11 certificate_1204_q certificate_1204_edges 4 2 [] := by decide +kernel
theorem certificate_1204_valid : certificate_1204.Valid 15 7 (patternOrder [[],[],[],[2],[2]]) (patternClique [[],[],[],[2],[2]]) (patternEdges [[],[],[],[2],[2]]) (patternAmount [[],[],[],[2],[2]]) (patternEdgeCount [[],[],[],[2],[2]]) [] := certificate_1204_checked

theorem certificate_1205_checked : certificate_1205.Valid 15 7 12 certificate_1205_q certificate_1205_edges 5 2 [] := by decide +kernel
theorem certificate_1205_valid : certificate_1205.Valid 15 7 (patternOrder [[],[],[],[2],[3]]) (patternClique [[],[],[],[2],[3]]) (patternEdges [[],[],[],[2],[3]]) (patternAmount [[],[],[],[2],[3]]) (patternEdgeCount [[],[],[],[2],[3]]) [] := certificate_1205_checked

theorem certificate_1206_checked : certificate_1206.Valid 15 7 13 certificate_1206_q certificate_1206_edges 6 2 [] := by decide +kernel
theorem certificate_1206_valid : certificate_1206.Valid 15 7 (patternOrder [[],[],[],[2],[4]]) (patternClique [[],[],[],[2],[4]]) (patternEdges [[],[],[],[2],[4]]) (patternAmount [[],[],[],[2],[4]]) (patternEdgeCount [[],[],[],[2],[4]]) [] := certificate_1206_checked

theorem certificate_1207_checked : certificate_1207.Valid 15 7 14 certificate_1207_q certificate_1207_edges 7 2 [] := by decide +kernel
theorem certificate_1207_valid : certificate_1207.Valid 15 7 (patternOrder [[],[],[],[2],[5]]) (patternClique [[],[],[],[2],[5]]) (patternEdges [[],[],[],[2],[5]]) (patternAmount [[],[],[],[2],[5]]) (patternEdgeCount [[],[],[],[2],[5]]) [] := certificate_1207_checked

theorem certificate_1208_checked : certificate_1208.Valid 15 7 15 certificate_1208_q certificate_1208_edges 8 2 [] := by decide +kernel
theorem certificate_1208_valid : certificate_1208.Valid 15 7 (patternOrder [[],[],[],[2],[6]]) (patternClique [[],[],[],[2],[6]]) (patternEdges [[],[],[],[2],[6]]) (patternAmount [[],[],[],[2],[6]]) (patternEdgeCount [[],[],[],[2],[6]]) [] := certificate_1208_checked

theorem certificate_1209_checked : certificate_1209.Valid 15 7 12 certificate_1209_q certificate_1209_edges 5 3 [] := by decide +kernel
theorem certificate_1209_valid : certificate_1209.Valid 15 7 (patternOrder [[],[],[],[2,1,2]]) (patternClique [[],[],[],[2,1,2]]) (patternEdges [[],[],[],[2,1,2]]) (patternAmount [[],[],[],[2,1,2]]) (patternEdgeCount [[],[],[],[2,1,2]]) [] := certificate_1209_checked

theorem certificate_1210_checked : certificate_1210.Valid 15 7 13 certificate_1210_q certificate_1210_edges 6 3 [] := by decide +kernel
theorem certificate_1210_valid : certificate_1210.Valid 15 7 (patternOrder [[],[],[],[2,1,3]]) (patternClique [[],[],[],[2,1,3]]) (patternEdges [[],[],[],[2,1,3]]) (patternAmount [[],[],[],[2,1,3]]) (patternEdgeCount [[],[],[],[2,1,3]]) [] := certificate_1210_checked

theorem certificate_1211_checked : certificate_1211.Valid 15 7 14 certificate_1211_q certificate_1211_edges 7 3 [] := by decide +kernel
theorem certificate_1211_valid : certificate_1211.Valid 15 7 (patternOrder [[],[],[],[2,1,4]]) (patternClique [[],[],[],[2,1,4]]) (patternEdges [[],[],[],[2,1,4]]) (patternAmount [[],[],[],[2,1,4]]) (patternEdgeCount [[],[],[],[2,1,4]]) [] := certificate_1211_checked

theorem certificate_1212_checked : certificate_1212.Valid 15 7 15 certificate_1212_q certificate_1212_edges 8 3 [] := by decide +kernel
theorem certificate_1212_valid : certificate_1212.Valid 15 7 (patternOrder [[],[],[],[2,1,5]]) (patternClique [[],[],[],[2,1,5]]) (patternEdges [[],[],[],[2,1,5]]) (patternAmount [[],[],[],[2,1,5]]) (patternEdgeCount [[],[],[],[2,1,5]]) [] := certificate_1212_checked

theorem certificate_1213_checked : certificate_1213.Valid 15 7 13 certificate_1213_q certificate_1213_edges 6 3 [] := by decide +kernel
theorem certificate_1213_valid : certificate_1213.Valid 15 7 (patternOrder [[],[],[],[2,2,2]]) (patternClique [[],[],[],[2,2,2]]) (patternEdges [[],[],[],[2,2,2]]) (patternAmount [[],[],[],[2,2,2]]) (patternEdgeCount [[],[],[],[2,2,2]]) [] := certificate_1213_checked

theorem certificate_1214_checked : certificate_1214.Valid 15 7 14 certificate_1214_q certificate_1214_edges 7 3 [] := by decide +kernel
theorem certificate_1214_valid : certificate_1214.Valid 15 7 (patternOrder [[],[],[],[2,2,3]]) (patternClique [[],[],[],[2,2,3]]) (patternEdges [[],[],[],[2,2,3]]) (patternAmount [[],[],[],[2,2,3]]) (patternEdgeCount [[],[],[],[2,2,3]]) [] := certificate_1214_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates039
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1231_checked : certificate_1231.Valid 15 7 15 certificate_1231_q certificate_1231_edges 8 3 [] := by decide +kernel
theorem certificate_1231_valid : certificate_1231.Valid 15 7 (patternOrder [[],[],[1],[1,6]]) (patternClique [[],[],[1],[1,6]]) (patternEdges [[],[],[1],[1,6]]) (patternAmount [[],[],[1],[1,6]]) (patternEdgeCount [[],[],[1],[1,6]]) [] := certificate_1231_checked

theorem certificate_1232_checked : certificate_1232.Valid 15 7 12 certificate_1232_q certificate_1232_edges 5 3 [] := by decide +kernel
theorem certificate_1232_valid : certificate_1232.Valid 15 7 (patternOrder [[],[],[1],[2,2]]) (patternClique [[],[],[1],[2,2]]) (patternEdges [[],[],[1],[2,2]]) (patternAmount [[],[],[1],[2,2]]) (patternEdgeCount [[],[],[1],[2,2]]) [] := certificate_1232_checked

theorem certificate_1233_checked : certificate_1233.Valid 15 7 13 certificate_1233_q certificate_1233_edges 6 3 [] := by decide +kernel
theorem certificate_1233_valid : certificate_1233.Valid 15 7 (patternOrder [[],[],[1],[2,3]]) (patternClique [[],[],[1],[2,3]]) (patternEdges [[],[],[1],[2,3]]) (patternAmount [[],[],[1],[2,3]]) (patternEdgeCount [[],[],[1],[2,3]]) [] := certificate_1233_checked

theorem certificate_1234_checked : certificate_1234.Valid 15 7 14 certificate_1234_q certificate_1234_edges 7 3 [] := by decide +kernel
theorem certificate_1234_valid : certificate_1234.Valid 15 7 (patternOrder [[],[],[1],[2,4]]) (patternClique [[],[],[1],[2,4]]) (patternEdges [[],[],[1],[2,4]]) (patternAmount [[],[],[1],[2,4]]) (patternEdgeCount [[],[],[1],[2,4]]) [] := certificate_1234_checked

theorem certificate_1235_checked : certificate_1235.Valid 15 7 15 certificate_1235_q certificate_1235_edges 8 3 [] := by decide +kernel
theorem certificate_1235_valid : certificate_1235.Valid 15 7 (patternOrder [[],[],[1],[2,5]]) (patternClique [[],[],[1],[2,5]]) (patternEdges [[],[],[1],[2,5]]) (patternAmount [[],[],[1],[2,5]]) (patternEdgeCount [[],[],[1],[2,5]]) [] := certificate_1235_checked

theorem certificate_1236_checked : certificate_1236.Valid 15 7 14 certificate_1236_q certificate_1236_edges 7 3 [] := by decide +kernel
theorem certificate_1236_valid : certificate_1236.Valid 15 7 (patternOrder [[],[],[1],[3,3]]) (patternClique [[],[],[1],[3,3]]) (patternEdges [[],[],[1],[3,3]]) (patternAmount [[],[],[1],[3,3]]) (patternEdgeCount [[],[],[1],[3,3]]) [] := certificate_1236_checked

theorem certificate_1237_checked : certificate_1237.Valid 15 7 15 certificate_1237_q certificate_1237_edges 8 3 [] := by decide +kernel
theorem certificate_1237_valid : certificate_1237.Valid 15 7 (patternOrder [[],[],[1],[3,4]]) (patternClique [[],[],[1],[3,4]]) (patternEdges [[],[],[1],[3,4]]) (patternAmount [[],[],[1],[3,4]]) (patternEdgeCount [[],[],[1],[3,4]]) [] := certificate_1237_checked

theorem certificate_1238_checked : certificate_1238.Valid 15 7 11 certificate_1238_q certificate_1238_edges 4 3 [] := by decide +kernel
theorem certificate_1238_valid : certificate_1238.Valid 15 7 (patternOrder [[],[],[1,1],[2]]) (patternClique [[],[],[1,1],[2]]) (patternEdges [[],[],[1,1],[2]]) (patternAmount [[],[],[1,1],[2]]) (patternEdgeCount [[],[],[1,1],[2]]) [] := certificate_1238_checked

theorem certificate_1239_checked : certificate_1239.Valid 15 7 12 certificate_1239_q certificate_1239_edges 5 3 [] := by decide +kernel
theorem certificate_1239_valid : certificate_1239.Valid 15 7 (patternOrder [[],[],[1,1],[3]]) (patternClique [[],[],[1,1],[3]]) (patternEdges [[],[],[1,1],[3]]) (patternAmount [[],[],[1,1],[3]]) (patternEdgeCount [[],[],[1,1],[3]]) [] := certificate_1239_checked

theorem certificate_1240_checked : certificate_1240.Valid 15 7 13 certificate_1240_q certificate_1240_edges 6 3 [] := by decide +kernel
theorem certificate_1240_valid : certificate_1240.Valid 15 7 (patternOrder [[],[],[1,1],[4]]) (patternClique [[],[],[1,1],[4]]) (patternEdges [[],[],[1,1],[4]]) (patternAmount [[],[],[1,1],[4]]) (patternEdgeCount [[],[],[1,1],[4]]) [] := certificate_1240_checked

theorem certificate_1241_checked : certificate_1241.Valid 15 7 14 certificate_1241_q certificate_1241_edges 7 3 [] := by decide +kernel
theorem certificate_1241_valid : certificate_1241.Valid 15 7 (patternOrder [[],[],[1,1],[5]]) (patternClique [[],[],[1,1],[5]]) (patternEdges [[],[],[1,1],[5]]) (patternAmount [[],[],[1,1],[5]]) (patternEdgeCount [[],[],[1,1],[5]]) [] := certificate_1241_checked

theorem certificate_1242_checked : certificate_1242.Valid 15 7 15 certificate_1242_q certificate_1242_edges 8 3 [] := by decide +kernel
theorem certificate_1242_valid : certificate_1242.Valid 15 7 (patternOrder [[],[],[1,1],[6]]) (patternClique [[],[],[1,1],[6]]) (patternEdges [[],[],[1,1],[6]]) (patternAmount [[],[],[1,1],[6]]) (patternEdgeCount [[],[],[1,1],[6]]) [] := certificate_1242_checked

theorem certificate_1243_checked : certificate_1243.Valid 15 7 11 certificate_1243_q certificate_1243_edges 4 4 [] := by decide +kernel
theorem certificate_1243_valid : certificate_1243.Valid 15 7 (patternOrder [[],[],[1,1,1,1]]) (patternClique [[],[],[1,1,1,1]]) (patternEdges [[],[],[1,1,1,1]]) (patternAmount [[],[],[1,1,1,1]]) (patternEdgeCount [[],[],[1,1,1,1]]) [] := certificate_1243_checked

theorem certificate_1244_checked : certificate_1244.Valid 15 7 12 certificate_1244_q certificate_1244_edges 5 4 [] := by decide +kernel
theorem certificate_1244_valid : certificate_1244.Valid 15 7 (patternOrder [[],[],[1,1,1,2]]) (patternClique [[],[],[1,1,1,2]]) (patternEdges [[],[],[1,1,1,2]]) (patternAmount [[],[],[1,1,1,2]]) (patternEdgeCount [[],[],[1,1,1,2]]) [] := certificate_1244_checked

theorem certificate_1245_checked : certificate_1245.Valid 15 7 13 certificate_1245_q certificate_1245_edges 6 4 [] := by decide +kernel
theorem certificate_1245_valid : certificate_1245.Valid 15 7 (patternOrder [[],[],[1,1,1,3]]) (patternClique [[],[],[1,1,1,3]]) (patternEdges [[],[],[1,1,1,3]]) (patternAmount [[],[],[1,1,1,3]]) (patternEdgeCount [[],[],[1,1,1,3]]) [] := certificate_1245_checked

theorem certificate_1246_checked : certificate_1246.Valid 15 7 14 certificate_1246_q certificate_1246_edges 7 4 [] := by decide +kernel
theorem certificate_1246_valid : certificate_1246.Valid 15 7 (patternOrder [[],[],[1,1,1,4]]) (patternClique [[],[],[1,1,1,4]]) (patternEdges [[],[],[1,1,1,4]]) (patternAmount [[],[],[1,1,1,4]]) (patternEdgeCount [[],[],[1,1,1,4]]) [] := certificate_1246_checked

theorem certificate_1247_checked : certificate_1247.Valid 15 7 15 certificate_1247_q certificate_1247_edges 8 4 [] := by decide +kernel
theorem certificate_1247_valid : certificate_1247.Valid 15 7 (patternOrder [[],[],[1,1,1,5]]) (patternClique [[],[],[1,1,1,5]]) (patternEdges [[],[],[1,1,1,5]]) (patternAmount [[],[],[1,1,1,5]]) (patternEdgeCount [[],[],[1,1,1,5]]) [] := certificate_1247_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates040
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1248_checked : certificate_1248.Valid 15 7 12 certificate_1248_q certificate_1248_edges 5 4 [] := by decide +kernel
theorem certificate_1248_valid : certificate_1248.Valid 15 7 (patternOrder [[],[],[1,1,2,1]]) (patternClique [[],[],[1,1,2,1]]) (patternEdges [[],[],[1,1,2,1]]) (patternAmount [[],[],[1,1,2,1]]) (patternEdgeCount [[],[],[1,1,2,1]]) [] := certificate_1248_checked

theorem certificate_1249_checked : certificate_1249.Valid 15 7 13 certificate_1249_q certificate_1249_edges 6 4 [] := by decide +kernel
theorem certificate_1249_valid : certificate_1249.Valid 15 7 (patternOrder [[],[],[1,1,2,2]]) (patternClique [[],[],[1,1,2,2]]) (patternEdges [[],[],[1,1,2,2]]) (patternAmount [[],[],[1,1,2,2]]) (patternEdgeCount [[],[],[1,1,2,2]]) [] := certificate_1249_checked

theorem certificate_1250_checked : certificate_1250.Valid 15 7 14 certificate_1250_q certificate_1250_edges 7 4 [] := by decide +kernel
theorem certificate_1250_valid : certificate_1250.Valid 15 7 (patternOrder [[],[],[1,1,2,3]]) (patternClique [[],[],[1,1,2,3]]) (patternEdges [[],[],[1,1,2,3]]) (patternAmount [[],[],[1,1,2,3]]) (patternEdgeCount [[],[],[1,1,2,3]]) [] := certificate_1250_checked

theorem certificate_1251_checked : certificate_1251.Valid 15 7 15 certificate_1251_q certificate_1251_edges 8 4 [] := by decide +kernel
theorem certificate_1251_valid : certificate_1251.Valid 15 7 (patternOrder [[],[],[1,1,2,4]]) (patternClique [[],[],[1,1,2,4]]) (patternEdges [[],[],[1,1,2,4]]) (patternAmount [[],[],[1,1,2,4]]) (patternEdgeCount [[],[],[1,1,2,4]]) [] := certificate_1251_checked

theorem certificate_1252_checked : certificate_1252.Valid 15 7 13 certificate_1252_q certificate_1252_edges 6 4 [] := by decide +kernel
theorem certificate_1252_valid : certificate_1252.Valid 15 7 (patternOrder [[],[],[1,1,3,1]]) (patternClique [[],[],[1,1,3,1]]) (patternEdges [[],[],[1,1,3,1]]) (patternAmount [[],[],[1,1,3,1]]) (patternEdgeCount [[],[],[1,1,3,1]]) [] := certificate_1252_checked

theorem certificate_1253_checked : certificate_1253.Valid 15 7 14 certificate_1253_q certificate_1253_edges 7 4 [] := by decide +kernel
theorem certificate_1253_valid : certificate_1253.Valid 15 7 (patternOrder [[],[],[1,1,3,2]]) (patternClique [[],[],[1,1,3,2]]) (patternEdges [[],[],[1,1,3,2]]) (patternAmount [[],[],[1,1,3,2]]) (patternEdgeCount [[],[],[1,1,3,2]]) [] := certificate_1253_checked

theorem certificate_1254_checked : certificate_1254.Valid 15 7 15 certificate_1254_q certificate_1254_edges 8 4 [] := by decide +kernel
theorem certificate_1254_valid : certificate_1254.Valid 15 7 (patternOrder [[],[],[1,1,3,3]]) (patternClique [[],[],[1,1,3,3]]) (patternEdges [[],[],[1,1,3,3]]) (patternAmount [[],[],[1,1,3,3]]) (patternEdgeCount [[],[],[1,1,3,3]]) [] := certificate_1254_checked

theorem certificate_1255_checked : certificate_1255.Valid 15 7 14 certificate_1255_q certificate_1255_edges 7 4 [] := by decide +kernel
theorem certificate_1255_valid : certificate_1255.Valid 15 7 (patternOrder [[],[],[1,1,4,1]]) (patternClique [[],[],[1,1,4,1]]) (patternEdges [[],[],[1,1,4,1]]) (patternAmount [[],[],[1,1,4,1]]) (patternEdgeCount [[],[],[1,1,4,1]]) [] := certificate_1255_checked

theorem certificate_1256_checked : certificate_1256.Valid 15 7 15 certificate_1256_q certificate_1256_edges 8 4 [] := by decide +kernel
theorem certificate_1256_valid : certificate_1256.Valid 15 7 (patternOrder [[],[],[1,1,4,2]]) (patternClique [[],[],[1,1,4,2]]) (patternEdges [[],[],[1,1,4,2]]) (patternAmount [[],[],[1,1,4,2]]) (patternEdgeCount [[],[],[1,1,4,2]]) [] := certificate_1256_checked

theorem certificate_1257_checked : certificate_1257.Valid 15 7 15 certificate_1257_q certificate_1257_edges 8 4 [] := by decide +kernel
theorem certificate_1257_valid : certificate_1257.Valid 15 7 (patternOrder [[],[],[1,1,5,1]]) (patternClique [[],[],[1,1,5,1]]) (patternEdges [[],[],[1,1,5,1]]) (patternAmount [[],[],[1,1,5,1]]) (patternEdgeCount [[],[],[1,1,5,1]]) [] := certificate_1257_checked

theorem certificate_1258_checked : certificate_1258.Valid 15 7 12 certificate_1258_q certificate_1258_edges 5 3 [] := by decide +kernel
theorem certificate_1258_valid : certificate_1258.Valid 15 7 (patternOrder [[],[],[1,2],[2]]) (patternClique [[],[],[1,2],[2]]) (patternEdges [[],[],[1,2],[2]]) (patternAmount [[],[],[1,2],[2]]) (patternEdgeCount [[],[],[1,2],[2]]) [] := certificate_1258_checked

theorem certificate_1259_checked : certificate_1259.Valid 15 7 13 certificate_1259_q certificate_1259_edges 6 3 [] := by decide +kernel
theorem certificate_1259_valid : certificate_1259.Valid 15 7 (patternOrder [[],[],[1,2],[3]]) (patternClique [[],[],[1,2],[3]]) (patternEdges [[],[],[1,2],[3]]) (patternAmount [[],[],[1,2],[3]]) (patternEdgeCount [[],[],[1,2],[3]]) [] := certificate_1259_checked

theorem certificate_1260_checked : certificate_1260.Valid 15 7 14 certificate_1260_q certificate_1260_edges 7 3 [] := by decide +kernel
theorem certificate_1260_valid : certificate_1260.Valid 15 7 (patternOrder [[],[],[1,2],[4]]) (patternClique [[],[],[1,2],[4]]) (patternEdges [[],[],[1,2],[4]]) (patternAmount [[],[],[1,2],[4]]) (patternEdgeCount [[],[],[1,2],[4]]) [] := certificate_1260_checked

theorem certificate_1261_checked : certificate_1261.Valid 15 7 15 certificate_1261_q certificate_1261_edges 8 3 [] := by decide +kernel
theorem certificate_1261_valid : certificate_1261.Valid 15 7 (patternOrder [[],[],[1,2],[5]]) (patternClique [[],[],[1,2],[5]]) (patternEdges [[],[],[1,2],[5]]) (patternAmount [[],[],[1,2],[5]]) (patternEdgeCount [[],[],[1,2],[5]]) [] := certificate_1261_checked

theorem certificate_1262_checked : certificate_1262.Valid 15 7 13 certificate_1262_q certificate_1262_edges 6 4 [] := by decide +kernel
theorem certificate_1262_valid : certificate_1262.Valid 15 7 (patternOrder [[],[],[1,2,1,2]]) (patternClique [[],[],[1,2,1,2]]) (patternEdges [[],[],[1,2,1,2]]) (patternAmount [[],[],[1,2,1,2]]) (patternEdgeCount [[],[],[1,2,1,2]]) [] := certificate_1262_checked

theorem certificate_1263_checked : certificate_1263.Valid 15 7 14 certificate_1263_q certificate_1263_edges 7 4 [] := by decide +kernel
theorem certificate_1263_valid : certificate_1263.Valid 15 7 (patternOrder [[],[],[1,2,1,3]]) (patternClique [[],[],[1,2,1,3]]) (patternEdges [[],[],[1,2,1,3]]) (patternAmount [[],[],[1,2,1,3]]) (patternEdgeCount [[],[],[1,2,1,3]]) [] := certificate_1263_checked

theorem certificate_1264_checked : certificate_1264.Valid 15 7 15 certificate_1264_q certificate_1264_edges 8 4 [] := by decide +kernel
theorem certificate_1264_valid : certificate_1264.Valid 15 7 (patternOrder [[],[],[1,2,1,4]]) (patternClique [[],[],[1,2,1,4]]) (patternEdges [[],[],[1,2,1,4]]) (patternAmount [[],[],[1,2,1,4]]) (patternEdgeCount [[],[],[1,2,1,4]]) [] := certificate_1264_checked

theorem certificate_1265_checked : certificate_1265.Valid 15 7 13 certificate_1265_q certificate_1265_edges 6 4 [] := by decide +kernel
theorem certificate_1265_valid : certificate_1265.Valid 15 7 (patternOrder [[],[],[1,2,2,1]]) (patternClique [[],[],[1,2,2,1]]) (patternEdges [[],[],[1,2,2,1]]) (patternAmount [[],[],[1,2,2,1]]) (patternEdgeCount [[],[],[1,2,2,1]]) [] := certificate_1265_checked

theorem certificate_1266_checked : certificate_1266.Valid 15 7 14 certificate_1266_q certificate_1266_edges 7 4 [] := by decide +kernel
theorem certificate_1266_valid : certificate_1266.Valid 15 7 (patternOrder [[],[],[1,2,2,2]]) (patternClique [[],[],[1,2,2,2]]) (patternEdges [[],[],[1,2,2,2]]) (patternAmount [[],[],[1,2,2,2]]) (patternEdgeCount [[],[],[1,2,2,2]]) [] := certificate_1266_checked

theorem certificate_1267_checked : certificate_1267.Valid 15 7 15 certificate_1267_q certificate_1267_edges 8 4 [] := by decide +kernel
theorem certificate_1267_valid : certificate_1267.Valid 15 7 (patternOrder [[],[],[1,2,2,3]]) (patternClique [[],[],[1,2,2,3]]) (patternEdges [[],[],[1,2,2,3]]) (patternAmount [[],[],[1,2,2,3]]) (patternEdgeCount [[],[],[1,2,2,3]]) [] := certificate_1267_checked

theorem certificate_1268_checked : certificate_1268.Valid 15 7 14 certificate_1268_q certificate_1268_edges 7 4 [] := by decide +kernel
theorem certificate_1268_valid : certificate_1268.Valid 15 7 (patternOrder [[],[],[1,2,3,1]]) (patternClique [[],[],[1,2,3,1]]) (patternEdges [[],[],[1,2,3,1]]) (patternAmount [[],[],[1,2,3,1]]) (patternEdgeCount [[],[],[1,2,3,1]]) [] := certificate_1268_checked

theorem certificate_1269_checked : certificate_1269.Valid 15 7 15 certificate_1269_q certificate_1269_edges 8 4 [] := by decide +kernel
theorem certificate_1269_valid : certificate_1269.Valid 15 7 (patternOrder [[],[],[1,2,3,2]]) (patternClique [[],[],[1,2,3,2]]) (patternEdges [[],[],[1,2,3,2]]) (patternAmount [[],[],[1,2,3,2]]) (patternEdgeCount [[],[],[1,2,3,2]]) [] := certificate_1269_checked

theorem certificate_1270_checked : certificate_1270.Valid 15 7 15 certificate_1270_q certificate_1270_edges 8 4 [] := by decide +kernel
theorem certificate_1270_valid : certificate_1270.Valid 15 7 (patternOrder [[],[],[1,2,4,1]]) (patternClique [[],[],[1,2,4,1]]) (patternEdges [[],[],[1,2,4,1]]) (patternAmount [[],[],[1,2,4,1]]) (patternEdgeCount [[],[],[1,2,4,1]]) [] := certificate_1270_checked

theorem certificate_1271_checked : certificate_1271.Valid 15 7 13 certificate_1271_q certificate_1271_edges 6 3 [] := by decide +kernel
theorem certificate_1271_valid : certificate_1271.Valid 15 7 (patternOrder [[],[],[1,3],[2]]) (patternClique [[],[],[1,3],[2]]) (patternEdges [[],[],[1,3],[2]]) (patternAmount [[],[],[1,3],[2]]) (patternEdgeCount [[],[],[1,3],[2]]) [] := certificate_1271_checked

theorem certificate_1272_checked : certificate_1272.Valid 15 7 14 certificate_1272_q certificate_1272_edges 7 3 [] := by decide +kernel
theorem certificate_1272_valid : certificate_1272.Valid 15 7 (patternOrder [[],[],[1,3],[3]]) (patternClique [[],[],[1,3],[3]]) (patternEdges [[],[],[1,3],[3]]) (patternAmount [[],[],[1,3],[3]]) (patternEdgeCount [[],[],[1,3],[3]]) [] := certificate_1272_checked

theorem certificate_1273_checked : certificate_1273.Valid 15 7 15 certificate_1273_q certificate_1273_edges 8 3 [] := by decide +kernel
theorem certificate_1273_valid : certificate_1273.Valid 15 7 (patternOrder [[],[],[1,3],[4]]) (patternClique [[],[],[1,3],[4]]) (patternEdges [[],[],[1,3],[4]]) (patternAmount [[],[],[1,3],[4]]) (patternEdgeCount [[],[],[1,3],[4]]) [] := certificate_1273_checked

theorem certificate_1274_checked : certificate_1274.Valid 15 7 14 certificate_1274_q certificate_1274_edges 7 4 [] := by decide +kernel
theorem certificate_1274_valid : certificate_1274.Valid 15 7 (patternOrder [[],[],[1,3,1,2]]) (patternClique [[],[],[1,3,1,2]]) (patternEdges [[],[],[1,3,1,2]]) (patternAmount [[],[],[1,3,1,2]]) (patternEdgeCount [[],[],[1,3,1,2]]) [] := certificate_1274_checked

theorem certificate_1275_checked : certificate_1275.Valid 15 7 15 certificate_1275_q certificate_1275_edges 8 4 [] := by decide +kernel
theorem certificate_1275_valid : certificate_1275.Valid 15 7 (patternOrder [[],[],[1,3,1,3]]) (patternClique [[],[],[1,3,1,3]]) (patternEdges [[],[],[1,3,1,3]]) (patternAmount [[],[],[1,3,1,3]]) (patternEdgeCount [[],[],[1,3,1,3]]) [] := certificate_1275_checked

theorem certificate_1276_checked : certificate_1276.Valid 15 7 15 certificate_1276_q certificate_1276_edges 8 4 [] := by decide +kernel
theorem certificate_1276_valid : certificate_1276.Valid 15 7 (patternOrder [[],[],[1,3,2,2]]) (patternClique [[],[],[1,3,2,2]]) (patternEdges [[],[],[1,3,2,2]]) (patternAmount [[],[],[1,3,2,2]]) (patternEdgeCount [[],[],[1,3,2,2]]) [] := certificate_1276_checked

theorem certificate_1277_checked : certificate_1277.Valid 15 7 15 certificate_1277_q certificate_1277_edges 8 4 [] := by decide +kernel
theorem certificate_1277_valid : certificate_1277.Valid 15 7 (patternOrder [[],[],[1,3,3,1]]) (patternClique [[],[],[1,3,3,1]]) (patternEdges [[],[],[1,3,3,1]]) (patternAmount [[],[],[1,3,3,1]]) (patternEdgeCount [[],[],[1,3,3,1]]) [] := certificate_1277_checked

theorem certificate_1278_checked : certificate_1278.Valid 15 7 14 certificate_1278_q certificate_1278_edges 7 3 [] := by decide +kernel
theorem certificate_1278_valid : certificate_1278.Valid 15 7 (patternOrder [[],[],[1,4],[2]]) (patternClique [[],[],[1,4],[2]]) (patternEdges [[],[],[1,4],[2]]) (patternAmount [[],[],[1,4],[2]]) (patternEdgeCount [[],[],[1,4],[2]]) [] := certificate_1278_checked

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

theorem patterns_15_7_2_verified : ∀ D ∈ patterns_15_7_2, PatternVerified 15 7 D := by

  simp only [patterns_15_7_2, List.forall_mem_cons]

  exact ⟨⟨certificate_1183, certificate_1183_valid⟩, ⟨⟨certificate_1184, certificate_1184_valid⟩, ⟨⟨certificate_1185, certificate_1185_valid⟩, ⟨⟨certificate_1186, certificate_1186_valid⟩, ⟨⟨certificate_1187, certificate_1187_valid⟩, ⟨⟨certificate_1188, certificate_1188_valid⟩, ⟨⟨certificate_1189, certificate_1189_valid⟩, ⟨⟨certificate_1190, certificate_1190_valid⟩, ⟨⟨certificate_1191, certificate_1191_valid⟩, ⟨⟨certificate_1192, certificate_1192_valid⟩, ⟨⟨certificate_1193, certificate_1193_valid⟩, ⟨⟨certificate_1194, certificate_1194_valid⟩, ⟨⟨certificate_1195, certificate_1195_valid⟩, ⟨⟨certificate_1196, certificate_1196_valid⟩, ⟨⟨certificate_1197, certificate_1197_valid⟩, ⟨⟨certificate_1198, certificate_1198_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_7_3_verified : ∀ D ∈ patterns_15_7_3, PatternVerified 15 7 D := by

  simp only [patterns_15_7_3, List.forall_mem_cons]

  exact ⟨⟨certificate_1199, certificate_1199_valid⟩, ⟨⟨certificate_1200, certificate_1200_valid⟩, ⟨⟨certificate_1201, certificate_1201_valid⟩, ⟨⟨certificate_1202, certificate_1202_valid⟩, ⟨⟨certificate_1203, certificate_1203_valid⟩, ⟨⟨certificate_1204, certificate_1204_valid⟩, ⟨⟨certificate_1205, certificate_1205_valid⟩, ⟨⟨certificate_1206, certificate_1206_valid⟩, ⟨⟨certificate_1207, certificate_1207_valid⟩, ⟨⟨certificate_1208, certificate_1208_valid⟩, ⟨⟨certificate_1209, certificate_1209_valid⟩, ⟨⟨certificate_1210, certificate_1210_valid⟩, ⟨⟨certificate_1211, certificate_1211_valid⟩, ⟨⟨certificate_1212, certificate_1212_valid⟩, ⟨⟨certificate_1213, certificate_1213_valid⟩, ⟨⟨certificate_1214, certificate_1214_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_7_5_verified : ∀ D ∈ patterns_15_7_5, PatternVerified 15 7 D := by

  simp only [patterns_15_7_5, List.forall_mem_cons]

  exact ⟨⟨certificate_1231, certificate_1231_valid⟩, ⟨⟨certificate_1232, certificate_1232_valid⟩, ⟨⟨certificate_1233, certificate_1233_valid⟩, ⟨⟨certificate_1234, certificate_1234_valid⟩, ⟨⟨certificate_1235, certificate_1235_valid⟩, ⟨⟨certificate_1236, certificate_1236_valid⟩, ⟨⟨certificate_1237, certificate_1237_valid⟩, ⟨⟨certificate_1238, certificate_1238_valid⟩, ⟨⟨certificate_1239, certificate_1239_valid⟩, ⟨⟨certificate_1240, certificate_1240_valid⟩, ⟨⟨certificate_1241, certificate_1241_valid⟩, ⟨⟨certificate_1242, certificate_1242_valid⟩, ⟨⟨certificate_1243, certificate_1243_valid⟩, ⟨⟨certificate_1244, certificate_1244_valid⟩, ⟨⟨certificate_1245, certificate_1245_valid⟩, ⟨⟨certificate_1246, certificate_1246_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_7_6_verified : ∀ D ∈ patterns_15_7_6, PatternVerified 15 7 D := by

  simp only [patterns_15_7_6, List.forall_mem_cons]

  exact ⟨⟨certificate_1247, certificate_1247_valid⟩, ⟨⟨certificate_1248, certificate_1248_valid⟩, ⟨⟨certificate_1249, certificate_1249_valid⟩, ⟨⟨certificate_1250, certificate_1250_valid⟩, ⟨⟨certificate_1251, certificate_1251_valid⟩, ⟨⟨certificate_1252, certificate_1252_valid⟩, ⟨⟨certificate_1253, certificate_1253_valid⟩, ⟨⟨certificate_1254, certificate_1254_valid⟩, ⟨⟨certificate_1255, certificate_1255_valid⟩, ⟨⟨certificate_1256, certificate_1256_valid⟩, ⟨⟨certificate_1257, certificate_1257_valid⟩, ⟨⟨certificate_1258, certificate_1258_valid⟩, ⟨⟨certificate_1259, certificate_1259_valid⟩, ⟨⟨certificate_1260, certificate_1260_valid⟩, ⟨⟨certificate_1261, certificate_1261_valid⟩, ⟨⟨certificate_1262, certificate_1262_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_7_7_verified : ∀ D ∈ patterns_15_7_7, PatternVerified 15 7 D := by

  simp only [patterns_15_7_7, List.forall_mem_cons]

  exact ⟨⟨certificate_1263, certificate_1263_valid⟩, ⟨⟨certificate_1264, certificate_1264_valid⟩, ⟨⟨certificate_1265, certificate_1265_valid⟩, ⟨⟨certificate_1266, certificate_1266_valid⟩, ⟨⟨certificate_1267, certificate_1267_valid⟩, ⟨⟨certificate_1268, certificate_1268_valid⟩, ⟨⟨certificate_1269, certificate_1269_valid⟩, ⟨⟨certificate_1270, certificate_1270_valid⟩, ⟨⟨certificate_1271, certificate_1271_valid⟩, ⟨⟨certificate_1272, certificate_1272_valid⟩, ⟨⟨certificate_1273, certificate_1273_valid⟩, ⟨⟨certificate_1274, certificate_1274_valid⟩, ⟨⟨certificate_1275, certificate_1275_valid⟩, ⟨⟨certificate_1276, certificate_1276_valid⟩, ⟨⟨certificate_1277, certificate_1277_valid⟩, ⟨⟨certificate_1278, certificate_1278_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_7_verified : ∀ D ∈ patterns_15_7, PatternVerified 15 7 D := by

  simp only [patterns_15_7, List.forall_mem_append]

  exact ⟨patterns_15_7_0_verified, ⟨patterns_15_7_1_verified, ⟨patterns_15_7_2_verified, ⟨patterns_15_7_3_verified, ⟨patterns_15_7_4_verified, ⟨patterns_15_7_5_verified, ⟨patterns_15_7_6_verified, ⟨patterns_15_7_7_verified, ⟨patterns_15_7_8_verified, ⟨patterns_15_7_9_verified, ⟨patterns_15_7_10_verified, ⟨patterns_15_7_11_verified, ⟨patterns_15_7_12_verified, ⟨patterns_15_7_13_verified, ⟨patterns_15_7_14_verified, ⟨patterns_15_7_15_verified, ⟨patterns_15_7_16_verified, ⟨patterns_15_7_17_verified, ⟨patterns_15_7_18_verified, ⟨patterns_15_7_19_verified, ⟨patterns_15_7_20_verified, ⟨patterns_15_7_21_verified, ⟨patterns_15_7_22_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_7_coverage : patternChoices 7 8 [] = patterns_15_7 := by decide +kernel

theorem finite_patterns_15_7_oai : ∀ D ∈ patternChoices 7 (15-7) [], PatternVerified 15 7 D := by

  rw [patterns_15_7_coverage]

  exact patterns_15_7_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_15_7_oai := @OAI.CycleClique.finite_patterns_15_7_oai
