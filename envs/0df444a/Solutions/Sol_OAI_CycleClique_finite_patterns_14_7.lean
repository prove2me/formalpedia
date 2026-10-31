-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_14_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:25:19.601324+00:00
-- url     : https://prove2.me/submissions/8a82f9f1-a731-4f8d-a1bc-31c8fefb6921

import Mathlib
import Definitions.Def_OAIQ107D008
import Definitions.Def_OAIQ107D133
import Theorems.Thm_OAI_CycleClique_patterns_14_7_0_verified
import Theorems.Thm_OAI_CycleClique_patterns_14_7_10_verified
import Theorems.Thm_OAI_CycleClique_patterns_14_7_11_verified
import Theorems.Thm_OAI_CycleClique_patterns_14_7_1_verified
import Theorems.Thm_OAI_CycleClique_patterns_14_7_3_verified
import Theorems.Thm_OAI_CycleClique_patterns_14_7_4_verified
import Theorems.Thm_OAI_CycleClique_patterns_14_7_5_verified

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates028
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_868_checked : certificate_868.Valid 14 7 12 certificate_868_q certificate_868_edges 5 3 [] := by decide +kernel
theorem certificate_868_valid : certificate_868.Valid 14 7 (patternOrder [[],[],[],[1,2,2]]) (patternClique [[],[],[],[1,2,2]]) (patternEdges [[],[],[],[1,2,2]]) (patternAmount [[],[],[],[1,2,2]]) (patternEdgeCount [[],[],[],[1,2,2]]) [] := certificate_868_checked

theorem certificate_869_checked : certificate_869.Valid 14 7 13 certificate_869_q certificate_869_edges 6 3 [] := by decide +kernel
theorem certificate_869_valid : certificate_869.Valid 14 7 (patternOrder [[],[],[],[1,2,3]]) (patternClique [[],[],[],[1,2,3]]) (patternEdges [[],[],[],[1,2,3]]) (patternAmount [[],[],[],[1,2,3]]) (patternEdgeCount [[],[],[],[1,2,3]]) [] := certificate_869_checked

theorem certificate_870_checked : certificate_870.Valid 14 7 14 certificate_870_q certificate_870_edges 7 3 [] := by decide +kernel
theorem certificate_870_valid : certificate_870.Valid 14 7 (patternOrder [[],[],[],[1,2,4]]) (patternClique [[],[],[],[1,2,4]]) (patternEdges [[],[],[],[1,2,4]]) (patternAmount [[],[],[],[1,2,4]]) (patternEdgeCount [[],[],[],[1,2,4]]) [] := certificate_870_checked

theorem certificate_871_checked : certificate_871.Valid 14 7 12 certificate_871_q certificate_871_edges 5 3 [] := by decide +kernel
theorem certificate_871_valid : certificate_871.Valid 14 7 (patternOrder [[],[],[],[1,3,1]]) (patternClique [[],[],[],[1,3,1]]) (patternEdges [[],[],[],[1,3,1]]) (patternAmount [[],[],[],[1,3,1]]) (patternEdgeCount [[],[],[],[1,3,1]]) [] := certificate_871_checked

theorem certificate_872_checked : certificate_872.Valid 14 7 13 certificate_872_q certificate_872_edges 6 3 [] := by decide +kernel
theorem certificate_872_valid : certificate_872.Valid 14 7 (patternOrder [[],[],[],[1,3,2]]) (patternClique [[],[],[],[1,3,2]]) (patternEdges [[],[],[],[1,3,2]]) (patternAmount [[],[],[],[1,3,2]]) (patternEdgeCount [[],[],[],[1,3,2]]) [] := certificate_872_checked

theorem certificate_873_checked : certificate_873.Valid 14 7 14 certificate_873_q certificate_873_edges 7 3 [] := by decide +kernel
theorem certificate_873_valid : certificate_873.Valid 14 7 (patternOrder [[],[],[],[1,3,3]]) (patternClique [[],[],[],[1,3,3]]) (patternEdges [[],[],[],[1,3,3]]) (patternAmount [[],[],[],[1,3,3]]) (patternEdgeCount [[],[],[],[1,3,3]]) [] := certificate_873_checked

theorem certificate_874_checked : certificate_874.Valid 14 7 13 certificate_874_q certificate_874_edges 6 3 [] := by decide +kernel
theorem certificate_874_valid : certificate_874.Valid 14 7 (patternOrder [[],[],[],[1,4,1]]) (patternClique [[],[],[],[1,4,1]]) (patternEdges [[],[],[],[1,4,1]]) (patternAmount [[],[],[],[1,4,1]]) (patternEdgeCount [[],[],[],[1,4,1]]) [] := certificate_874_checked

theorem certificate_875_checked : certificate_875.Valid 14 7 14 certificate_875_q certificate_875_edges 7 3 [] := by decide +kernel
theorem certificate_875_valid : certificate_875.Valid 14 7 (patternOrder [[],[],[],[1,4,2]]) (patternClique [[],[],[],[1,4,2]]) (patternEdges [[],[],[],[1,4,2]]) (patternAmount [[],[],[],[1,4,2]]) (patternEdgeCount [[],[],[],[1,4,2]]) [] := certificate_875_checked

theorem certificate_876_checked : certificate_876.Valid 14 7 14 certificate_876_q certificate_876_edges 7 3 [] := by decide +kernel
theorem certificate_876_valid : certificate_876.Valid 14 7 (patternOrder [[],[],[],[1,5,1]]) (patternClique [[],[],[],[1,5,1]]) (patternEdges [[],[],[],[1,5,1]]) (patternAmount [[],[],[],[1,5,1]]) (patternEdgeCount [[],[],[],[1,5,1]]) [] := certificate_876_checked

theorem certificate_877_checked : certificate_877.Valid 14 7 11 certificate_877_q certificate_877_edges 4 2 [] := by decide +kernel
theorem certificate_877_valid : certificate_877.Valid 14 7 (patternOrder [[],[],[],[2],[2]]) (patternClique [[],[],[],[2],[2]]) (patternEdges [[],[],[],[2],[2]]) (patternAmount [[],[],[],[2],[2]]) (patternEdgeCount [[],[],[],[2],[2]]) [] := certificate_877_checked

theorem certificate_878_checked : certificate_878.Valid 14 7 12 certificate_878_q certificate_878_edges 5 2 [] := by decide +kernel
theorem certificate_878_valid : certificate_878.Valid 14 7 (patternOrder [[],[],[],[2],[3]]) (patternClique [[],[],[],[2],[3]]) (patternEdges [[],[],[],[2],[3]]) (patternAmount [[],[],[],[2],[3]]) (patternEdgeCount [[],[],[],[2],[3]]) [] := certificate_878_checked

theorem certificate_879_checked : certificate_879.Valid 14 7 13 certificate_879_q certificate_879_edges 6 2 [] := by decide +kernel
theorem certificate_879_valid : certificate_879.Valid 14 7 (patternOrder [[],[],[],[2],[4]]) (patternClique [[],[],[],[2],[4]]) (patternEdges [[],[],[],[2],[4]]) (patternAmount [[],[],[],[2],[4]]) (patternEdgeCount [[],[],[],[2],[4]]) [] := certificate_879_checked

theorem certificate_880_checked : certificate_880.Valid 14 7 14 certificate_880_q certificate_880_edges 7 2 [] := by decide +kernel
theorem certificate_880_valid : certificate_880.Valid 14 7 (patternOrder [[],[],[],[2],[5]]) (patternClique [[],[],[],[2],[5]]) (patternEdges [[],[],[],[2],[5]]) (patternAmount [[],[],[],[2],[5]]) (patternEdgeCount [[],[],[],[2],[5]]) [] := certificate_880_checked

theorem certificate_881_checked : certificate_881.Valid 14 7 12 certificate_881_q certificate_881_edges 5 3 [] := by decide +kernel
theorem certificate_881_valid : certificate_881.Valid 14 7 (patternOrder [[],[],[],[2,1,2]]) (patternClique [[],[],[],[2,1,2]]) (patternEdges [[],[],[],[2,1,2]]) (patternAmount [[],[],[],[2,1,2]]) (patternEdgeCount [[],[],[],[2,1,2]]) [] := certificate_881_checked

theorem certificate_882_checked : certificate_882.Valid 14 7 13 certificate_882_q certificate_882_edges 6 3 [] := by decide +kernel
theorem certificate_882_valid : certificate_882.Valid 14 7 (patternOrder [[],[],[],[2,1,3]]) (patternClique [[],[],[],[2,1,3]]) (patternEdges [[],[],[],[2,1,3]]) (patternAmount [[],[],[],[2,1,3]]) (patternEdgeCount [[],[],[],[2,1,3]]) [] := certificate_882_checked

theorem certificate_883_checked : certificate_883.Valid 14 7 14 certificate_883_q certificate_883_edges 7 3 [] := by decide +kernel
theorem certificate_883_valid : certificate_883.Valid 14 7 (patternOrder [[],[],[],[2,1,4]]) (patternClique [[],[],[],[2,1,4]]) (patternEdges [[],[],[],[2,1,4]]) (patternAmount [[],[],[],[2,1,4]]) (patternEdgeCount [[],[],[],[2,1,4]]) [] := certificate_883_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates030
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_932_checked : certificate_932.Valid 14 7 11 certificate_932_q certificate_932_edges 4 3 [] := by decide +kernel
theorem certificate_932_valid : certificate_932.Valid 14 7 (patternOrder [[],[1],[1],[2]]) (patternClique [[],[1],[1],[2]]) (patternEdges [[],[1],[1],[2]]) (patternAmount [[],[1],[1],[2]]) (patternEdgeCount [[],[1],[1],[2]]) [] := certificate_932_checked

theorem certificate_933_checked : certificate_933.Valid 14 7 12 certificate_933_q certificate_933_edges 5 3 [] := by decide +kernel
theorem certificate_933_valid : certificate_933.Valid 14 7 (patternOrder [[],[1],[1],[3]]) (patternClique [[],[1],[1],[3]]) (patternEdges [[],[1],[1],[3]]) (patternAmount [[],[1],[1],[3]]) (patternEdgeCount [[],[1],[1],[3]]) [] := certificate_933_checked

theorem certificate_934_checked : certificate_934.Valid 14 7 13 certificate_934_q certificate_934_edges 6 3 [] := by decide +kernel
theorem certificate_934_valid : certificate_934.Valid 14 7 (patternOrder [[],[1],[1],[4]]) (patternClique [[],[1],[1],[4]]) (patternEdges [[],[1],[1],[4]]) (patternAmount [[],[1],[1],[4]]) (patternEdgeCount [[],[1],[1],[4]]) [] := certificate_934_checked

theorem certificate_935_checked : certificate_935.Valid 14 7 14 certificate_935_q certificate_935_edges 7 3 [] := by decide +kernel
theorem certificate_935_valid : certificate_935.Valid 14 7 (patternOrder [[],[1],[1],[5]]) (patternClique [[],[1],[1],[5]]) (patternEdges [[],[1],[1],[5]]) (patternAmount [[],[1],[1],[5]]) (patternEdgeCount [[],[1],[1],[5]]) [] := certificate_935_checked

theorem certificate_936_checked : certificate_936.Valid 14 7 11 certificate_936_q certificate_936_edges 4 4 [] := by decide +kernel
theorem certificate_936_valid : certificate_936.Valid 14 7 (patternOrder [[],[1],[1,1,1]]) (patternClique [[],[1],[1,1,1]]) (patternEdges [[],[1],[1,1,1]]) (patternAmount [[],[1],[1,1,1]]) (patternEdgeCount [[],[1],[1,1,1]]) [] := certificate_936_checked

theorem certificate_937_checked : certificate_937.Valid 14 7 12 certificate_937_q certificate_937_edges 5 4 [] := by decide +kernel
theorem certificate_937_valid : certificate_937.Valid 14 7 (patternOrder [[],[1],[1,1,2]]) (patternClique [[],[1],[1,1,2]]) (patternEdges [[],[1],[1,1,2]]) (patternAmount [[],[1],[1,1,2]]) (patternEdgeCount [[],[1],[1,1,2]]) [] := certificate_937_checked

theorem certificate_938_checked : certificate_938.Valid 14 7 13 certificate_938_q certificate_938_edges 6 4 [] := by decide +kernel
theorem certificate_938_valid : certificate_938.Valid 14 7 (patternOrder [[],[1],[1,1,3]]) (patternClique [[],[1],[1,1,3]]) (patternEdges [[],[1],[1,1,3]]) (patternAmount [[],[1],[1,1,3]]) (patternEdgeCount [[],[1],[1,1,3]]) [] := certificate_938_checked

theorem certificate_939_checked : certificate_939.Valid 14 7 14 certificate_939_q certificate_939_edges 7 4 [] := by decide +kernel
theorem certificate_939_valid : certificate_939.Valid 14 7 (patternOrder [[],[1],[1,1,4]]) (patternClique [[],[1],[1,1,4]]) (patternEdges [[],[1],[1,1,4]]) (patternAmount [[],[1],[1,1,4]]) (patternEdgeCount [[],[1],[1,1,4]]) [] := certificate_939_checked

theorem certificate_940_checked : certificate_940.Valid 14 7 12 certificate_940_q certificate_940_edges 5 4 [] := by decide +kernel
theorem certificate_940_valid : certificate_940.Valid 14 7 (patternOrder [[],[1],[1,2,1]]) (patternClique [[],[1],[1,2,1]]) (patternEdges [[],[1],[1,2,1]]) (patternAmount [[],[1],[1,2,1]]) (patternEdgeCount [[],[1],[1,2,1]]) [] := certificate_940_checked

theorem certificate_941_checked : certificate_941.Valid 14 7 13 certificate_941_q certificate_941_edges 6 4 [] := by decide +kernel
theorem certificate_941_valid : certificate_941.Valid 14 7 (patternOrder [[],[1],[1,2,2]]) (patternClique [[],[1],[1,2,2]]) (patternEdges [[],[1],[1,2,2]]) (patternAmount [[],[1],[1,2,2]]) (patternEdgeCount [[],[1],[1,2,2]]) [] := certificate_941_checked

theorem certificate_942_checked : certificate_942.Valid 14 7 14 certificate_942_q certificate_942_edges 7 4 [] := by decide +kernel
theorem certificate_942_valid : certificate_942.Valid 14 7 (patternOrder [[],[1],[1,2,3]]) (patternClique [[],[1],[1,2,3]]) (patternEdges [[],[1],[1,2,3]]) (patternAmount [[],[1],[1,2,3]]) (patternEdgeCount [[],[1],[1,2,3]]) [] := certificate_942_checked

theorem certificate_943_checked : certificate_943.Valid 14 7 13 certificate_943_q certificate_943_edges 6 4 [] := by decide +kernel
theorem certificate_943_valid : certificate_943.Valid 14 7 (patternOrder [[],[1],[1,3,1]]) (patternClique [[],[1],[1,3,1]]) (patternEdges [[],[1],[1,3,1]]) (patternAmount [[],[1],[1,3,1]]) (patternEdgeCount [[],[1],[1,3,1]]) [] := certificate_943_checked

theorem certificate_944_checked : certificate_944.Valid 14 7 14 certificate_944_q certificate_944_edges 7 4 [] := by decide +kernel
theorem certificate_944_valid : certificate_944.Valid 14 7 (patternOrder [[],[1],[1,3,2]]) (patternClique [[],[1],[1,3,2]]) (patternEdges [[],[1],[1,3,2]]) (patternAmount [[],[1],[1,3,2]]) (patternEdgeCount [[],[1],[1,3,2]]) [] := certificate_944_checked

theorem certificate_945_checked : certificate_945.Valid 14 7 14 certificate_945_q certificate_945_edges 7 4 [] := by decide +kernel
theorem certificate_945_valid : certificate_945.Valid 14 7 (patternOrder [[],[1],[1,4,1]]) (patternClique [[],[1],[1,4,1]]) (patternEdges [[],[1],[1,4,1]]) (patternAmount [[],[1],[1,4,1]]) (patternEdgeCount [[],[1],[1,4,1]]) [] := certificate_945_checked

theorem certificate_946_checked : certificate_946.Valid 14 7 12 certificate_946_q certificate_946_edges 5 3 [] := by decide +kernel
theorem certificate_946_valid : certificate_946.Valid 14 7 (patternOrder [[],[1],[2],[2]]) (patternClique [[],[1],[2],[2]]) (patternEdges [[],[1],[2],[2]]) (patternAmount [[],[1],[2],[2]]) (patternEdgeCount [[],[1],[2],[2]]) [] := certificate_946_checked

theorem certificate_947_checked : certificate_947.Valid 14 7 13 certificate_947_q certificate_947_edges 6 3 [] := by decide +kernel
theorem certificate_947_valid : certificate_947.Valid 14 7 (patternOrder [[],[1],[2],[3]]) (patternClique [[],[1],[2],[3]]) (patternEdges [[],[1],[2],[3]]) (patternAmount [[],[1],[2],[3]]) (patternEdgeCount [[],[1],[2],[3]]) [] := certificate_947_checked

theorem certificate_948_checked : certificate_948.Valid 14 7 14 certificate_948_q certificate_948_edges 7 3 [] := by decide +kernel
theorem certificate_948_valid : certificate_948.Valid 14 7 (patternOrder [[],[1],[2],[4]]) (patternClique [[],[1],[2],[4]]) (patternEdges [[],[1],[2],[4]]) (patternAmount [[],[1],[2],[4]]) (patternEdgeCount [[],[1],[2],[4]]) [] := certificate_948_checked

theorem certificate_949_checked : certificate_949.Valid 14 7 13 certificate_949_q certificate_949_edges 6 4 [] := by decide +kernel
theorem certificate_949_valid : certificate_949.Valid 14 7 (patternOrder [[],[1],[2,1,2]]) (patternClique [[],[1],[2,1,2]]) (patternEdges [[],[1],[2,1,2]]) (patternAmount [[],[1],[2,1,2]]) (patternEdgeCount [[],[1],[2,1,2]]) [] := certificate_949_checked

theorem certificate_950_checked : certificate_950.Valid 14 7 14 certificate_950_q certificate_950_edges 7 4 [] := by decide +kernel
theorem certificate_950_valid : certificate_950.Valid 14 7 (patternOrder [[],[1],[2,1,3]]) (patternClique [[],[1],[2,1,3]]) (patternEdges [[],[1],[2,1,3]]) (patternAmount [[],[1],[2,1,3]]) (patternEdgeCount [[],[1],[2,1,3]]) [] := certificate_950_checked

theorem certificate_951_checked : certificate_951.Valid 14 7 14 certificate_951_q certificate_951_edges 7 4 [] := by decide +kernel
theorem certificate_951_valid : certificate_951.Valid 14 7 (patternOrder [[],[1],[2,2,2]]) (patternClique [[],[1],[2,2,2]]) (patternEdges [[],[1],[2,2,2]]) (patternAmount [[],[1],[2,2,2]]) (patternEdgeCount [[],[1],[2,2,2]]) [] := certificate_951_checked

theorem certificate_952_checked : certificate_952.Valid 14 7 14 certificate_952_q certificate_952_edges 7 3 [] := by decide +kernel
theorem certificate_952_valid : certificate_952.Valid 14 7 (patternOrder [[],[1],[3],[3]]) (patternClique [[],[1],[3],[3]]) (patternEdges [[],[1],[3],[3]]) (patternAmount [[],[1],[3],[3]]) (patternEdgeCount [[],[1],[3],[3]]) [] := certificate_952_checked

theorem certificate_953_checked : certificate_953.Valid 14 7 11 certificate_953_q certificate_953_edges 4 4 [] := by decide +kernel
theorem certificate_953_valid : certificate_953.Valid 14 7 (patternOrder [[],[1,1],[1,1]]) (patternClique [[],[1,1],[1,1]]) (patternEdges [[],[1,1],[1,1]]) (patternAmount [[],[1,1],[1,1]]) (patternEdgeCount [[],[1,1],[1,1]]) [] := certificate_953_checked

theorem certificate_954_checked : certificate_954.Valid 14 7 12 certificate_954_q certificate_954_edges 5 4 [] := by decide +kernel
theorem certificate_954_valid : certificate_954.Valid 14 7 (patternOrder [[],[1,1],[1,2]]) (patternClique [[],[1,1],[1,2]]) (patternEdges [[],[1,1],[1,2]]) (patternAmount [[],[1,1],[1,2]]) (patternEdgeCount [[],[1,1],[1,2]]) [] := certificate_954_checked

theorem certificate_955_checked : certificate_955.Valid 14 7 13 certificate_955_q certificate_955_edges 6 4 [] := by decide +kernel
theorem certificate_955_valid : certificate_955.Valid 14 7 (patternOrder [[],[1,1],[1,3]]) (patternClique [[],[1,1],[1,3]]) (patternEdges [[],[1,1],[1,3]]) (patternAmount [[],[1,1],[1,3]]) (patternEdgeCount [[],[1,1],[1,3]]) [] := certificate_955_checked

theorem certificate_956_checked : certificate_956.Valid 14 7 14 certificate_956_q certificate_956_edges 7 4 [] := by decide +kernel
theorem certificate_956_valid : certificate_956.Valid 14 7 (patternOrder [[],[1,1],[1,4]]) (patternClique [[],[1,1],[1,4]]) (patternEdges [[],[1,1],[1,4]]) (patternAmount [[],[1,1],[1,4]]) (patternEdgeCount [[],[1,1],[1,4]]) [] := certificate_956_checked

theorem certificate_957_checked : certificate_957.Valid 14 7 13 certificate_957_q certificate_957_edges 6 4 [] := by decide +kernel
theorem certificate_957_valid : certificate_957.Valid 14 7 (patternOrder [[],[1,1],[2,2]]) (patternClique [[],[1,1],[2,2]]) (patternEdges [[],[1,1],[2,2]]) (patternAmount [[],[1,1],[2,2]]) (patternEdgeCount [[],[1,1],[2,2]]) [] := certificate_957_checked

theorem certificate_958_checked : certificate_958.Valid 14 7 14 certificate_958_q certificate_958_edges 7 4 [] := by decide +kernel
theorem certificate_958_valid : certificate_958.Valid 14 7 (patternOrder [[],[1,1],[2,3]]) (patternClique [[],[1,1],[2,3]]) (patternEdges [[],[1,1],[2,3]]) (patternAmount [[],[1,1],[2,3]]) (patternEdgeCount [[],[1,1],[2,3]]) [] := certificate_958_checked

theorem certificate_959_checked : certificate_959.Valid 14 7 12 certificate_959_q certificate_959_edges 5 4 [] := by decide +kernel
theorem certificate_959_valid : certificate_959.Valid 14 7 (patternOrder [[],[1,1,1],[2]]) (patternClique [[],[1,1,1],[2]]) (patternEdges [[],[1,1,1],[2]]) (patternAmount [[],[1,1,1],[2]]) (patternEdgeCount [[],[1,1,1],[2]]) [] := certificate_959_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates031
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_960_checked : certificate_960.Valid 14 7 13 certificate_960_q certificate_960_edges 6 4 [] := by decide +kernel
theorem certificate_960_valid : certificate_960.Valid 14 7 (patternOrder [[],[1,1,1],[3]]) (patternClique [[],[1,1,1],[3]]) (patternEdges [[],[1,1,1],[3]]) (patternAmount [[],[1,1,1],[3]]) (patternEdgeCount [[],[1,1,1],[3]]) [] := certificate_960_checked

theorem certificate_961_checked : certificate_961.Valid 14 7 14 certificate_961_q certificate_961_edges 7 4 [] := by decide +kernel
theorem certificate_961_valid : certificate_961.Valid 14 7 (patternOrder [[],[1,1,1],[4]]) (patternClique [[],[1,1,1],[4]]) (patternEdges [[],[1,1,1],[4]]) (patternAmount [[],[1,1,1],[4]]) (patternEdgeCount [[],[1,1,1],[4]]) [] := certificate_961_checked

theorem certificate_962_checked : certificate_962.Valid 14 7 12 certificate_962_q certificate_962_edges 5 5 [] := by decide +kernel
theorem certificate_962_valid : certificate_962.Valid 14 7 (patternOrder [[],[1,1,1,1,1]]) (patternClique [[],[1,1,1,1,1]]) (patternEdges [[],[1,1,1,1,1]]) (patternAmount [[],[1,1,1,1,1]]) (patternEdgeCount [[],[1,1,1,1,1]]) [] := certificate_962_checked

theorem certificate_963_checked : certificate_963.Valid 14 7 13 certificate_963_q certificate_963_edges 6 5 [] := by decide +kernel
theorem certificate_963_valid : certificate_963.Valid 14 7 (patternOrder [[],[1,1,1,1,2]]) (patternClique [[],[1,1,1,1,2]]) (patternEdges [[],[1,1,1,1,2]]) (patternAmount [[],[1,1,1,1,2]]) (patternEdgeCount [[],[1,1,1,1,2]]) [] := certificate_963_checked

theorem certificate_964_checked : certificate_964.Valid 14 7 14 certificate_964_q certificate_964_edges 7 5 [] := by decide +kernel
theorem certificate_964_valid : certificate_964.Valid 14 7 (patternOrder [[],[1,1,1,1,3]]) (patternClique [[],[1,1,1,1,3]]) (patternEdges [[],[1,1,1,1,3]]) (patternAmount [[],[1,1,1,1,3]]) (patternEdgeCount [[],[1,1,1,1,3]]) [] := certificate_964_checked

theorem certificate_965_checked : certificate_965.Valid 14 7 13 certificate_965_q certificate_965_edges 6 5 [] := by decide +kernel
theorem certificate_965_valid : certificate_965.Valid 14 7 (patternOrder [[],[1,1,1,2,1]]) (patternClique [[],[1,1,1,2,1]]) (patternEdges [[],[1,1,1,2,1]]) (patternAmount [[],[1,1,1,2,1]]) (patternEdgeCount [[],[1,1,1,2,1]]) [] := certificate_965_checked

theorem certificate_966_checked : certificate_966.Valid 14 7 14 certificate_966_q certificate_966_edges 7 5 [] := by decide +kernel
theorem certificate_966_valid : certificate_966.Valid 14 7 (patternOrder [[],[1,1,1,2,2]]) (patternClique [[],[1,1,1,2,2]]) (patternEdges [[],[1,1,1,2,2]]) (patternAmount [[],[1,1,1,2,2]]) (patternEdgeCount [[],[1,1,1,2,2]]) [] := certificate_966_checked

theorem certificate_967_checked : certificate_967.Valid 14 7 14 certificate_967_q certificate_967_edges 7 5 [] := by decide +kernel
theorem certificate_967_valid : certificate_967.Valid 14 7 (patternOrder [[],[1,1,1,3,1]]) (patternClique [[],[1,1,1,3,1]]) (patternEdges [[],[1,1,1,3,1]]) (patternAmount [[],[1,1,1,3,1]]) (patternEdgeCount [[],[1,1,1,3,1]]) [] := certificate_967_checked

theorem certificate_968_checked : certificate_968.Valid 14 7 13 certificate_968_q certificate_968_edges 6 4 [] := by decide +kernel
theorem certificate_968_valid : certificate_968.Valid 14 7 (patternOrder [[],[1,1,2],[2]]) (patternClique [[],[1,1,2],[2]]) (patternEdges [[],[1,1,2],[2]]) (patternAmount [[],[1,1,2],[2]]) (patternEdgeCount [[],[1,1,2],[2]]) [] := certificate_968_checked

theorem certificate_969_checked : certificate_969.Valid 14 7 14 certificate_969_q certificate_969_edges 7 4 [] := by decide +kernel
theorem certificate_969_valid : certificate_969.Valid 14 7 (patternOrder [[],[1,1,2],[3]]) (patternClique [[],[1,1,2],[3]]) (patternEdges [[],[1,1,2],[3]]) (patternAmount [[],[1,1,2],[3]]) (patternEdgeCount [[],[1,1,2],[3]]) [] := certificate_969_checked

theorem certificate_970_checked : certificate_970.Valid 14 7 13 certificate_970_q certificate_970_edges 6 5 [] := by decide +kernel
theorem certificate_970_valid : certificate_970.Valid 14 7 (patternOrder [[],[1,1,2,1,1]]) (patternClique [[],[1,1,2,1,1]]) (patternEdges [[],[1,1,2,1,1]]) (patternAmount [[],[1,1,2,1,1]]) (patternEdgeCount [[],[1,1,2,1,1]]) [] := certificate_970_checked

theorem certificate_971_checked : certificate_971.Valid 14 7 14 certificate_971_q certificate_971_edges 7 5 [] := by decide +kernel
theorem certificate_971_valid : certificate_971.Valid 14 7 (patternOrder [[],[1,1,2,1,2]]) (patternClique [[],[1,1,2,1,2]]) (patternEdges [[],[1,1,2,1,2]]) (patternAmount [[],[1,1,2,1,2]]) (patternEdgeCount [[],[1,1,2,1,2]]) [] := certificate_971_checked

theorem certificate_972_checked : certificate_972.Valid 14 7 14 certificate_972_q certificate_972_edges 7 5 [] := by decide +kernel
theorem certificate_972_valid : certificate_972.Valid 14 7 (patternOrder [[],[1,1,2,2,1]]) (patternClique [[],[1,1,2,2,1]]) (patternEdges [[],[1,1,2,2,1]]) (patternAmount [[],[1,1,2,2,1]]) (patternEdgeCount [[],[1,1,2,2,1]]) [] := certificate_972_checked

theorem certificate_973_checked : certificate_973.Valid 14 7 14 certificate_973_q certificate_973_edges 7 4 [] := by decide +kernel
theorem certificate_973_valid : certificate_973.Valid 14 7 (patternOrder [[],[1,1,3],[2]]) (patternClique [[],[1,1,3],[2]]) (patternEdges [[],[1,1,3],[2]]) (patternAmount [[],[1,1,3],[2]]) (patternEdgeCount [[],[1,1,3],[2]]) [] := certificate_973_checked

theorem certificate_974_checked : certificate_974.Valid 14 7 14 certificate_974_q certificate_974_edges 7 5 [] := by decide +kernel
theorem certificate_974_valid : certificate_974.Valid 14 7 (patternOrder [[],[1,1,3,1,1]]) (patternClique [[],[1,1,3,1,1]]) (patternEdges [[],[1,1,3,1,1]]) (patternAmount [[],[1,1,3,1,1]]) (patternEdgeCount [[],[1,1,3,1,1]]) [] := certificate_974_checked

theorem certificate_975_checked : certificate_975.Valid 14 7 13 certificate_975_q certificate_975_edges 6 4 [] := by decide +kernel
theorem certificate_975_valid : certificate_975.Valid 14 7 (patternOrder [[],[1,2],[1,2]]) (patternClique [[],[1,2],[1,2]]) (patternEdges [[],[1,2],[1,2]]) (patternAmount [[],[1,2],[1,2]]) (patternEdgeCount [[],[1,2],[1,2]]) [] := certificate_975_checked

theorem certificate_976_checked : certificate_976.Valid 14 7 14 certificate_976_q certificate_976_edges 7 4 [] := by decide +kernel
theorem certificate_976_valid : certificate_976.Valid 14 7 (patternOrder [[],[1,2],[1,3]]) (patternClique [[],[1,2],[1,3]]) (patternEdges [[],[1,2],[1,3]]) (patternAmount [[],[1,2],[1,3]]) (patternEdgeCount [[],[1,2],[1,3]]) [] := certificate_976_checked

theorem certificate_977_checked : certificate_977.Valid 14 7 14 certificate_977_q certificate_977_edges 7 4 [] := by decide +kernel
theorem certificate_977_valid : certificate_977.Valid 14 7 (patternOrder [[],[1,2],[2,2]]) (patternClique [[],[1,2],[2,2]]) (patternEdges [[],[1,2],[2,2]]) (patternAmount [[],[1,2],[2,2]]) (patternEdgeCount [[],[1,2],[2,2]]) [] := certificate_977_checked

theorem certificate_978_checked : certificate_978.Valid 14 7 13 certificate_978_q certificate_978_edges 6 4 [] := by decide +kernel
theorem certificate_978_valid : certificate_978.Valid 14 7 (patternOrder [[],[1,2,1],[2]]) (patternClique [[],[1,2,1],[2]]) (patternEdges [[],[1,2,1],[2]]) (patternAmount [[],[1,2,1],[2]]) (patternEdgeCount [[],[1,2,1],[2]]) [] := certificate_978_checked

theorem certificate_979_checked : certificate_979.Valid 14 7 14 certificate_979_q certificate_979_edges 7 4 [] := by decide +kernel
theorem certificate_979_valid : certificate_979.Valid 14 7 (patternOrder [[],[1,2,1],[3]]) (patternClique [[],[1,2,1],[3]]) (patternEdges [[],[1,2,1],[3]]) (patternAmount [[],[1,2,1],[3]]) (patternEdgeCount [[],[1,2,1],[3]]) [] := certificate_979_checked

theorem certificate_980_checked : certificate_980.Valid 14 7 14 certificate_980_q certificate_980_edges 7 5 [] := by decide +kernel
theorem certificate_980_valid : certificate_980.Valid 14 7 (patternOrder [[],[1,2,1,1,2]]) (patternClique [[],[1,2,1,1,2]]) (patternEdges [[],[1,2,1,1,2]]) (patternAmount [[],[1,2,1,1,2]]) (patternEdgeCount [[],[1,2,1,1,2]]) [] := certificate_980_checked

theorem certificate_981_checked : certificate_981.Valid 14 7 14 certificate_981_q certificate_981_edges 7 5 [] := by decide +kernel
theorem certificate_981_valid : certificate_981.Valid 14 7 (patternOrder [[],[1,2,1,2,1]]) (patternClique [[],[1,2,1,2,1]]) (patternEdges [[],[1,2,1,2,1]]) (patternAmount [[],[1,2,1,2,1]]) (patternEdgeCount [[],[1,2,1,2,1]]) [] := certificate_981_checked

theorem certificate_982_checked : certificate_982.Valid 14 7 14 certificate_982_q certificate_982_edges 7 4 [] := by decide +kernel
theorem certificate_982_valid : certificate_982.Valid 14 7 (patternOrder [[],[1,2,2],[2]]) (patternClique [[],[1,2,2],[2]]) (patternEdges [[],[1,2,2],[2]]) (patternAmount [[],[1,2,2],[2]]) (patternEdgeCount [[],[1,2,2],[2]]) [] := certificate_982_checked

theorem certificate_983_checked : certificate_983.Valid 14 7 14 certificate_983_q certificate_983_edges 7 4 [] := by decide +kernel
theorem certificate_983_valid : certificate_983.Valid 14 7 (patternOrder [[],[1,3,1],[2]]) (patternClique [[],[1,3,1],[2]]) (patternEdges [[],[1,3,1],[2]]) (patternAmount [[],[1,3,1],[2]]) (patternEdgeCount [[],[1,3,1],[2]]) [] := certificate_983_checked

theorem certificate_984_checked : certificate_984.Valid 14 7 13 certificate_984_q certificate_984_edges 6 3 [] := by decide +kernel
theorem certificate_984_valid : certificate_984.Valid 14 7 (patternOrder [[],[2],[2],[2]]) (patternClique [[],[2],[2],[2]]) (patternEdges [[],[2],[2],[2]]) (patternAmount [[],[2],[2],[2]]) (patternEdgeCount [[],[2],[2],[2]]) [] := certificate_984_checked

theorem certificate_985_checked : certificate_985.Valid 14 7 14 certificate_985_q certificate_985_edges 7 3 [] := by decide +kernel
theorem certificate_985_valid : certificate_985.Valid 14 7 (patternOrder [[],[2],[2],[3]]) (patternClique [[],[2],[2],[3]]) (patternEdges [[],[2],[2],[3]]) (patternAmount [[],[2],[2],[3]]) (patternEdgeCount [[],[2],[2],[3]]) [] := certificate_985_checked

theorem certificate_986_checked : certificate_986.Valid 14 7 14 certificate_986_q certificate_986_edges 7 4 [] := by decide +kernel
theorem certificate_986_valid : certificate_986.Valid 14 7 (patternOrder [[],[2],[2,1,2]]) (patternClique [[],[2],[2,1,2]]) (patternEdges [[],[2],[2,1,2]]) (patternAmount [[],[2],[2,1,2]]) (patternEdgeCount [[],[2],[2,1,2]]) [] := certificate_986_checked

theorem certificate_987_checked : certificate_987.Valid 14 7 14 certificate_987_q certificate_987_edges 7 5 [] := by decide +kernel
theorem certificate_987_valid : certificate_987.Valid 14 7 (patternOrder [[],[2,1,1,1,2]]) (patternClique [[],[2,1,1,1,2]]) (patternEdges [[],[2,1,1,1,2]]) (patternAmount [[],[2,1,1,1,2]]) (patternEdgeCount [[],[2,1,1,1,2]]) [] := certificate_987_checked

theorem certificate_988_checked : certificate_988.Valid 14 7 11 certificate_988_q certificate_988_edges 4 4 [] := by decide +kernel
theorem certificate_988_valid : certificate_988.Valid 14 7 (patternOrder [[1],[1],[1,1]]) (patternClique [[1],[1],[1,1]]) (patternEdges [[1],[1],[1,1]]) (patternAmount [[1],[1],[1,1]]) (patternEdgeCount [[1],[1],[1,1]]) [] := certificate_988_checked

theorem certificate_989_checked : certificate_989.Valid 14 7 12 certificate_989_q certificate_989_edges 5 4 [] := by decide +kernel
theorem certificate_989_valid : certificate_989.Valid 14 7 (patternOrder [[1],[1],[1,2]]) (patternClique [[1],[1],[1,2]]) (patternEdges [[1],[1],[1,2]]) (patternAmount [[1],[1],[1,2]]) (patternEdgeCount [[1],[1],[1,2]]) [] := certificate_989_checked

theorem certificate_990_checked : certificate_990.Valid 14 7 13 certificate_990_q certificate_990_edges 6 4 [] := by decide +kernel
theorem certificate_990_valid : certificate_990.Valid 14 7 (patternOrder [[1],[1],[1,3]]) (patternClique [[1],[1],[1,3]]) (patternEdges [[1],[1],[1,3]]) (patternAmount [[1],[1],[1,3]]) (patternEdgeCount [[1],[1],[1,3]]) [] := certificate_990_checked

theorem certificate_991_checked : certificate_991.Valid 14 7 14 certificate_991_q certificate_991_edges 7 4 [] := by decide +kernel
theorem certificate_991_valid : certificate_991.Valid 14 7 (patternOrder [[1],[1],[1,4]]) (patternClique [[1],[1],[1,4]]) (patternEdges [[1],[1],[1,4]]) (patternAmount [[1],[1],[1,4]]) (patternEdgeCount [[1],[1],[1,4]]) [] := certificate_991_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates032
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_992_checked : certificate_992.Valid 14 7 13 certificate_992_q certificate_992_edges 6 4 [] := by decide +kernel
theorem certificate_992_valid : certificate_992.Valid 14 7 (patternOrder [[1],[1],[2,2]]) (patternClique [[1],[1],[2,2]]) (patternEdges [[1],[1],[2,2]]) (patternAmount [[1],[1],[2,2]]) (patternEdgeCount [[1],[1],[2,2]]) [] := certificate_992_checked

theorem certificate_993_checked : certificate_993.Valid 14 7 14 certificate_993_q certificate_993_edges 7 4 [] := by decide +kernel
theorem certificate_993_valid : certificate_993.Valid 14 7 (patternOrder [[1],[1],[2,3]]) (patternClique [[1],[1],[2,3]]) (patternEdges [[1],[1],[2,3]]) (patternAmount [[1],[1],[2,3]]) (patternEdgeCount [[1],[1],[2,3]]) [] := certificate_993_checked

theorem certificate_994_checked : certificate_994.Valid 14 7 12 certificate_994_q certificate_994_edges 5 4 [] := by decide +kernel
theorem certificate_994_valid : certificate_994.Valid 14 7 (patternOrder [[1],[1,1],[2]]) (patternClique [[1],[1,1],[2]]) (patternEdges [[1],[1,1],[2]]) (patternAmount [[1],[1,1],[2]]) (patternEdgeCount [[1],[1,1],[2]]) [] := certificate_994_checked

theorem certificate_995_checked : certificate_995.Valid 14 7 13 certificate_995_q certificate_995_edges 6 4 [] := by decide +kernel
theorem certificate_995_valid : certificate_995.Valid 14 7 (patternOrder [[1],[1,1],[3]]) (patternClique [[1],[1,1],[3]]) (patternEdges [[1],[1,1],[3]]) (patternAmount [[1],[1,1],[3]]) (patternEdgeCount [[1],[1,1],[3]]) [] := certificate_995_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates033
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1028_checked : certificate_1028.Valid 14 7 14 certificate_1028_q certificate_1028_edges 7 6 [] := by decide +kernel
theorem certificate_1028_valid : certificate_1028.Valid 14 7 (patternOrder [[1,1,1,2,1,1]]) (patternClique [[1,1,1,2,1,1]]) (patternEdges [[1,1,1,2,1,1]]) (patternAmount [[1,1,1,2,1,1]]) (patternEdgeCount [[1,1,1,2,1,1]]) [] := certificate_1028_checked

theorem certificate_1029_checked : certificate_1029.Valid 14 7 14 certificate_1029_q certificate_1029_edges 7 5 [] := by decide +kernel
theorem certificate_1029_valid : certificate_1029.Valid 14 7 (patternOrder [[1,1,2],[1,2]]) (patternClique [[1,1,2],[1,2]]) (patternEdges [[1,1,2],[1,2]]) (patternAmount [[1,1,2],[1,2]]) (patternEdgeCount [[1,1,2],[1,2]]) [] := certificate_1029_checked

theorem certificate_1030_checked : certificate_1030.Valid 14 7 14 certificate_1030_q certificate_1030_edges 7 5 [] := by decide +kernel
theorem certificate_1030_valid : certificate_1030.Valid 14 7 (patternOrder [[1,1,2,1],[2]]) (patternClique [[1,1,2,1],[2]]) (patternEdges [[1,1,2,1],[2]]) (patternAmount [[1,1,2,1],[2]]) (patternEdgeCount [[1,1,2,1],[2]]) [] := certificate_1030_checked

theorem certificate_1031_checked : certificate_1031.Valid 14 7 14 certificate_1031_q certificate_1031_edges 7 5 [] := by decide +kernel
theorem certificate_1031_valid : certificate_1031.Valid 14 7 (patternOrder [[1,2],[1,2,1]]) (patternClique [[1,2],[1,2,1]]) (patternEdges [[1,2],[1,2,1]]) (patternAmount [[1,2],[1,2,1]]) (patternEdgeCount [[1,2],[1,2,1]]) [] := certificate_1031_checked

theorem certificate_1032_checked : certificate_1032.Valid 14 7 14 certificate_1032_q certificate_1032_edges 7 4 [] := by decide +kernel
theorem certificate_1032_valid : certificate_1032.Valid 14 7 (patternOrder [[1,2],[2],[2]]) (patternClique [[1,2],[2],[2]]) (patternEdges [[1,2],[2],[2]]) (patternAmount [[1,2],[2],[2]]) (patternEdgeCount [[1,2],[2],[2]]) [] := certificate_1032_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns14x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_14_7_2_verified : ∀ D ∈ patterns_14_7_2, PatternVerified 14 7 D := by

  simp only [patterns_14_7_2, List.forall_mem_cons]

  exact ⟨⟨certificate_868, certificate_868_valid⟩, ⟨⟨certificate_869, certificate_869_valid⟩, ⟨⟨certificate_870, certificate_870_valid⟩, ⟨⟨certificate_871, certificate_871_valid⟩, ⟨⟨certificate_872, certificate_872_valid⟩, ⟨⟨certificate_873, certificate_873_valid⟩, ⟨⟨certificate_874, certificate_874_valid⟩, ⟨⟨certificate_875, certificate_875_valid⟩, ⟨⟨certificate_876, certificate_876_valid⟩, ⟨⟨certificate_877, certificate_877_valid⟩, ⟨⟨certificate_878, certificate_878_valid⟩, ⟨⟨certificate_879, certificate_879_valid⟩, ⟨⟨certificate_880, certificate_880_valid⟩, ⟨⟨certificate_881, certificate_881_valid⟩, ⟨⟨certificate_882, certificate_882_valid⟩, ⟨⟨certificate_883, certificate_883_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_7_6_verified : ∀ D ∈ patterns_14_7_6, PatternVerified 14 7 D := by

  simp only [patterns_14_7_6, List.forall_mem_cons]

  exact ⟨⟨certificate_932, certificate_932_valid⟩, ⟨⟨certificate_933, certificate_933_valid⟩, ⟨⟨certificate_934, certificate_934_valid⟩, ⟨⟨certificate_935, certificate_935_valid⟩, ⟨⟨certificate_936, certificate_936_valid⟩, ⟨⟨certificate_937, certificate_937_valid⟩, ⟨⟨certificate_938, certificate_938_valid⟩, ⟨⟨certificate_939, certificate_939_valid⟩, ⟨⟨certificate_940, certificate_940_valid⟩, ⟨⟨certificate_941, certificate_941_valid⟩, ⟨⟨certificate_942, certificate_942_valid⟩, ⟨⟨certificate_943, certificate_943_valid⟩, ⟨⟨certificate_944, certificate_944_valid⟩, ⟨⟨certificate_945, certificate_945_valid⟩, ⟨⟨certificate_946, certificate_946_valid⟩, ⟨⟨certificate_947, certificate_947_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_7_7_verified : ∀ D ∈ patterns_14_7_7, PatternVerified 14 7 D := by

  simp only [patterns_14_7_7, List.forall_mem_cons]

  exact ⟨⟨certificate_948, certificate_948_valid⟩, ⟨⟨certificate_949, certificate_949_valid⟩, ⟨⟨certificate_950, certificate_950_valid⟩, ⟨⟨certificate_951, certificate_951_valid⟩, ⟨⟨certificate_952, certificate_952_valid⟩, ⟨⟨certificate_953, certificate_953_valid⟩, ⟨⟨certificate_954, certificate_954_valid⟩, ⟨⟨certificate_955, certificate_955_valid⟩, ⟨⟨certificate_956, certificate_956_valid⟩, ⟨⟨certificate_957, certificate_957_valid⟩, ⟨⟨certificate_958, certificate_958_valid⟩, ⟨⟨certificate_959, certificate_959_valid⟩, ⟨⟨certificate_960, certificate_960_valid⟩, ⟨⟨certificate_961, certificate_961_valid⟩, ⟨⟨certificate_962, certificate_962_valid⟩, ⟨⟨certificate_963, certificate_963_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_7_8_verified : ∀ D ∈ patterns_14_7_8, PatternVerified 14 7 D := by

  simp only [patterns_14_7_8, List.forall_mem_cons]

  exact ⟨⟨certificate_964, certificate_964_valid⟩, ⟨⟨certificate_965, certificate_965_valid⟩, ⟨⟨certificate_966, certificate_966_valid⟩, ⟨⟨certificate_967, certificate_967_valid⟩, ⟨⟨certificate_968, certificate_968_valid⟩, ⟨⟨certificate_969, certificate_969_valid⟩, ⟨⟨certificate_970, certificate_970_valid⟩, ⟨⟨certificate_971, certificate_971_valid⟩, ⟨⟨certificate_972, certificate_972_valid⟩, ⟨⟨certificate_973, certificate_973_valid⟩, ⟨⟨certificate_974, certificate_974_valid⟩, ⟨⟨certificate_975, certificate_975_valid⟩, ⟨⟨certificate_976, certificate_976_valid⟩, ⟨⟨certificate_977, certificate_977_valid⟩, ⟨⟨certificate_978, certificate_978_valid⟩, ⟨⟨certificate_979, certificate_979_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_7_9_verified : ∀ D ∈ patterns_14_7_9, PatternVerified 14 7 D := by

  simp only [patterns_14_7_9, List.forall_mem_cons]

  exact ⟨⟨certificate_980, certificate_980_valid⟩, ⟨⟨certificate_981, certificate_981_valid⟩, ⟨⟨certificate_982, certificate_982_valid⟩, ⟨⟨certificate_983, certificate_983_valid⟩, ⟨⟨certificate_984, certificate_984_valid⟩, ⟨⟨certificate_985, certificate_985_valid⟩, ⟨⟨certificate_986, certificate_986_valid⟩, ⟨⟨certificate_987, certificate_987_valid⟩, ⟨⟨certificate_988, certificate_988_valid⟩, ⟨⟨certificate_989, certificate_989_valid⟩, ⟨⟨certificate_990, certificate_990_valid⟩, ⟨⟨certificate_991, certificate_991_valid⟩, ⟨⟨certificate_992, certificate_992_valid⟩, ⟨⟨certificate_993, certificate_993_valid⟩, ⟨⟨certificate_994, certificate_994_valid⟩, ⟨⟨certificate_995, certificate_995_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_7_12_verified : ∀ D ∈ patterns_14_7_12, PatternVerified 14 7 D := by

  simp only [patterns_14_7_12, List.forall_mem_cons]

  exact ⟨⟨certificate_1028, certificate_1028_valid⟩, ⟨⟨certificate_1029, certificate_1029_valid⟩, ⟨⟨certificate_1030, certificate_1030_valid⟩, ⟨⟨certificate_1031, certificate_1031_valid⟩, ⟨⟨certificate_1032, certificate_1032_valid⟩, (by simp)⟩⟩⟩⟩⟩

theorem patterns_14_7_verified : ∀ D ∈ patterns_14_7, PatternVerified 14 7 D := by

  simp only [patterns_14_7, List.forall_mem_append]

  exact ⟨patterns_14_7_0_verified, ⟨patterns_14_7_1_verified, ⟨patterns_14_7_2_verified, ⟨patterns_14_7_3_verified, ⟨patterns_14_7_4_verified, ⟨patterns_14_7_5_verified, ⟨patterns_14_7_6_verified, ⟨patterns_14_7_7_verified, ⟨patterns_14_7_8_verified, ⟨patterns_14_7_9_verified, ⟨patterns_14_7_10_verified, ⟨patterns_14_7_11_verified, ⟨patterns_14_7_12_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_7_coverage : patternChoices 7 7 [] = patterns_14_7 := by decide +kernel

theorem finite_patterns_14_7_oai : ∀ D ∈ patternChoices 7 (14-7) [], PatternVerified 14 7 D := by

  rw [patterns_14_7_coverage]

  exact patterns_14_7_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_14_7_oai := @OAI.CycleClique.finite_patterns_14_7_oai
