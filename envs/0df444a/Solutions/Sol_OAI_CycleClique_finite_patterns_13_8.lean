-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_13_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:32:09.990779+00:00
-- url     : https://prove2.me/submissions/088849f3-37e5-401c-a2a8-927e6138bae0

import Mathlib
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates025
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_781_checked : certificate_781.Valid 13 8 8 certificate_781_q certificate_781_edges 0 0 [] := by decide +kernel
theorem certificate_781_valid : certificate_781.Valid 13 8 (patternOrder [[],[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[],[]]) [] := certificate_781_checked

theorem certificate_782_checked : certificate_782.Valid 13 8 9 certificate_782_q certificate_782_edges 1 1 [] := by decide +kernel
theorem certificate_782_valid : certificate_782.Valid 13 8 (patternOrder [[],[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[],[1]]) [] := certificate_782_checked

theorem certificate_783_checked : certificate_783.Valid 13 8 10 certificate_783_q certificate_783_edges 2 1 [] := by decide +kernel
theorem certificate_783_valid : certificate_783.Valid 13 8 (patternOrder [[],[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[],[2]]) [] := certificate_783_checked

theorem certificate_784_checked : certificate_784.Valid 13 8 11 certificate_784_q certificate_784_edges 3 1 [] := by decide +kernel
theorem certificate_784_valid : certificate_784.Valid 13 8 (patternOrder [[],[],[],[],[],[],[3]]) (patternClique [[],[],[],[],[],[],[3]]) (patternEdges [[],[],[],[],[],[],[3]]) (patternAmount [[],[],[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[],[],[3]]) [] := certificate_784_checked

theorem certificate_785_checked : certificate_785.Valid 13 8 12 certificate_785_q certificate_785_edges 4 1 [] := by decide +kernel
theorem certificate_785_valid : certificate_785.Valid 13 8 (patternOrder [[],[],[],[],[],[],[4]]) (patternClique [[],[],[],[],[],[],[4]]) (patternEdges [[],[],[],[],[],[],[4]]) (patternAmount [[],[],[],[],[],[],[4]]) (patternEdgeCount [[],[],[],[],[],[],[4]]) [] := certificate_785_checked

theorem certificate_786_checked : certificate_786.Valid 13 8 13 certificate_786_q certificate_786_edges 5 1 [] := by decide +kernel
theorem certificate_786_valid : certificate_786.Valid 13 8 (patternOrder [[],[],[],[],[],[],[5]]) (patternClique [[],[],[],[],[],[],[5]]) (patternEdges [[],[],[],[],[],[],[5]]) (patternAmount [[],[],[],[],[],[],[5]]) (patternEdgeCount [[],[],[],[],[],[],[5]]) [] := certificate_786_checked

theorem certificate_787_checked : certificate_787.Valid 13 8 10 certificate_787_q certificate_787_edges 2 2 [] := by decide +kernel
theorem certificate_787_valid : certificate_787.Valid 13 8 (patternOrder [[],[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[],[1,1]]) [] := certificate_787_checked

theorem certificate_788_checked : certificate_788.Valid 13 8 11 certificate_788_q certificate_788_edges 3 2 [] := by decide +kernel
theorem certificate_788_valid : certificate_788.Valid 13 8 (patternOrder [[],[],[],[],[],[1,2]]) (patternClique [[],[],[],[],[],[1,2]]) (patternEdges [[],[],[],[],[],[1,2]]) (patternAmount [[],[],[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[],[],[1,2]]) [] := certificate_788_checked

theorem certificate_789_checked : certificate_789.Valid 13 8 12 certificate_789_q certificate_789_edges 4 2 [] := by decide +kernel
theorem certificate_789_valid : certificate_789.Valid 13 8 (patternOrder [[],[],[],[],[],[1,3]]) (patternClique [[],[],[],[],[],[1,3]]) (patternEdges [[],[],[],[],[],[1,3]]) (patternAmount [[],[],[],[],[],[1,3]]) (patternEdgeCount [[],[],[],[],[],[1,3]]) [] := certificate_789_checked

theorem certificate_790_checked : certificate_790.Valid 13 8 13 certificate_790_q certificate_790_edges 5 2 [] := by decide +kernel
theorem certificate_790_valid : certificate_790.Valid 13 8 (patternOrder [[],[],[],[],[],[1,4]]) (patternClique [[],[],[],[],[],[1,4]]) (patternEdges [[],[],[],[],[],[1,4]]) (patternAmount [[],[],[],[],[],[1,4]]) (patternEdgeCount [[],[],[],[],[],[1,4]]) [] := certificate_790_checked

theorem certificate_791_checked : certificate_791.Valid 13 8 12 certificate_791_q certificate_791_edges 4 2 [] := by decide +kernel
theorem certificate_791_valid : certificate_791.Valid 13 8 (patternOrder [[],[],[],[],[],[2,2]]) (patternClique [[],[],[],[],[],[2,2]]) (patternEdges [[],[],[],[],[],[2,2]]) (patternAmount [[],[],[],[],[],[2,2]]) (patternEdgeCount [[],[],[],[],[],[2,2]]) [] := certificate_791_checked

theorem certificate_792_checked : certificate_792.Valid 13 8 13 certificate_792_q certificate_792_edges 5 2 [] := by decide +kernel
theorem certificate_792_valid : certificate_792.Valid 13 8 (patternOrder [[],[],[],[],[],[2,3]]) (patternClique [[],[],[],[],[],[2,3]]) (patternEdges [[],[],[],[],[],[2,3]]) (patternAmount [[],[],[],[],[],[2,3]]) (patternEdgeCount [[],[],[],[],[],[2,3]]) [] := certificate_792_checked

theorem certificate_793_checked : certificate_793.Valid 13 8 10 certificate_793_q certificate_793_edges 2 2 [] := by decide +kernel
theorem certificate_793_valid : certificate_793.Valid 13 8 (patternOrder [[],[],[],[],[1],[1]]) (patternClique [[],[],[],[],[1],[1]]) (patternEdges [[],[],[],[],[1],[1]]) (patternAmount [[],[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[],[1],[1]]) [] := certificate_793_checked

theorem certificate_794_checked : certificate_794.Valid 13 8 11 certificate_794_q certificate_794_edges 3 2 [] := by decide +kernel
theorem certificate_794_valid : certificate_794.Valid 13 8 (patternOrder [[],[],[],[],[1],[2]]) (patternClique [[],[],[],[],[1],[2]]) (patternEdges [[],[],[],[],[1],[2]]) (patternAmount [[],[],[],[],[1],[2]]) (patternEdgeCount [[],[],[],[],[1],[2]]) [] := certificate_794_checked

theorem certificate_795_checked : certificate_795.Valid 13 8 12 certificate_795_q certificate_795_edges 4 2 [] := by decide +kernel
theorem certificate_795_valid : certificate_795.Valid 13 8 (patternOrder [[],[],[],[],[1],[3]]) (patternClique [[],[],[],[],[1],[3]]) (patternEdges [[],[],[],[],[1],[3]]) (patternAmount [[],[],[],[],[1],[3]]) (patternEdgeCount [[],[],[],[],[1],[3]]) [] := certificate_795_checked

theorem certificate_796_checked : certificate_796.Valid 13 8 13 certificate_796_q certificate_796_edges 5 2 [] := by decide +kernel
theorem certificate_796_valid : certificate_796.Valid 13 8 (patternOrder [[],[],[],[],[1],[4]]) (patternClique [[],[],[],[],[1],[4]]) (patternEdges [[],[],[],[],[1],[4]]) (patternAmount [[],[],[],[],[1],[4]]) (patternEdgeCount [[],[],[],[],[1],[4]]) [] := certificate_796_checked

theorem certificate_797_checked : certificate_797.Valid 13 8 11 certificate_797_q certificate_797_edges 3 3 [] := by decide +kernel
theorem certificate_797_valid : certificate_797.Valid 13 8 (patternOrder [[],[],[],[],[1,1,1]]) (patternClique [[],[],[],[],[1,1,1]]) (patternEdges [[],[],[],[],[1,1,1]]) (patternAmount [[],[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[],[1,1,1]]) [] := certificate_797_checked

theorem certificate_798_checked : certificate_798.Valid 13 8 12 certificate_798_q certificate_798_edges 4 3 [] := by decide +kernel
theorem certificate_798_valid : certificate_798.Valid 13 8 (patternOrder [[],[],[],[],[1,1,2]]) (patternClique [[],[],[],[],[1,1,2]]) (patternEdges [[],[],[],[],[1,1,2]]) (patternAmount [[],[],[],[],[1,1,2]]) (patternEdgeCount [[],[],[],[],[1,1,2]]) [] := certificate_798_checked

theorem certificate_799_checked : certificate_799.Valid 13 8 13 certificate_799_q certificate_799_edges 5 3 [] := by decide +kernel
theorem certificate_799_valid : certificate_799.Valid 13 8 (patternOrder [[],[],[],[],[1,1,3]]) (patternClique [[],[],[],[],[1,1,3]]) (patternEdges [[],[],[],[],[1,1,3]]) (patternAmount [[],[],[],[],[1,1,3]]) (patternEdgeCount [[],[],[],[],[1,1,3]]) [] := certificate_799_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates026
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_800_checked : certificate_800.Valid 13 8 12 certificate_800_q certificate_800_edges 4 3 [] := by decide +kernel
theorem certificate_800_valid : certificate_800.Valid 13 8 (patternOrder [[],[],[],[],[1,2,1]]) (patternClique [[],[],[],[],[1,2,1]]) (patternEdges [[],[],[],[],[1,2,1]]) (patternAmount [[],[],[],[],[1,2,1]]) (patternEdgeCount [[],[],[],[],[1,2,1]]) [] := certificate_800_checked

theorem certificate_801_checked : certificate_801.Valid 13 8 13 certificate_801_q certificate_801_edges 5 3 [] := by decide +kernel
theorem certificate_801_valid : certificate_801.Valid 13 8 (patternOrder [[],[],[],[],[1,2,2]]) (patternClique [[],[],[],[],[1,2,2]]) (patternEdges [[],[],[],[],[1,2,2]]) (patternAmount [[],[],[],[],[1,2,2]]) (patternEdgeCount [[],[],[],[],[1,2,2]]) [] := certificate_801_checked

theorem certificate_802_checked : certificate_802.Valid 13 8 13 certificate_802_q certificate_802_edges 5 3 [] := by decide +kernel
theorem certificate_802_valid : certificate_802.Valid 13 8 (patternOrder [[],[],[],[],[1,3,1]]) (patternClique [[],[],[],[],[1,3,1]]) (patternEdges [[],[],[],[],[1,3,1]]) (patternAmount [[],[],[],[],[1,3,1]]) (patternEdgeCount [[],[],[],[],[1,3,1]]) [] := certificate_802_checked

theorem certificate_803_checked : certificate_803.Valid 13 8 12 certificate_803_q certificate_803_edges 4 2 [] := by decide +kernel
theorem certificate_803_valid : certificate_803.Valid 13 8 (patternOrder [[],[],[],[],[2],[2]]) (patternClique [[],[],[],[],[2],[2]]) (patternEdges [[],[],[],[],[2],[2]]) (patternAmount [[],[],[],[],[2],[2]]) (patternEdgeCount [[],[],[],[],[2],[2]]) [] := certificate_803_checked

theorem certificate_804_checked : certificate_804.Valid 13 8 13 certificate_804_q certificate_804_edges 5 2 [] := by decide +kernel
theorem certificate_804_valid : certificate_804.Valid 13 8 (patternOrder [[],[],[],[],[2],[3]]) (patternClique [[],[],[],[],[2],[3]]) (patternEdges [[],[],[],[],[2],[3]]) (patternAmount [[],[],[],[],[2],[3]]) (patternEdgeCount [[],[],[],[],[2],[3]]) [] := certificate_804_checked

theorem certificate_805_checked : certificate_805.Valid 13 8 13 certificate_805_q certificate_805_edges 5 3 [] := by decide +kernel
theorem certificate_805_valid : certificate_805.Valid 13 8 (patternOrder [[],[],[],[],[2,1,2]]) (patternClique [[],[],[],[],[2,1,2]]) (patternEdges [[],[],[],[],[2,1,2]]) (patternAmount [[],[],[],[],[2,1,2]]) (patternEdgeCount [[],[],[],[],[2,1,2]]) [] := certificate_805_checked

theorem certificate_806_checked : certificate_806.Valid 13 8 11 certificate_806_q certificate_806_edges 3 3 [] := by decide +kernel
theorem certificate_806_valid : certificate_806.Valid 13 8 (patternOrder [[],[],[],[1],[1,1]]) (patternClique [[],[],[],[1],[1,1]]) (patternEdges [[],[],[],[1],[1,1]]) (patternAmount [[],[],[],[1],[1,1]]) (patternEdgeCount [[],[],[],[1],[1,1]]) [] := certificate_806_checked

theorem certificate_807_checked : certificate_807.Valid 13 8 12 certificate_807_q certificate_807_edges 4 3 [] := by decide +kernel
theorem certificate_807_valid : certificate_807.Valid 13 8 (patternOrder [[],[],[],[1],[1,2]]) (patternClique [[],[],[],[1],[1,2]]) (patternEdges [[],[],[],[1],[1,2]]) (patternAmount [[],[],[],[1],[1,2]]) (patternEdgeCount [[],[],[],[1],[1,2]]) [] := certificate_807_checked

theorem certificate_808_checked : certificate_808.Valid 13 8 13 certificate_808_q certificate_808_edges 5 3 [] := by decide +kernel
theorem certificate_808_valid : certificate_808.Valid 13 8 (patternOrder [[],[],[],[1],[1,3]]) (patternClique [[],[],[],[1],[1,3]]) (patternEdges [[],[],[],[1],[1,3]]) (patternAmount [[],[],[],[1],[1,3]]) (patternEdgeCount [[],[],[],[1],[1,3]]) [] := certificate_808_checked

theorem certificate_809_checked : certificate_809.Valid 13 8 13 certificate_809_q certificate_809_edges 5 3 [] := by decide +kernel
theorem certificate_809_valid : certificate_809.Valid 13 8 (patternOrder [[],[],[],[1],[2,2]]) (patternClique [[],[],[],[1],[2,2]]) (patternEdges [[],[],[],[1],[2,2]]) (patternAmount [[],[],[],[1],[2,2]]) (patternEdgeCount [[],[],[],[1],[2,2]]) [] := certificate_809_checked

theorem certificate_810_checked : certificate_810.Valid 13 8 12 certificate_810_q certificate_810_edges 4 3 [] := by decide +kernel
theorem certificate_810_valid : certificate_810.Valid 13 8 (patternOrder [[],[],[],[1,1],[2]]) (patternClique [[],[],[],[1,1],[2]]) (patternEdges [[],[],[],[1,1],[2]]) (patternAmount [[],[],[],[1,1],[2]]) (patternEdgeCount [[],[],[],[1,1],[2]]) [] := certificate_810_checked

theorem certificate_811_checked : certificate_811.Valid 13 8 13 certificate_811_q certificate_811_edges 5 3 [] := by decide +kernel
theorem certificate_811_valid : certificate_811.Valid 13 8 (patternOrder [[],[],[],[1,1],[3]]) (patternClique [[],[],[],[1,1],[3]]) (patternEdges [[],[],[],[1,1],[3]]) (patternAmount [[],[],[],[1,1],[3]]) (patternEdgeCount [[],[],[],[1,1],[3]]) [] := certificate_811_checked

theorem certificate_812_checked : certificate_812.Valid 13 8 12 certificate_812_q certificate_812_edges 4 4 [] := by decide +kernel
theorem certificate_812_valid : certificate_812.Valid 13 8 (patternOrder [[],[],[],[1,1,1,1]]) (patternClique [[],[],[],[1,1,1,1]]) (patternEdges [[],[],[],[1,1,1,1]]) (patternAmount [[],[],[],[1,1,1,1]]) (patternEdgeCount [[],[],[],[1,1,1,1]]) [] := certificate_812_checked

theorem certificate_813_checked : certificate_813.Valid 13 8 13 certificate_813_q certificate_813_edges 5 4 [] := by decide +kernel
theorem certificate_813_valid : certificate_813.Valid 13 8 (patternOrder [[],[],[],[1,1,1,2]]) (patternClique [[],[],[],[1,1,1,2]]) (patternEdges [[],[],[],[1,1,1,2]]) (patternAmount [[],[],[],[1,1,1,2]]) (patternEdgeCount [[],[],[],[1,1,1,2]]) [] := certificate_813_checked

theorem certificate_814_checked : certificate_814.Valid 13 8 13 certificate_814_q certificate_814_edges 5 4 [] := by decide +kernel
theorem certificate_814_valid : certificate_814.Valid 13 8 (patternOrder [[],[],[],[1,1,2,1]]) (patternClique [[],[],[],[1,1,2,1]]) (patternEdges [[],[],[],[1,1,2,1]]) (patternAmount [[],[],[],[1,1,2,1]]) (patternEdgeCount [[],[],[],[1,1,2,1]]) [] := certificate_814_checked

theorem certificate_815_checked : certificate_815.Valid 13 8 13 certificate_815_q certificate_815_edges 5 3 [] := by decide +kernel
theorem certificate_815_valid : certificate_815.Valid 13 8 (patternOrder [[],[],[],[1,2],[2]]) (patternClique [[],[],[],[1,2],[2]]) (patternEdges [[],[],[],[1,2],[2]]) (patternAmount [[],[],[],[1,2],[2]]) (patternEdgeCount [[],[],[],[1,2],[2]]) [] := certificate_815_checked

theorem certificate_816_checked : certificate_816.Valid 13 8 11 certificate_816_q certificate_816_edges 3 3 [] := by decide +kernel
theorem certificate_816_valid : certificate_816.Valid 13 8 (patternOrder [[],[],[1],[1],[1]]) (patternClique [[],[],[1],[1],[1]]) (patternEdges [[],[],[1],[1],[1]]) (patternAmount [[],[],[1],[1],[1]]) (patternEdgeCount [[],[],[1],[1],[1]]) [] := certificate_816_checked

theorem certificate_817_checked : certificate_817.Valid 13 8 12 certificate_817_q certificate_817_edges 4 3 [] := by decide +kernel
theorem certificate_817_valid : certificate_817.Valid 13 8 (patternOrder [[],[],[1],[1],[2]]) (patternClique [[],[],[1],[1],[2]]) (patternEdges [[],[],[1],[1],[2]]) (patternAmount [[],[],[1],[1],[2]]) (patternEdgeCount [[],[],[1],[1],[2]]) [] := certificate_817_checked

theorem certificate_818_checked : certificate_818.Valid 13 8 13 certificate_818_q certificate_818_edges 5 3 [] := by decide +kernel
theorem certificate_818_valid : certificate_818.Valid 13 8 (patternOrder [[],[],[1],[1],[3]]) (patternClique [[],[],[1],[1],[3]]) (patternEdges [[],[],[1],[1],[3]]) (patternAmount [[],[],[1],[1],[3]]) (patternEdgeCount [[],[],[1],[1],[3]]) [] := certificate_818_checked

theorem certificate_819_checked : certificate_819.Valid 13 8 12 certificate_819_q certificate_819_edges 4 4 [] := by decide +kernel
theorem certificate_819_valid : certificate_819.Valid 13 8 (patternOrder [[],[],[1],[1,1,1]]) (patternClique [[],[],[1],[1,1,1]]) (patternEdges [[],[],[1],[1,1,1]]) (patternAmount [[],[],[1],[1,1,1]]) (patternEdgeCount [[],[],[1],[1,1,1]]) [] := certificate_819_checked

theorem certificate_820_checked : certificate_820.Valid 13 8 13 certificate_820_q certificate_820_edges 5 4 [] := by decide +kernel
theorem certificate_820_valid : certificate_820.Valid 13 8 (patternOrder [[],[],[1],[1,1,2]]) (patternClique [[],[],[1],[1,1,2]]) (patternEdges [[],[],[1],[1,1,2]]) (patternAmount [[],[],[1],[1,1,2]]) (patternEdgeCount [[],[],[1],[1,1,2]]) [] := certificate_820_checked

theorem certificate_821_checked : certificate_821.Valid 13 8 13 certificate_821_q certificate_821_edges 5 4 [] := by decide +kernel
theorem certificate_821_valid : certificate_821.Valid 13 8 (patternOrder [[],[],[1],[1,2,1]]) (patternClique [[],[],[1],[1,2,1]]) (patternEdges [[],[],[1],[1,2,1]]) (patternAmount [[],[],[1],[1,2,1]]) (patternEdgeCount [[],[],[1],[1,2,1]]) [] := certificate_821_checked

theorem certificate_822_checked : certificate_822.Valid 13 8 13 certificate_822_q certificate_822_edges 5 3 [] := by decide +kernel
theorem certificate_822_valid : certificate_822.Valid 13 8 (patternOrder [[],[],[1],[2],[2]]) (patternClique [[],[],[1],[2],[2]]) (patternEdges [[],[],[1],[2],[2]]) (patternAmount [[],[],[1],[2],[2]]) (patternEdgeCount [[],[],[1],[2],[2]]) [] := certificate_822_checked

theorem certificate_823_checked : certificate_823.Valid 13 8 12 certificate_823_q certificate_823_edges 4 4 [] := by decide +kernel
theorem certificate_823_valid : certificate_823.Valid 13 8 (patternOrder [[],[],[1,1],[1,1]]) (patternClique [[],[],[1,1],[1,1]]) (patternEdges [[],[],[1,1],[1,1]]) (patternAmount [[],[],[1,1],[1,1]]) (patternEdgeCount [[],[],[1,1],[1,1]]) [] := certificate_823_checked

theorem certificate_824_checked : certificate_824.Valid 13 8 13 certificate_824_q certificate_824_edges 5 4 [] := by decide +kernel
theorem certificate_824_valid : certificate_824.Valid 13 8 (patternOrder [[],[],[1,1],[1,2]]) (patternClique [[],[],[1,1],[1,2]]) (patternEdges [[],[],[1,1],[1,2]]) (patternAmount [[],[],[1,1],[1,2]]) (patternEdgeCount [[],[],[1,1],[1,2]]) [] := certificate_824_checked

theorem certificate_825_checked : certificate_825.Valid 13 8 13 certificate_825_q certificate_825_edges 5 4 [] := by decide +kernel
theorem certificate_825_valid : certificate_825.Valid 13 8 (patternOrder [[],[],[1,1,1],[2]]) (patternClique [[],[],[1,1,1],[2]]) (patternEdges [[],[],[1,1,1],[2]]) (patternAmount [[],[],[1,1,1],[2]]) (patternEdgeCount [[],[],[1,1,1],[2]]) [] := certificate_825_checked

theorem certificate_826_checked : certificate_826.Valid 13 8 13 certificate_826_q certificate_826_edges 5 5 [] := by decide +kernel
theorem certificate_826_valid : certificate_826.Valid 13 8 (patternOrder [[],[],[1,1,1,1,1]]) (patternClique [[],[],[1,1,1,1,1]]) (patternEdges [[],[],[1,1,1,1,1]]) (patternAmount [[],[],[1,1,1,1,1]]) (patternEdgeCount [[],[],[1,1,1,1,1]]) [] := certificate_826_checked

theorem certificate_827_checked : certificate_827.Valid 13 8 12 certificate_827_q certificate_827_edges 4 4 [] := by decide +kernel
theorem certificate_827_valid : certificate_827.Valid 13 8 (patternOrder [[],[1],[1],[1,1]]) (patternClique [[],[1],[1],[1,1]]) (patternEdges [[],[1],[1],[1,1]]) (patternAmount [[],[1],[1],[1,1]]) (patternEdgeCount [[],[1],[1],[1,1]]) [] := certificate_827_checked

theorem certificate_828_checked : certificate_828.Valid 13 8 13 certificate_828_q certificate_828_edges 5 4 [] := by decide +kernel
theorem certificate_828_valid : certificate_828.Valid 13 8 (patternOrder [[],[1],[1],[1,2]]) (patternClique [[],[1],[1],[1,2]]) (patternEdges [[],[1],[1],[1,2]]) (patternAmount [[],[1],[1],[1,2]]) (patternEdgeCount [[],[1],[1],[1,2]]) [] := certificate_828_checked

theorem certificate_829_checked : certificate_829.Valid 13 8 13 certificate_829_q certificate_829_edges 5 4 [] := by decide +kernel
theorem certificate_829_valid : certificate_829.Valid 13 8 (patternOrder [[],[1],[1,1],[2]]) (patternClique [[],[1],[1,1],[2]]) (patternEdges [[],[1],[1,1],[2]]) (patternAmount [[],[1],[1,1],[2]]) (patternEdgeCount [[],[1],[1,1],[2]]) [] := certificate_829_checked

theorem certificate_830_checked : certificate_830.Valid 13 8 13 certificate_830_q certificate_830_edges 5 5 [] := by decide +kernel
theorem certificate_830_valid : certificate_830.Valid 13 8 (patternOrder [[],[1],[1,1,1,1]]) (patternClique [[],[1],[1,1,1,1]]) (patternEdges [[],[1],[1,1,1,1]]) (patternAmount [[],[1],[1,1,1,1]]) (patternEdgeCount [[],[1],[1,1,1,1]]) [] := certificate_830_checked

theorem certificate_831_checked : certificate_831.Valid 13 8 13 certificate_831_q certificate_831_edges 5 5 [] := by decide +kernel
theorem certificate_831_valid : certificate_831.Valid 13 8 (patternOrder [[],[1,1],[1,1,1]]) (patternClique [[],[1,1],[1,1,1]]) (patternEdges [[],[1,1],[1,1,1]]) (patternAmount [[],[1,1],[1,1,1]]) (patternEdgeCount [[],[1,1],[1,1,1]]) [] := certificate_831_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates027
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_832_checked : certificate_832.Valid 13 8 12 certificate_832_q certificate_832_edges 4 4 [] := by decide +kernel
theorem certificate_832_valid : certificate_832.Valid 13 8 (patternOrder [[1],[1],[1],[1]]) (patternClique [[1],[1],[1],[1]]) (patternEdges [[1],[1],[1],[1]]) (patternAmount [[1],[1],[1],[1]]) (patternEdgeCount [[1],[1],[1],[1]]) [] := certificate_832_checked

theorem certificate_833_checked : certificate_833.Valid 13 8 13 certificate_833_q certificate_833_edges 5 4 [] := by decide +kernel
theorem certificate_833_valid : certificate_833.Valid 13 8 (patternOrder [[1],[1],[1],[2]]) (patternClique [[1],[1],[1],[2]]) (patternEdges [[1],[1],[1],[2]]) (patternAmount [[1],[1],[1],[2]]) (patternEdgeCount [[1],[1],[1],[2]]) [] := certificate_833_checked

theorem certificate_834_checked : certificate_834.Valid 13 8 13 certificate_834_q certificate_834_edges 5 5 [] := by decide +kernel
theorem certificate_834_valid : certificate_834.Valid 13 8 (patternOrder [[1],[1],[1,1,1]]) (patternClique [[1],[1],[1,1,1]]) (patternEdges [[1],[1],[1,1,1]]) (patternAmount [[1],[1],[1,1,1]]) (patternEdgeCount [[1],[1],[1,1,1]]) [] := certificate_834_checked

theorem certificate_835_checked : certificate_835.Valid 13 8 13 certificate_835_q certificate_835_edges 5 5 [] := by decide +kernel
theorem certificate_835_valid : certificate_835.Valid 13 8 (patternOrder [[1],[1,1],[1,1]]) (patternClique [[1],[1,1],[1,1]]) (patternEdges [[1],[1,1],[1,1]]) (patternAmount [[1],[1,1],[1,1]]) (patternEdgeCount [[1],[1,1],[1,1]]) [] := certificate_835_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns13x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_13_8_0_verified : ∀ D ∈ patterns_13_8_0, PatternVerified 13 8 D := by

  simp only [patterns_13_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_781, certificate_781_valid⟩, ⟨⟨certificate_782, certificate_782_valid⟩, ⟨⟨certificate_783, certificate_783_valid⟩, ⟨⟨certificate_784, certificate_784_valid⟩, ⟨⟨certificate_785, certificate_785_valid⟩, ⟨⟨certificate_786, certificate_786_valid⟩, ⟨⟨certificate_787, certificate_787_valid⟩, ⟨⟨certificate_788, certificate_788_valid⟩, ⟨⟨certificate_789, certificate_789_valid⟩, ⟨⟨certificate_790, certificate_790_valid⟩, ⟨⟨certificate_791, certificate_791_valid⟩, ⟨⟨certificate_792, certificate_792_valid⟩, ⟨⟨certificate_793, certificate_793_valid⟩, ⟨⟨certificate_794, certificate_794_valid⟩, ⟨⟨certificate_795, certificate_795_valid⟩, ⟨⟨certificate_796, certificate_796_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_8_1_verified : ∀ D ∈ patterns_13_8_1, PatternVerified 13 8 D := by

  simp only [patterns_13_8_1, List.forall_mem_cons]

  exact ⟨⟨certificate_797, certificate_797_valid⟩, ⟨⟨certificate_798, certificate_798_valid⟩, ⟨⟨certificate_799, certificate_799_valid⟩, ⟨⟨certificate_800, certificate_800_valid⟩, ⟨⟨certificate_801, certificate_801_valid⟩, ⟨⟨certificate_802, certificate_802_valid⟩, ⟨⟨certificate_803, certificate_803_valid⟩, ⟨⟨certificate_804, certificate_804_valid⟩, ⟨⟨certificate_805, certificate_805_valid⟩, ⟨⟨certificate_806, certificate_806_valid⟩, ⟨⟨certificate_807, certificate_807_valid⟩, ⟨⟨certificate_808, certificate_808_valid⟩, ⟨⟨certificate_809, certificate_809_valid⟩, ⟨⟨certificate_810, certificate_810_valid⟩, ⟨⟨certificate_811, certificate_811_valid⟩, ⟨⟨certificate_812, certificate_812_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_8_2_verified : ∀ D ∈ patterns_13_8_2, PatternVerified 13 8 D := by

  simp only [patterns_13_8_2, List.forall_mem_cons]

  exact ⟨⟨certificate_813, certificate_813_valid⟩, ⟨⟨certificate_814, certificate_814_valid⟩, ⟨⟨certificate_815, certificate_815_valid⟩, ⟨⟨certificate_816, certificate_816_valid⟩, ⟨⟨certificate_817, certificate_817_valid⟩, ⟨⟨certificate_818, certificate_818_valid⟩, ⟨⟨certificate_819, certificate_819_valid⟩, ⟨⟨certificate_820, certificate_820_valid⟩, ⟨⟨certificate_821, certificate_821_valid⟩, ⟨⟨certificate_822, certificate_822_valid⟩, ⟨⟨certificate_823, certificate_823_valid⟩, ⟨⟨certificate_824, certificate_824_valid⟩, ⟨⟨certificate_825, certificate_825_valid⟩, ⟨⟨certificate_826, certificate_826_valid⟩, ⟨⟨certificate_827, certificate_827_valid⟩, ⟨⟨certificate_828, certificate_828_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_8_3_verified : ∀ D ∈ patterns_13_8_3, PatternVerified 13 8 D := by

  simp only [patterns_13_8_3, List.forall_mem_cons]

  exact ⟨⟨certificate_829, certificate_829_valid⟩, ⟨⟨certificate_830, certificate_830_valid⟩, ⟨⟨certificate_831, certificate_831_valid⟩, ⟨⟨certificate_832, certificate_832_valid⟩, ⟨⟨certificate_833, certificate_833_valid⟩, ⟨⟨certificate_834, certificate_834_valid⟩, ⟨⟨certificate_835, certificate_835_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_8_verified : ∀ D ∈ patterns_13_8, PatternVerified 13 8 D := by

  simp only [patterns_13_8, List.forall_mem_append]

  exact ⟨patterns_13_8_0_verified, ⟨patterns_13_8_1_verified, ⟨patterns_13_8_2_verified, ⟨patterns_13_8_3_verified, by simp⟩⟩⟩⟩

theorem patterns_13_8_coverage : patternChoices 8 5 [] = patterns_13_8 := by decide +kernel

theorem finite_patterns_13_8_oai : ∀ D ∈ patternChoices 8 (13-8) [], PatternVerified 13 8 D := by

  rw [patterns_13_8_coverage]

  exact patterns_13_8_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_13_8_oai := @OAI.CycleClique.finite_patterns_13_8_oai
