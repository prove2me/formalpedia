-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_13_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:15:56.644882+00:00
-- url     : https://prove2.me/submissions/689a39bd-5aeb-45cd-8da1-9f2c5bb6a40e

import Mathlib
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates022
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_677_checked : certificate_677.Valid 13 7 7 certificate_677_q certificate_677_edges 0 0 [] := by decide +kernel
theorem certificate_677_valid : certificate_677.Valid 13 7 (patternOrder [[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[]]) [] := certificate_677_checked

theorem certificate_678_checked : certificate_678.Valid 13 7 8 certificate_678_q certificate_678_edges 1 1 [] := by decide +kernel
theorem certificate_678_valid : certificate_678.Valid 13 7 (patternOrder [[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[1]]) [] := certificate_678_checked

theorem certificate_679_checked : certificate_679.Valid 13 7 9 certificate_679_q certificate_679_edges 2 1 [] := by decide +kernel
theorem certificate_679_valid : certificate_679.Valid 13 7 (patternOrder [[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[2]]) [] := certificate_679_checked

theorem certificate_680_checked : certificate_680.Valid 13 7 10 certificate_680_q certificate_680_edges 3 1 [] := by decide +kernel
theorem certificate_680_valid : certificate_680.Valid 13 7 (patternOrder [[],[],[],[],[],[3]]) (patternClique [[],[],[],[],[],[3]]) (patternEdges [[],[],[],[],[],[3]]) (patternAmount [[],[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[],[3]]) [] := certificate_680_checked

theorem certificate_681_checked : certificate_681.Valid 13 7 11 certificate_681_q certificate_681_edges 4 1 [] := by decide +kernel
theorem certificate_681_valid : certificate_681.Valid 13 7 (patternOrder [[],[],[],[],[],[4]]) (patternClique [[],[],[],[],[],[4]]) (patternEdges [[],[],[],[],[],[4]]) (patternAmount [[],[],[],[],[],[4]]) (patternEdgeCount [[],[],[],[],[],[4]]) [] := certificate_681_checked

theorem certificate_682_checked : certificate_682.Valid 13 7 12 certificate_682_q certificate_682_edges 5 1 [] := by decide +kernel
theorem certificate_682_valid : certificate_682.Valid 13 7 (patternOrder [[],[],[],[],[],[5]]) (patternClique [[],[],[],[],[],[5]]) (patternEdges [[],[],[],[],[],[5]]) (patternAmount [[],[],[],[],[],[5]]) (patternEdgeCount [[],[],[],[],[],[5]]) [] := certificate_682_checked

theorem certificate_683_checked : certificate_683.Valid 13 7 13 certificate_683_q certificate_683_edges 6 1 [] := by decide +kernel
theorem certificate_683_valid : certificate_683.Valid 13 7 (patternOrder [[],[],[],[],[],[6]]) (patternClique [[],[],[],[],[],[6]]) (patternEdges [[],[],[],[],[],[6]]) (patternAmount [[],[],[],[],[],[6]]) (patternEdgeCount [[],[],[],[],[],[6]]) [] := certificate_683_checked

theorem certificate_684_checked : certificate_684.Valid 13 7 9 certificate_684_q certificate_684_edges 2 2 [] := by decide +kernel
theorem certificate_684_valid : certificate_684.Valid 13 7 (patternOrder [[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[1,1]]) [] := certificate_684_checked

theorem certificate_685_checked : certificate_685.Valid 13 7 10 certificate_685_q certificate_685_edges 3 2 [] := by decide +kernel
theorem certificate_685_valid : certificate_685.Valid 13 7 (patternOrder [[],[],[],[],[1,2]]) (patternClique [[],[],[],[],[1,2]]) (patternEdges [[],[],[],[],[1,2]]) (patternAmount [[],[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[],[1,2]]) [] := certificate_685_checked

theorem certificate_686_checked : certificate_686.Valid 13 7 11 certificate_686_q certificate_686_edges 4 2 [] := by decide +kernel
theorem certificate_686_valid : certificate_686.Valid 13 7 (patternOrder [[],[],[],[],[1,3]]) (patternClique [[],[],[],[],[1,3]]) (patternEdges [[],[],[],[],[1,3]]) (patternAmount [[],[],[],[],[1,3]]) (patternEdgeCount [[],[],[],[],[1,3]]) [] := certificate_686_checked

theorem certificate_687_checked : certificate_687.Valid 13 7 12 certificate_687_q certificate_687_edges 5 2 [] := by decide +kernel
theorem certificate_687_valid : certificate_687.Valid 13 7 (patternOrder [[],[],[],[],[1,4]]) (patternClique [[],[],[],[],[1,4]]) (patternEdges [[],[],[],[],[1,4]]) (patternAmount [[],[],[],[],[1,4]]) (patternEdgeCount [[],[],[],[],[1,4]]) [] := certificate_687_checked

theorem certificate_688_checked : certificate_688.Valid 13 7 13 certificate_688_q certificate_688_edges 6 2 [] := by decide +kernel
theorem certificate_688_valid : certificate_688.Valid 13 7 (patternOrder [[],[],[],[],[1,5]]) (patternClique [[],[],[],[],[1,5]]) (patternEdges [[],[],[],[],[1,5]]) (patternAmount [[],[],[],[],[1,5]]) (patternEdgeCount [[],[],[],[],[1,5]]) [] := certificate_688_checked

theorem certificate_689_checked : certificate_689.Valid 13 7 11 certificate_689_q certificate_689_edges 4 2 [] := by decide +kernel
theorem certificate_689_valid : certificate_689.Valid 13 7 (patternOrder [[],[],[],[],[2,2]]) (patternClique [[],[],[],[],[2,2]]) (patternEdges [[],[],[],[],[2,2]]) (patternAmount [[],[],[],[],[2,2]]) (patternEdgeCount [[],[],[],[],[2,2]]) [] := certificate_689_checked

theorem certificate_690_checked : certificate_690.Valid 13 7 12 certificate_690_q certificate_690_edges 5 2 [] := by decide +kernel
theorem certificate_690_valid : certificate_690.Valid 13 7 (patternOrder [[],[],[],[],[2,3]]) (patternClique [[],[],[],[],[2,3]]) (patternEdges [[],[],[],[],[2,3]]) (patternAmount [[],[],[],[],[2,3]]) (patternEdgeCount [[],[],[],[],[2,3]]) [] := certificate_690_checked

theorem certificate_691_checked : certificate_691.Valid 13 7 13 certificate_691_q certificate_691_edges 6 2 [] := by decide +kernel
theorem certificate_691_valid : certificate_691.Valid 13 7 (patternOrder [[],[],[],[],[2,4]]) (patternClique [[],[],[],[],[2,4]]) (patternEdges [[],[],[],[],[2,4]]) (patternAmount [[],[],[],[],[2,4]]) (patternEdgeCount [[],[],[],[],[2,4]]) [] := certificate_691_checked

theorem certificate_692_checked : certificate_692.Valid 13 7 13 certificate_692_q certificate_692_edges 6 2 [] := by decide +kernel
theorem certificate_692_valid : certificate_692.Valid 13 7 (patternOrder [[],[],[],[],[3,3]]) (patternClique [[],[],[],[],[3,3]]) (patternEdges [[],[],[],[],[3,3]]) (patternAmount [[],[],[],[],[3,3]]) (patternEdgeCount [[],[],[],[],[3,3]]) [] := certificate_692_checked

theorem certificate_693_checked : certificate_693.Valid 13 7 9 certificate_693_q certificate_693_edges 2 2 [] := by decide +kernel
theorem certificate_693_valid : certificate_693.Valid 13 7 (patternOrder [[],[],[],[1],[1]]) (patternClique [[],[],[],[1],[1]]) (patternEdges [[],[],[],[1],[1]]) (patternAmount [[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[1],[1]]) [] := certificate_693_checked

theorem certificate_694_checked : certificate_694.Valid 13 7 10 certificate_694_q certificate_694_edges 3 2 [] := by decide +kernel
theorem certificate_694_valid : certificate_694.Valid 13 7 (patternOrder [[],[],[],[1],[2]]) (patternClique [[],[],[],[1],[2]]) (patternEdges [[],[],[],[1],[2]]) (patternAmount [[],[],[],[1],[2]]) (patternEdgeCount [[],[],[],[1],[2]]) [] := certificate_694_checked

theorem certificate_695_checked : certificate_695.Valid 13 7 11 certificate_695_q certificate_695_edges 4 2 [] := by decide +kernel
theorem certificate_695_valid : certificate_695.Valid 13 7 (patternOrder [[],[],[],[1],[3]]) (patternClique [[],[],[],[1],[3]]) (patternEdges [[],[],[],[1],[3]]) (patternAmount [[],[],[],[1],[3]]) (patternEdgeCount [[],[],[],[1],[3]]) [] := certificate_695_checked

theorem certificate_696_checked : certificate_696.Valid 13 7 12 certificate_696_q certificate_696_edges 5 2 [] := by decide +kernel
theorem certificate_696_valid : certificate_696.Valid 13 7 (patternOrder [[],[],[],[1],[4]]) (patternClique [[],[],[],[1],[4]]) (patternEdges [[],[],[],[1],[4]]) (patternAmount [[],[],[],[1],[4]]) (patternEdgeCount [[],[],[],[1],[4]]) [] := certificate_696_checked

theorem certificate_697_checked : certificate_697.Valid 13 7 13 certificate_697_q certificate_697_edges 6 2 [] := by decide +kernel
theorem certificate_697_valid : certificate_697.Valid 13 7 (patternOrder [[],[],[],[1],[5]]) (patternClique [[],[],[],[1],[5]]) (patternEdges [[],[],[],[1],[5]]) (patternAmount [[],[],[],[1],[5]]) (patternEdgeCount [[],[],[],[1],[5]]) [] := certificate_697_checked

theorem certificate_698_checked : certificate_698.Valid 13 7 10 certificate_698_q certificate_698_edges 3 3 [] := by decide +kernel
theorem certificate_698_valid : certificate_698.Valid 13 7 (patternOrder [[],[],[],[1,1,1]]) (patternClique [[],[],[],[1,1,1]]) (patternEdges [[],[],[],[1,1,1]]) (patternAmount [[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[1,1,1]]) [] := certificate_698_checked

theorem certificate_699_checked : certificate_699.Valid 13 7 11 certificate_699_q certificate_699_edges 4 3 [] := by decide +kernel
theorem certificate_699_valid : certificate_699.Valid 13 7 (patternOrder [[],[],[],[1,1,2]]) (patternClique [[],[],[],[1,1,2]]) (patternEdges [[],[],[],[1,1,2]]) (patternAmount [[],[],[],[1,1,2]]) (patternEdgeCount [[],[],[],[1,1,2]]) [] := certificate_699_checked

theorem certificate_700_checked : certificate_700.Valid 13 7 12 certificate_700_q certificate_700_edges 5 3 [] := by decide +kernel
theorem certificate_700_valid : certificate_700.Valid 13 7 (patternOrder [[],[],[],[1,1,3]]) (patternClique [[],[],[],[1,1,3]]) (patternEdges [[],[],[],[1,1,3]]) (patternAmount [[],[],[],[1,1,3]]) (patternEdgeCount [[],[],[],[1,1,3]]) [] := certificate_700_checked

theorem certificate_701_checked : certificate_701.Valid 13 7 13 certificate_701_q certificate_701_edges 6 3 [] := by decide +kernel
theorem certificate_701_valid : certificate_701.Valid 13 7 (patternOrder [[],[],[],[1,1,4]]) (patternClique [[],[],[],[1,1,4]]) (patternEdges [[],[],[],[1,1,4]]) (patternAmount [[],[],[],[1,1,4]]) (patternEdgeCount [[],[],[],[1,1,4]]) [] := certificate_701_checked

theorem certificate_702_checked : certificate_702.Valid 13 7 11 certificate_702_q certificate_702_edges 4 3 [] := by decide +kernel
theorem certificate_702_valid : certificate_702.Valid 13 7 (patternOrder [[],[],[],[1,2,1]]) (patternClique [[],[],[],[1,2,1]]) (patternEdges [[],[],[],[1,2,1]]) (patternAmount [[],[],[],[1,2,1]]) (patternEdgeCount [[],[],[],[1,2,1]]) [] := certificate_702_checked

theorem certificate_703_checked : certificate_703.Valid 13 7 12 certificate_703_q certificate_703_edges 5 3 [] := by decide +kernel
theorem certificate_703_valid : certificate_703.Valid 13 7 (patternOrder [[],[],[],[1,2,2]]) (patternClique [[],[],[],[1,2,2]]) (patternEdges [[],[],[],[1,2,2]]) (patternAmount [[],[],[],[1,2,2]]) (patternEdgeCount [[],[],[],[1,2,2]]) [] := certificate_703_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates023
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_704_checked : certificate_704.Valid 13 7 13 certificate_704_q certificate_704_edges 6 3 [] := by decide +kernel
theorem certificate_704_valid : certificate_704.Valid 13 7 (patternOrder [[],[],[],[1,2,3]]) (patternClique [[],[],[],[1,2,3]]) (patternEdges [[],[],[],[1,2,3]]) (patternAmount [[],[],[],[1,2,3]]) (patternEdgeCount [[],[],[],[1,2,3]]) [] := certificate_704_checked

theorem certificate_705_checked : certificate_705.Valid 13 7 12 certificate_705_q certificate_705_edges 5 3 [] := by decide +kernel
theorem certificate_705_valid : certificate_705.Valid 13 7 (patternOrder [[],[],[],[1,3,1]]) (patternClique [[],[],[],[1,3,1]]) (patternEdges [[],[],[],[1,3,1]]) (patternAmount [[],[],[],[1,3,1]]) (patternEdgeCount [[],[],[],[1,3,1]]) [] := certificate_705_checked

theorem certificate_706_checked : certificate_706.Valid 13 7 13 certificate_706_q certificate_706_edges 6 3 [] := by decide +kernel
theorem certificate_706_valid : certificate_706.Valid 13 7 (patternOrder [[],[],[],[1,3,2]]) (patternClique [[],[],[],[1,3,2]]) (patternEdges [[],[],[],[1,3,2]]) (patternAmount [[],[],[],[1,3,2]]) (patternEdgeCount [[],[],[],[1,3,2]]) [] := certificate_706_checked

theorem certificate_707_checked : certificate_707.Valid 13 7 13 certificate_707_q certificate_707_edges 6 3 [] := by decide +kernel
theorem certificate_707_valid : certificate_707.Valid 13 7 (patternOrder [[],[],[],[1,4,1]]) (patternClique [[],[],[],[1,4,1]]) (patternEdges [[],[],[],[1,4,1]]) (patternAmount [[],[],[],[1,4,1]]) (patternEdgeCount [[],[],[],[1,4,1]]) [] := certificate_707_checked

theorem certificate_708_checked : certificate_708.Valid 13 7 11 certificate_708_q certificate_708_edges 4 2 [] := by decide +kernel
theorem certificate_708_valid : certificate_708.Valid 13 7 (patternOrder [[],[],[],[2],[2]]) (patternClique [[],[],[],[2],[2]]) (patternEdges [[],[],[],[2],[2]]) (patternAmount [[],[],[],[2],[2]]) (patternEdgeCount [[],[],[],[2],[2]]) [] := certificate_708_checked

theorem certificate_709_checked : certificate_709.Valid 13 7 12 certificate_709_q certificate_709_edges 5 2 [] := by decide +kernel
theorem certificate_709_valid : certificate_709.Valid 13 7 (patternOrder [[],[],[],[2],[3]]) (patternClique [[],[],[],[2],[3]]) (patternEdges [[],[],[],[2],[3]]) (patternAmount [[],[],[],[2],[3]]) (patternEdgeCount [[],[],[],[2],[3]]) [] := certificate_709_checked

theorem certificate_710_checked : certificate_710.Valid 13 7 13 certificate_710_q certificate_710_edges 6 2 [] := by decide +kernel
theorem certificate_710_valid : certificate_710.Valid 13 7 (patternOrder [[],[],[],[2],[4]]) (patternClique [[],[],[],[2],[4]]) (patternEdges [[],[],[],[2],[4]]) (patternAmount [[],[],[],[2],[4]]) (patternEdgeCount [[],[],[],[2],[4]]) [] := certificate_710_checked

theorem certificate_711_checked : certificate_711.Valid 13 7 12 certificate_711_q certificate_711_edges 5 3 [] := by decide +kernel
theorem certificate_711_valid : certificate_711.Valid 13 7 (patternOrder [[],[],[],[2,1,2]]) (patternClique [[],[],[],[2,1,2]]) (patternEdges [[],[],[],[2,1,2]]) (patternAmount [[],[],[],[2,1,2]]) (patternEdgeCount [[],[],[],[2,1,2]]) [] := certificate_711_checked

theorem certificate_712_checked : certificate_712.Valid 13 7 13 certificate_712_q certificate_712_edges 6 3 [] := by decide +kernel
theorem certificate_712_valid : certificate_712.Valid 13 7 (patternOrder [[],[],[],[2,1,3]]) (patternClique [[],[],[],[2,1,3]]) (patternEdges [[],[],[],[2,1,3]]) (patternAmount [[],[],[],[2,1,3]]) (patternEdgeCount [[],[],[],[2,1,3]]) [] := certificate_712_checked

theorem certificate_713_checked : certificate_713.Valid 13 7 13 certificate_713_q certificate_713_edges 6 3 [] := by decide +kernel
theorem certificate_713_valid : certificate_713.Valid 13 7 (patternOrder [[],[],[],[2,2,2]]) (patternClique [[],[],[],[2,2,2]]) (patternEdges [[],[],[],[2,2,2]]) (patternAmount [[],[],[],[2,2,2]]) (patternEdgeCount [[],[],[],[2,2,2]]) [] := certificate_713_checked

theorem certificate_714_checked : certificate_714.Valid 13 7 13 certificate_714_q certificate_714_edges 6 2 [] := by decide +kernel
theorem certificate_714_valid : certificate_714.Valid 13 7 (patternOrder [[],[],[],[3],[3]]) (patternClique [[],[],[],[3],[3]]) (patternEdges [[],[],[],[3],[3]]) (patternAmount [[],[],[],[3],[3]]) (patternEdgeCount [[],[],[],[3],[3]]) [] := certificate_714_checked

theorem certificate_715_checked : certificate_715.Valid 13 7 10 certificate_715_q certificate_715_edges 3 3 [] := by decide +kernel
theorem certificate_715_valid : certificate_715.Valid 13 7 (patternOrder [[],[],[1],[1,1]]) (patternClique [[],[],[1],[1,1]]) (patternEdges [[],[],[1],[1,1]]) (patternAmount [[],[],[1],[1,1]]) (patternEdgeCount [[],[],[1],[1,1]]) [] := certificate_715_checked

theorem certificate_716_checked : certificate_716.Valid 13 7 11 certificate_716_q certificate_716_edges 4 3 [] := by decide +kernel
theorem certificate_716_valid : certificate_716.Valid 13 7 (patternOrder [[],[],[1],[1,2]]) (patternClique [[],[],[1],[1,2]]) (patternEdges [[],[],[1],[1,2]]) (patternAmount [[],[],[1],[1,2]]) (patternEdgeCount [[],[],[1],[1,2]]) [] := certificate_716_checked

theorem certificate_717_checked : certificate_717.Valid 13 7 12 certificate_717_q certificate_717_edges 5 3 [] := by decide +kernel
theorem certificate_717_valid : certificate_717.Valid 13 7 (patternOrder [[],[],[1],[1,3]]) (patternClique [[],[],[1],[1,3]]) (patternEdges [[],[],[1],[1,3]]) (patternAmount [[],[],[1],[1,3]]) (patternEdgeCount [[],[],[1],[1,3]]) [] := certificate_717_checked

theorem certificate_718_checked : certificate_718.Valid 13 7 13 certificate_718_q certificate_718_edges 6 3 [] := by decide +kernel
theorem certificate_718_valid : certificate_718.Valid 13 7 (patternOrder [[],[],[1],[1,4]]) (patternClique [[],[],[1],[1,4]]) (patternEdges [[],[],[1],[1,4]]) (patternAmount [[],[],[1],[1,4]]) (patternEdgeCount [[],[],[1],[1,4]]) [] := certificate_718_checked

theorem certificate_719_checked : certificate_719.Valid 13 7 12 certificate_719_q certificate_719_edges 5 3 [] := by decide +kernel
theorem certificate_719_valid : certificate_719.Valid 13 7 (patternOrder [[],[],[1],[2,2]]) (patternClique [[],[],[1],[2,2]]) (patternEdges [[],[],[1],[2,2]]) (patternAmount [[],[],[1],[2,2]]) (patternEdgeCount [[],[],[1],[2,2]]) [] := certificate_719_checked

theorem certificate_720_checked : certificate_720.Valid 13 7 13 certificate_720_q certificate_720_edges 6 3 [] := by decide +kernel
theorem certificate_720_valid : certificate_720.Valid 13 7 (patternOrder [[],[],[1],[2,3]]) (patternClique [[],[],[1],[2,3]]) (patternEdges [[],[],[1],[2,3]]) (patternAmount [[],[],[1],[2,3]]) (patternEdgeCount [[],[],[1],[2,3]]) [] := certificate_720_checked

theorem certificate_721_checked : certificate_721.Valid 13 7 11 certificate_721_q certificate_721_edges 4 3 [] := by decide +kernel
theorem certificate_721_valid : certificate_721.Valid 13 7 (patternOrder [[],[],[1,1],[2]]) (patternClique [[],[],[1,1],[2]]) (patternEdges [[],[],[1,1],[2]]) (patternAmount [[],[],[1,1],[2]]) (patternEdgeCount [[],[],[1,1],[2]]) [] := certificate_721_checked

theorem certificate_722_checked : certificate_722.Valid 13 7 12 certificate_722_q certificate_722_edges 5 3 [] := by decide +kernel
theorem certificate_722_valid : certificate_722.Valid 13 7 (patternOrder [[],[],[1,1],[3]]) (patternClique [[],[],[1,1],[3]]) (patternEdges [[],[],[1,1],[3]]) (patternAmount [[],[],[1,1],[3]]) (patternEdgeCount [[],[],[1,1],[3]]) [] := certificate_722_checked

theorem certificate_723_checked : certificate_723.Valid 13 7 13 certificate_723_q certificate_723_edges 6 3 [] := by decide +kernel
theorem certificate_723_valid : certificate_723.Valid 13 7 (patternOrder [[],[],[1,1],[4]]) (patternClique [[],[],[1,1],[4]]) (patternEdges [[],[],[1,1],[4]]) (patternAmount [[],[],[1,1],[4]]) (patternEdgeCount [[],[],[1,1],[4]]) [] := certificate_723_checked

theorem certificate_724_checked : certificate_724.Valid 13 7 11 certificate_724_q certificate_724_edges 4 4 [] := by decide +kernel
theorem certificate_724_valid : certificate_724.Valid 13 7 (patternOrder [[],[],[1,1,1,1]]) (patternClique [[],[],[1,1,1,1]]) (patternEdges [[],[],[1,1,1,1]]) (patternAmount [[],[],[1,1,1,1]]) (patternEdgeCount [[],[],[1,1,1,1]]) [] := certificate_724_checked

theorem certificate_725_checked : certificate_725.Valid 13 7 12 certificate_725_q certificate_725_edges 5 4 [] := by decide +kernel
theorem certificate_725_valid : certificate_725.Valid 13 7 (patternOrder [[],[],[1,1,1,2]]) (patternClique [[],[],[1,1,1,2]]) (patternEdges [[],[],[1,1,1,2]]) (patternAmount [[],[],[1,1,1,2]]) (patternEdgeCount [[],[],[1,1,1,2]]) [] := certificate_725_checked

theorem certificate_726_checked : certificate_726.Valid 13 7 13 certificate_726_q certificate_726_edges 6 4 [] := by decide +kernel
theorem certificate_726_valid : certificate_726.Valid 13 7 (patternOrder [[],[],[1,1,1,3]]) (patternClique [[],[],[1,1,1,3]]) (patternEdges [[],[],[1,1,1,3]]) (patternAmount [[],[],[1,1,1,3]]) (patternEdgeCount [[],[],[1,1,1,3]]) [] := certificate_726_checked

theorem certificate_727_checked : certificate_727.Valid 13 7 12 certificate_727_q certificate_727_edges 5 4 [] := by decide +kernel
theorem certificate_727_valid : certificate_727.Valid 13 7 (patternOrder [[],[],[1,1,2,1]]) (patternClique [[],[],[1,1,2,1]]) (patternEdges [[],[],[1,1,2,1]]) (patternAmount [[],[],[1,1,2,1]]) (patternEdgeCount [[],[],[1,1,2,1]]) [] := certificate_727_checked

theorem certificate_728_checked : certificate_728.Valid 13 7 13 certificate_728_q certificate_728_edges 6 4 [] := by decide +kernel
theorem certificate_728_valid : certificate_728.Valid 13 7 (patternOrder [[],[],[1,1,2,2]]) (patternClique [[],[],[1,1,2,2]]) (patternEdges [[],[],[1,1,2,2]]) (patternAmount [[],[],[1,1,2,2]]) (patternEdgeCount [[],[],[1,1,2,2]]) [] := certificate_728_checked

theorem certificate_729_checked : certificate_729.Valid 13 7 13 certificate_729_q certificate_729_edges 6 4 [] := by decide +kernel
theorem certificate_729_valid : certificate_729.Valid 13 7 (patternOrder [[],[],[1,1,3,1]]) (patternClique [[],[],[1,1,3,1]]) (patternEdges [[],[],[1,1,3,1]]) (patternAmount [[],[],[1,1,3,1]]) (patternEdgeCount [[],[],[1,1,3,1]]) [] := certificate_729_checked

theorem certificate_730_checked : certificate_730.Valid 13 7 12 certificate_730_q certificate_730_edges 5 3 [] := by decide +kernel
theorem certificate_730_valid : certificate_730.Valid 13 7 (patternOrder [[],[],[1,2],[2]]) (patternClique [[],[],[1,2],[2]]) (patternEdges [[],[],[1,2],[2]]) (patternAmount [[],[],[1,2],[2]]) (patternEdgeCount [[],[],[1,2],[2]]) [] := certificate_730_checked

theorem certificate_731_checked : certificate_731.Valid 13 7 13 certificate_731_q certificate_731_edges 6 3 [] := by decide +kernel
theorem certificate_731_valid : certificate_731.Valid 13 7 (patternOrder [[],[],[1,2],[3]]) (patternClique [[],[],[1,2],[3]]) (patternEdges [[],[],[1,2],[3]]) (patternAmount [[],[],[1,2],[3]]) (patternEdgeCount [[],[],[1,2],[3]]) [] := certificate_731_checked

theorem certificate_732_checked : certificate_732.Valid 13 7 13 certificate_732_q certificate_732_edges 6 4 [] := by decide +kernel
theorem certificate_732_valid : certificate_732.Valid 13 7 (patternOrder [[],[],[1,2,1,2]]) (patternClique [[],[],[1,2,1,2]]) (patternEdges [[],[],[1,2,1,2]]) (patternAmount [[],[],[1,2,1,2]]) (patternEdgeCount [[],[],[1,2,1,2]]) [] := certificate_732_checked

theorem certificate_733_checked : certificate_733.Valid 13 7 13 certificate_733_q certificate_733_edges 6 4 [] := by decide +kernel
theorem certificate_733_valid : certificate_733.Valid 13 7 (patternOrder [[],[],[1,2,2,1]]) (patternClique [[],[],[1,2,2,1]]) (patternEdges [[],[],[1,2,2,1]]) (patternAmount [[],[],[1,2,2,1]]) (patternEdgeCount [[],[],[1,2,2,1]]) [] := certificate_733_checked

theorem certificate_734_checked : certificate_734.Valid 13 7 13 certificate_734_q certificate_734_edges 6 3 [] := by decide +kernel
theorem certificate_734_valid : certificate_734.Valid 13 7 (patternOrder [[],[],[1,3],[2]]) (patternClique [[],[],[1,3],[2]]) (patternEdges [[],[],[1,3],[2]]) (patternAmount [[],[],[1,3],[2]]) (patternEdgeCount [[],[],[1,3],[2]]) [] := certificate_734_checked

theorem certificate_735_checked : certificate_735.Valid 13 7 13 certificate_735_q certificate_735_edges 6 3 [] := by decide +kernel
theorem certificate_735_valid : certificate_735.Valid 13 7 (patternOrder [[],[],[2],[2,2]]) (patternClique [[],[],[2],[2,2]]) (patternEdges [[],[],[2],[2,2]]) (patternAmount [[],[],[2],[2,2]]) (patternEdgeCount [[],[],[2],[2,2]]) [] := certificate_735_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates024
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_736_checked : certificate_736.Valid 13 7 13 certificate_736_q certificate_736_edges 6 4 [] := by decide +kernel
theorem certificate_736_valid : certificate_736.Valid 13 7 (patternOrder [[],[],[2,1,1,2]]) (patternClique [[],[],[2,1,1,2]]) (patternEdges [[],[],[2,1,1,2]]) (patternAmount [[],[],[2,1,1,2]]) (patternEdgeCount [[],[],[2,1,1,2]]) [] := certificate_736_checked

theorem certificate_737_checked : certificate_737.Valid 13 7 10 certificate_737_q certificate_737_edges 3 3 [] := by decide +kernel
theorem certificate_737_valid : certificate_737.Valid 13 7 (patternOrder [[],[1],[1],[1]]) (patternClique [[],[1],[1],[1]]) (patternEdges [[],[1],[1],[1]]) (patternAmount [[],[1],[1],[1]]) (patternEdgeCount [[],[1],[1],[1]]) [] := certificate_737_checked

theorem certificate_738_checked : certificate_738.Valid 13 7 11 certificate_738_q certificate_738_edges 4 3 [] := by decide +kernel
theorem certificate_738_valid : certificate_738.Valid 13 7 (patternOrder [[],[1],[1],[2]]) (patternClique [[],[1],[1],[2]]) (patternEdges [[],[1],[1],[2]]) (patternAmount [[],[1],[1],[2]]) (patternEdgeCount [[],[1],[1],[2]]) [] := certificate_738_checked

theorem certificate_739_checked : certificate_739.Valid 13 7 12 certificate_739_q certificate_739_edges 5 3 [] := by decide +kernel
theorem certificate_739_valid : certificate_739.Valid 13 7 (patternOrder [[],[1],[1],[3]]) (patternClique [[],[1],[1],[3]]) (patternEdges [[],[1],[1],[3]]) (patternAmount [[],[1],[1],[3]]) (patternEdgeCount [[],[1],[1],[3]]) [] := certificate_739_checked

theorem certificate_740_checked : certificate_740.Valid 13 7 13 certificate_740_q certificate_740_edges 6 3 [] := by decide +kernel
theorem certificate_740_valid : certificate_740.Valid 13 7 (patternOrder [[],[1],[1],[4]]) (patternClique [[],[1],[1],[4]]) (patternEdges [[],[1],[1],[4]]) (patternAmount [[],[1],[1],[4]]) (patternEdgeCount [[],[1],[1],[4]]) [] := certificate_740_checked

theorem certificate_741_checked : certificate_741.Valid 13 7 11 certificate_741_q certificate_741_edges 4 4 [] := by decide +kernel
theorem certificate_741_valid : certificate_741.Valid 13 7 (patternOrder [[],[1],[1,1,1]]) (patternClique [[],[1],[1,1,1]]) (patternEdges [[],[1],[1,1,1]]) (patternAmount [[],[1],[1,1,1]]) (patternEdgeCount [[],[1],[1,1,1]]) [] := certificate_741_checked

theorem certificate_742_checked : certificate_742.Valid 13 7 12 certificate_742_q certificate_742_edges 5 4 [] := by decide +kernel
theorem certificate_742_valid : certificate_742.Valid 13 7 (patternOrder [[],[1],[1,1,2]]) (patternClique [[],[1],[1,1,2]]) (patternEdges [[],[1],[1,1,2]]) (patternAmount [[],[1],[1,1,2]]) (patternEdgeCount [[],[1],[1,1,2]]) [] := certificate_742_checked

theorem certificate_743_checked : certificate_743.Valid 13 7 13 certificate_743_q certificate_743_edges 6 4 [] := by decide +kernel
theorem certificate_743_valid : certificate_743.Valid 13 7 (patternOrder [[],[1],[1,1,3]]) (patternClique [[],[1],[1,1,3]]) (patternEdges [[],[1],[1,1,3]]) (patternAmount [[],[1],[1,1,3]]) (patternEdgeCount [[],[1],[1,1,3]]) [] := certificate_743_checked

theorem certificate_744_checked : certificate_744.Valid 13 7 12 certificate_744_q certificate_744_edges 5 4 [] := by decide +kernel
theorem certificate_744_valid : certificate_744.Valid 13 7 (patternOrder [[],[1],[1,2,1]]) (patternClique [[],[1],[1,2,1]]) (patternEdges [[],[1],[1,2,1]]) (patternAmount [[],[1],[1,2,1]]) (patternEdgeCount [[],[1],[1,2,1]]) [] := certificate_744_checked

theorem certificate_745_checked : certificate_745.Valid 13 7 13 certificate_745_q certificate_745_edges 6 4 [] := by decide +kernel
theorem certificate_745_valid : certificate_745.Valid 13 7 (patternOrder [[],[1],[1,2,2]]) (patternClique [[],[1],[1,2,2]]) (patternEdges [[],[1],[1,2,2]]) (patternAmount [[],[1],[1,2,2]]) (patternEdgeCount [[],[1],[1,2,2]]) [] := certificate_745_checked

theorem certificate_746_checked : certificate_746.Valid 13 7 13 certificate_746_q certificate_746_edges 6 4 [] := by decide +kernel
theorem certificate_746_valid : certificate_746.Valid 13 7 (patternOrder [[],[1],[1,3,1]]) (patternClique [[],[1],[1,3,1]]) (patternEdges [[],[1],[1,3,1]]) (patternAmount [[],[1],[1,3,1]]) (patternEdgeCount [[],[1],[1,3,1]]) [] := certificate_746_checked

theorem certificate_747_checked : certificate_747.Valid 13 7 12 certificate_747_q certificate_747_edges 5 3 [] := by decide +kernel
theorem certificate_747_valid : certificate_747.Valid 13 7 (patternOrder [[],[1],[2],[2]]) (patternClique [[],[1],[2],[2]]) (patternEdges [[],[1],[2],[2]]) (patternAmount [[],[1],[2],[2]]) (patternEdgeCount [[],[1],[2],[2]]) [] := certificate_747_checked

theorem certificate_748_checked : certificate_748.Valid 13 7 13 certificate_748_q certificate_748_edges 6 3 [] := by decide +kernel
theorem certificate_748_valid : certificate_748.Valid 13 7 (patternOrder [[],[1],[2],[3]]) (patternClique [[],[1],[2],[3]]) (patternEdges [[],[1],[2],[3]]) (patternAmount [[],[1],[2],[3]]) (patternEdgeCount [[],[1],[2],[3]]) [] := certificate_748_checked

theorem certificate_749_checked : certificate_749.Valid 13 7 13 certificate_749_q certificate_749_edges 6 4 [] := by decide +kernel
theorem certificate_749_valid : certificate_749.Valid 13 7 (patternOrder [[],[1],[2,1,2]]) (patternClique [[],[1],[2,1,2]]) (patternEdges [[],[1],[2,1,2]]) (patternAmount [[],[1],[2,1,2]]) (patternEdgeCount [[],[1],[2,1,2]]) [] := certificate_749_checked

theorem certificate_750_checked : certificate_750.Valid 13 7 11 certificate_750_q certificate_750_edges 4 4 [] := by decide +kernel
theorem certificate_750_valid : certificate_750.Valid 13 7 (patternOrder [[],[1,1],[1,1]]) (patternClique [[],[1,1],[1,1]]) (patternEdges [[],[1,1],[1,1]]) (patternAmount [[],[1,1],[1,1]]) (patternEdgeCount [[],[1,1],[1,1]]) [] := certificate_750_checked

theorem certificate_751_checked : certificate_751.Valid 13 7 12 certificate_751_q certificate_751_edges 5 4 [] := by decide +kernel
theorem certificate_751_valid : certificate_751.Valid 13 7 (patternOrder [[],[1,1],[1,2]]) (patternClique [[],[1,1],[1,2]]) (patternEdges [[],[1,1],[1,2]]) (patternAmount [[],[1,1],[1,2]]) (patternEdgeCount [[],[1,1],[1,2]]) [] := certificate_751_checked

theorem certificate_752_checked : certificate_752.Valid 13 7 13 certificate_752_q certificate_752_edges 6 4 [] := by decide +kernel
theorem certificate_752_valid : certificate_752.Valid 13 7 (patternOrder [[],[1,1],[1,3]]) (patternClique [[],[1,1],[1,3]]) (patternEdges [[],[1,1],[1,3]]) (patternAmount [[],[1,1],[1,3]]) (patternEdgeCount [[],[1,1],[1,3]]) [] := certificate_752_checked

theorem certificate_753_checked : certificate_753.Valid 13 7 13 certificate_753_q certificate_753_edges 6 4 [] := by decide +kernel
theorem certificate_753_valid : certificate_753.Valid 13 7 (patternOrder [[],[1,1],[2,2]]) (patternClique [[],[1,1],[2,2]]) (patternEdges [[],[1,1],[2,2]]) (patternAmount [[],[1,1],[2,2]]) (patternEdgeCount [[],[1,1],[2,2]]) [] := certificate_753_checked

theorem certificate_754_checked : certificate_754.Valid 13 7 12 certificate_754_q certificate_754_edges 5 4 [] := by decide +kernel
theorem certificate_754_valid : certificate_754.Valid 13 7 (patternOrder [[],[1,1,1],[2]]) (patternClique [[],[1,1,1],[2]]) (patternEdges [[],[1,1,1],[2]]) (patternAmount [[],[1,1,1],[2]]) (patternEdgeCount [[],[1,1,1],[2]]) [] := certificate_754_checked

theorem certificate_755_checked : certificate_755.Valid 13 7 13 certificate_755_q certificate_755_edges 6 4 [] := by decide +kernel
theorem certificate_755_valid : certificate_755.Valid 13 7 (patternOrder [[],[1,1,1],[3]]) (patternClique [[],[1,1,1],[3]]) (patternEdges [[],[1,1,1],[3]]) (patternAmount [[],[1,1,1],[3]]) (patternEdgeCount [[],[1,1,1],[3]]) [] := certificate_755_checked

theorem certificate_756_checked : certificate_756.Valid 13 7 12 certificate_756_q certificate_756_edges 5 5 [] := by decide +kernel
theorem certificate_756_valid : certificate_756.Valid 13 7 (patternOrder [[],[1,1,1,1,1]]) (patternClique [[],[1,1,1,1,1]]) (patternEdges [[],[1,1,1,1,1]]) (patternAmount [[],[1,1,1,1,1]]) (patternEdgeCount [[],[1,1,1,1,1]]) [] := certificate_756_checked

theorem certificate_757_checked : certificate_757.Valid 13 7 13 certificate_757_q certificate_757_edges 6 5 [] := by decide +kernel
theorem certificate_757_valid : certificate_757.Valid 13 7 (patternOrder [[],[1,1,1,1,2]]) (patternClique [[],[1,1,1,1,2]]) (patternEdges [[],[1,1,1,1,2]]) (patternAmount [[],[1,1,1,1,2]]) (patternEdgeCount [[],[1,1,1,1,2]]) [] := certificate_757_checked

theorem certificate_758_checked : certificate_758.Valid 13 7 13 certificate_758_q certificate_758_edges 6 5 [] := by decide +kernel
theorem certificate_758_valid : certificate_758.Valid 13 7 (patternOrder [[],[1,1,1,2,1]]) (patternClique [[],[1,1,1,2,1]]) (patternEdges [[],[1,1,1,2,1]]) (patternAmount [[],[1,1,1,2,1]]) (patternEdgeCount [[],[1,1,1,2,1]]) [] := certificate_758_checked

theorem certificate_759_checked : certificate_759.Valid 13 7 13 certificate_759_q certificate_759_edges 6 4 [] := by decide +kernel
theorem certificate_759_valid : certificate_759.Valid 13 7 (patternOrder [[],[1,1,2],[2]]) (patternClique [[],[1,1,2],[2]]) (patternEdges [[],[1,1,2],[2]]) (patternAmount [[],[1,1,2],[2]]) (patternEdgeCount [[],[1,1,2],[2]]) [] := certificate_759_checked

theorem certificate_760_checked : certificate_760.Valid 13 7 13 certificate_760_q certificate_760_edges 6 5 [] := by decide +kernel
theorem certificate_760_valid : certificate_760.Valid 13 7 (patternOrder [[],[1,1,2,1,1]]) (patternClique [[],[1,1,2,1,1]]) (patternEdges [[],[1,1,2,1,1]]) (patternAmount [[],[1,1,2,1,1]]) (patternEdgeCount [[],[1,1,2,1,1]]) [] := certificate_760_checked

theorem certificate_761_checked : certificate_761.Valid 13 7 13 certificate_761_q certificate_761_edges 6 4 [] := by decide +kernel
theorem certificate_761_valid : certificate_761.Valid 13 7 (patternOrder [[],[1,2],[1,2]]) (patternClique [[],[1,2],[1,2]]) (patternEdges [[],[1,2],[1,2]]) (patternAmount [[],[1,2],[1,2]]) (patternEdgeCount [[],[1,2],[1,2]]) [] := certificate_761_checked

theorem certificate_762_checked : certificate_762.Valid 13 7 13 certificate_762_q certificate_762_edges 6 4 [] := by decide +kernel
theorem certificate_762_valid : certificate_762.Valid 13 7 (patternOrder [[],[1,2,1],[2]]) (patternClique [[],[1,2,1],[2]]) (patternEdges [[],[1,2,1],[2]]) (patternAmount [[],[1,2,1],[2]]) (patternEdgeCount [[],[1,2,1],[2]]) [] := certificate_762_checked

theorem certificate_763_checked : certificate_763.Valid 13 7 13 certificate_763_q certificate_763_edges 6 3 [] := by decide +kernel
theorem certificate_763_valid : certificate_763.Valid 13 7 (patternOrder [[],[2],[2],[2]]) (patternClique [[],[2],[2],[2]]) (patternEdges [[],[2],[2],[2]]) (patternAmount [[],[2],[2],[2]]) (patternEdgeCount [[],[2],[2],[2]]) [] := certificate_763_checked

theorem certificate_764_checked : certificate_764.Valid 13 7 11 certificate_764_q certificate_764_edges 4 4 [] := by decide +kernel
theorem certificate_764_valid : certificate_764.Valid 13 7 (patternOrder [[1],[1],[1,1]]) (patternClique [[1],[1],[1,1]]) (patternEdges [[1],[1],[1,1]]) (patternAmount [[1],[1],[1,1]]) (patternEdgeCount [[1],[1],[1,1]]) [] := certificate_764_checked

theorem certificate_765_checked : certificate_765.Valid 13 7 12 certificate_765_q certificate_765_edges 5 4 [] := by decide +kernel
theorem certificate_765_valid : certificate_765.Valid 13 7 (patternOrder [[1],[1],[1,2]]) (patternClique [[1],[1],[1,2]]) (patternEdges [[1],[1],[1,2]]) (patternAmount [[1],[1],[1,2]]) (patternEdgeCount [[1],[1],[1,2]]) [] := certificate_765_checked

theorem certificate_766_checked : certificate_766.Valid 13 7 13 certificate_766_q certificate_766_edges 6 4 [] := by decide +kernel
theorem certificate_766_valid : certificate_766.Valid 13 7 (patternOrder [[1],[1],[1,3]]) (patternClique [[1],[1],[1,3]]) (patternEdges [[1],[1],[1,3]]) (patternAmount [[1],[1],[1,3]]) (patternEdgeCount [[1],[1],[1,3]]) [] := certificate_766_checked

theorem certificate_767_checked : certificate_767.Valid 13 7 13 certificate_767_q certificate_767_edges 6 4 [] := by decide +kernel
theorem certificate_767_valid : certificate_767.Valid 13 7 (patternOrder [[1],[1],[2,2]]) (patternClique [[1],[1],[2,2]]) (patternEdges [[1],[1],[2,2]]) (patternAmount [[1],[1],[2,2]]) (patternEdgeCount [[1],[1],[2,2]]) [] := certificate_767_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates025
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_768_checked : certificate_768.Valid 13 7 12 certificate_768_q certificate_768_edges 5 4 [] := by decide +kernel
theorem certificate_768_valid : certificate_768.Valid 13 7 (patternOrder [[1],[1,1],[2]]) (patternClique [[1],[1,1],[2]]) (patternEdges [[1],[1,1],[2]]) (patternAmount [[1],[1,1],[2]]) (patternEdgeCount [[1],[1,1],[2]]) [] := certificate_768_checked

theorem certificate_769_checked : certificate_769.Valid 13 7 13 certificate_769_q certificate_769_edges 6 4 [] := by decide +kernel
theorem certificate_769_valid : certificate_769.Valid 13 7 (patternOrder [[1],[1,1],[3]]) (patternClique [[1],[1,1],[3]]) (patternEdges [[1],[1,1],[3]]) (patternAmount [[1],[1,1],[3]]) (patternEdgeCount [[1],[1,1],[3]]) [] := certificate_769_checked

theorem certificate_770_checked : certificate_770.Valid 13 7 12 certificate_770_q certificate_770_edges 5 5 [] := by decide +kernel
theorem certificate_770_valid : certificate_770.Valid 13 7 (patternOrder [[1],[1,1,1,1]]) (patternClique [[1],[1,1,1,1]]) (patternEdges [[1],[1,1,1,1]]) (patternAmount [[1],[1,1,1,1]]) (patternEdgeCount [[1],[1,1,1,1]]) [] := certificate_770_checked

theorem certificate_771_checked : certificate_771.Valid 13 7 13 certificate_771_q certificate_771_edges 6 5 [] := by decide +kernel
theorem certificate_771_valid : certificate_771.Valid 13 7 (patternOrder [[1],[1,1,1,2]]) (patternClique [[1],[1,1,1,2]]) (patternEdges [[1],[1,1,1,2]]) (patternAmount [[1],[1,1,1,2]]) (patternEdgeCount [[1],[1,1,1,2]]) [] := certificate_771_checked

theorem certificate_772_checked : certificate_772.Valid 13 7 13 certificate_772_q certificate_772_edges 6 5 [] := by decide +kernel
theorem certificate_772_valid : certificate_772.Valid 13 7 (patternOrder [[1],[1,1,2,1]]) (patternClique [[1],[1,1,2,1]]) (patternEdges [[1],[1,1,2,1]]) (patternAmount [[1],[1,1,2,1]]) (patternEdgeCount [[1],[1,1,2,1]]) [] := certificate_772_checked

theorem certificate_773_checked : certificate_773.Valid 13 7 13 certificate_773_q certificate_773_edges 6 4 [] := by decide +kernel
theorem certificate_773_valid : certificate_773.Valid 13 7 (patternOrder [[1],[1,2],[2]]) (patternClique [[1],[1,2],[2]]) (patternEdges [[1],[1,2],[2]]) (patternAmount [[1],[1,2],[2]]) (patternEdgeCount [[1],[1,2],[2]]) [] := certificate_773_checked

theorem certificate_774_checked : certificate_774.Valid 13 7 12 certificate_774_q certificate_774_edges 5 5 [] := by decide +kernel
theorem certificate_774_valid : certificate_774.Valid 13 7 (patternOrder [[1,1],[1,1,1]]) (patternClique [[1,1],[1,1,1]]) (patternEdges [[1,1],[1,1,1]]) (patternAmount [[1,1],[1,1,1]]) (patternEdgeCount [[1,1],[1,1,1]]) [] := certificate_774_checked

theorem certificate_775_checked : certificate_775.Valid 13 7 13 certificate_775_q certificate_775_edges 6 5 [] := by decide +kernel
theorem certificate_775_valid : certificate_775.Valid 13 7 (patternOrder [[1,1],[1,1,2]]) (patternClique [[1,1],[1,1,2]]) (patternEdges [[1,1],[1,1,2]]) (patternAmount [[1,1],[1,1,2]]) (patternEdgeCount [[1,1],[1,1,2]]) [] := certificate_775_checked

theorem certificate_776_checked : certificate_776.Valid 13 7 13 certificate_776_q certificate_776_edges 6 5 [] := by decide +kernel
theorem certificate_776_valid : certificate_776.Valid 13 7 (patternOrder [[1,1],[1,2,1]]) (patternClique [[1,1],[1,2,1]]) (patternEdges [[1,1],[1,2,1]]) (patternAmount [[1,1],[1,2,1]]) (patternEdgeCount [[1,1],[1,2,1]]) [] := certificate_776_checked

theorem certificate_777_checked : certificate_777.Valid 13 7 13 certificate_777_q certificate_777_edges 6 4 [] := by decide +kernel
theorem certificate_777_valid : certificate_777.Valid 13 7 (patternOrder [[1,1],[2],[2]]) (patternClique [[1,1],[2],[2]]) (patternEdges [[1,1],[2],[2]]) (patternAmount [[1,1],[2],[2]]) (patternEdgeCount [[1,1],[2],[2]]) [] := certificate_777_checked

theorem certificate_778_checked : certificate_778.Valid 13 7 13 certificate_778_q certificate_778_edges 6 5 [] := by decide +kernel
theorem certificate_778_valid : certificate_778.Valid 13 7 (patternOrder [[1,1,1],[1,2]]) (patternClique [[1,1,1],[1,2]]) (patternEdges [[1,1,1],[1,2]]) (patternAmount [[1,1,1],[1,2]]) (patternEdgeCount [[1,1,1],[1,2]]) [] := certificate_778_checked

theorem certificate_779_checked : certificate_779.Valid 13 7 13 certificate_779_q certificate_779_edges 6 5 [] := by decide +kernel
theorem certificate_779_valid : certificate_779.Valid 13 7 (patternOrder [[1,1,1,1],[2]]) (patternClique [[1,1,1,1],[2]]) (patternEdges [[1,1,1,1],[2]]) (patternAmount [[1,1,1,1],[2]]) (patternEdgeCount [[1,1,1,1],[2]]) [] := certificate_779_checked

theorem certificate_780_checked : certificate_780.Valid 13 7 13 certificate_780_q certificate_780_edges 6 6 [] := by decide +kernel
theorem certificate_780_valid : certificate_780.Valid 13 7 (patternOrder [[1,1,1,1,1,1]]) (patternClique [[1,1,1,1,1,1]]) (patternEdges [[1,1,1,1,1,1]]) (patternAmount [[1,1,1,1,1,1]]) (patternEdgeCount [[1,1,1,1,1,1]]) [] := certificate_780_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns13x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_13_7_0_verified : ∀ D ∈ patterns_13_7_0, PatternVerified 13 7 D := by

  simp only [patterns_13_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_677, certificate_677_valid⟩, ⟨⟨certificate_678, certificate_678_valid⟩, ⟨⟨certificate_679, certificate_679_valid⟩, ⟨⟨certificate_680, certificate_680_valid⟩, ⟨⟨certificate_681, certificate_681_valid⟩, ⟨⟨certificate_682, certificate_682_valid⟩, ⟨⟨certificate_683, certificate_683_valid⟩, ⟨⟨certificate_684, certificate_684_valid⟩, ⟨⟨certificate_685, certificate_685_valid⟩, ⟨⟨certificate_686, certificate_686_valid⟩, ⟨⟨certificate_687, certificate_687_valid⟩, ⟨⟨certificate_688, certificate_688_valid⟩, ⟨⟨certificate_689, certificate_689_valid⟩, ⟨⟨certificate_690, certificate_690_valid⟩, ⟨⟨certificate_691, certificate_691_valid⟩, ⟨⟨certificate_692, certificate_692_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_7_1_verified : ∀ D ∈ patterns_13_7_1, PatternVerified 13 7 D := by

  simp only [patterns_13_7_1, List.forall_mem_cons]

  exact ⟨⟨certificate_693, certificate_693_valid⟩, ⟨⟨certificate_694, certificate_694_valid⟩, ⟨⟨certificate_695, certificate_695_valid⟩, ⟨⟨certificate_696, certificate_696_valid⟩, ⟨⟨certificate_697, certificate_697_valid⟩, ⟨⟨certificate_698, certificate_698_valid⟩, ⟨⟨certificate_699, certificate_699_valid⟩, ⟨⟨certificate_700, certificate_700_valid⟩, ⟨⟨certificate_701, certificate_701_valid⟩, ⟨⟨certificate_702, certificate_702_valid⟩, ⟨⟨certificate_703, certificate_703_valid⟩, ⟨⟨certificate_704, certificate_704_valid⟩, ⟨⟨certificate_705, certificate_705_valid⟩, ⟨⟨certificate_706, certificate_706_valid⟩, ⟨⟨certificate_707, certificate_707_valid⟩, ⟨⟨certificate_708, certificate_708_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_7_2_verified : ∀ D ∈ patterns_13_7_2, PatternVerified 13 7 D := by

  simp only [patterns_13_7_2, List.forall_mem_cons]

  exact ⟨⟨certificate_709, certificate_709_valid⟩, ⟨⟨certificate_710, certificate_710_valid⟩, ⟨⟨certificate_711, certificate_711_valid⟩, ⟨⟨certificate_712, certificate_712_valid⟩, ⟨⟨certificate_713, certificate_713_valid⟩, ⟨⟨certificate_714, certificate_714_valid⟩, ⟨⟨certificate_715, certificate_715_valid⟩, ⟨⟨certificate_716, certificate_716_valid⟩, ⟨⟨certificate_717, certificate_717_valid⟩, ⟨⟨certificate_718, certificate_718_valid⟩, ⟨⟨certificate_719, certificate_719_valid⟩, ⟨⟨certificate_720, certificate_720_valid⟩, ⟨⟨certificate_721, certificate_721_valid⟩, ⟨⟨certificate_722, certificate_722_valid⟩, ⟨⟨certificate_723, certificate_723_valid⟩, ⟨⟨certificate_724, certificate_724_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_7_3_verified : ∀ D ∈ patterns_13_7_3, PatternVerified 13 7 D := by

  simp only [patterns_13_7_3, List.forall_mem_cons]

  exact ⟨⟨certificate_725, certificate_725_valid⟩, ⟨⟨certificate_726, certificate_726_valid⟩, ⟨⟨certificate_727, certificate_727_valid⟩, ⟨⟨certificate_728, certificate_728_valid⟩, ⟨⟨certificate_729, certificate_729_valid⟩, ⟨⟨certificate_730, certificate_730_valid⟩, ⟨⟨certificate_731, certificate_731_valid⟩, ⟨⟨certificate_732, certificate_732_valid⟩, ⟨⟨certificate_733, certificate_733_valid⟩, ⟨⟨certificate_734, certificate_734_valid⟩, ⟨⟨certificate_735, certificate_735_valid⟩, ⟨⟨certificate_736, certificate_736_valid⟩, ⟨⟨certificate_737, certificate_737_valid⟩, ⟨⟨certificate_738, certificate_738_valid⟩, ⟨⟨certificate_739, certificate_739_valid⟩, ⟨⟨certificate_740, certificate_740_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_7_4_verified : ∀ D ∈ patterns_13_7_4, PatternVerified 13 7 D := by

  simp only [patterns_13_7_4, List.forall_mem_cons]

  exact ⟨⟨certificate_741, certificate_741_valid⟩, ⟨⟨certificate_742, certificate_742_valid⟩, ⟨⟨certificate_743, certificate_743_valid⟩, ⟨⟨certificate_744, certificate_744_valid⟩, ⟨⟨certificate_745, certificate_745_valid⟩, ⟨⟨certificate_746, certificate_746_valid⟩, ⟨⟨certificate_747, certificate_747_valid⟩, ⟨⟨certificate_748, certificate_748_valid⟩, ⟨⟨certificate_749, certificate_749_valid⟩, ⟨⟨certificate_750, certificate_750_valid⟩, ⟨⟨certificate_751, certificate_751_valid⟩, ⟨⟨certificate_752, certificate_752_valid⟩, ⟨⟨certificate_753, certificate_753_valid⟩, ⟨⟨certificate_754, certificate_754_valid⟩, ⟨⟨certificate_755, certificate_755_valid⟩, ⟨⟨certificate_756, certificate_756_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_7_5_verified : ∀ D ∈ patterns_13_7_5, PatternVerified 13 7 D := by

  simp only [patterns_13_7_5, List.forall_mem_cons]

  exact ⟨⟨certificate_757, certificate_757_valid⟩, ⟨⟨certificate_758, certificate_758_valid⟩, ⟨⟨certificate_759, certificate_759_valid⟩, ⟨⟨certificate_760, certificate_760_valid⟩, ⟨⟨certificate_761, certificate_761_valid⟩, ⟨⟨certificate_762, certificate_762_valid⟩, ⟨⟨certificate_763, certificate_763_valid⟩, ⟨⟨certificate_764, certificate_764_valid⟩, ⟨⟨certificate_765, certificate_765_valid⟩, ⟨⟨certificate_766, certificate_766_valid⟩, ⟨⟨certificate_767, certificate_767_valid⟩, ⟨⟨certificate_768, certificate_768_valid⟩, ⟨⟨certificate_769, certificate_769_valid⟩, ⟨⟨certificate_770, certificate_770_valid⟩, ⟨⟨certificate_771, certificate_771_valid⟩, ⟨⟨certificate_772, certificate_772_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_7_6_verified : ∀ D ∈ patterns_13_7_6, PatternVerified 13 7 D := by

  simp only [patterns_13_7_6, List.forall_mem_cons]

  exact ⟨⟨certificate_773, certificate_773_valid⟩, ⟨⟨certificate_774, certificate_774_valid⟩, ⟨⟨certificate_775, certificate_775_valid⟩, ⟨⟨certificate_776, certificate_776_valid⟩, ⟨⟨certificate_777, certificate_777_valid⟩, ⟨⟨certificate_778, certificate_778_valid⟩, ⟨⟨certificate_779, certificate_779_valid⟩, ⟨⟨certificate_780, certificate_780_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_7_verified : ∀ D ∈ patterns_13_7, PatternVerified 13 7 D := by

  simp only [patterns_13_7, List.forall_mem_append]

  exact ⟨patterns_13_7_0_verified, ⟨patterns_13_7_1_verified, ⟨patterns_13_7_2_verified, ⟨patterns_13_7_3_verified, ⟨patterns_13_7_4_verified, ⟨patterns_13_7_5_verified, ⟨patterns_13_7_6_verified, by simp⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_7_coverage : patternChoices 7 6 [] = patterns_13_7 := by decide +kernel

theorem finite_patterns_13_7_oai : ∀ D ∈ patternChoices 7 (13-7) [], PatternVerified 13 7 D := by

  rw [patterns_13_7_coverage]

  exact patterns_13_7_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_13_7_oai := @OAI.CycleClique.finite_patterns_13_7_oai
