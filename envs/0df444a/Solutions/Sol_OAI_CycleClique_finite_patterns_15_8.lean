-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_15_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:40:46.343889+00:00
-- url     : https://prove2.me/submissions/80991fb3-1cab-41e4-9bc3-e4d662da1362

import Mathlib
import Definitions.Def_OAIQ107D047
import Definitions.Def_OAIQ107D129
import Definitions.Def_OAIQ107D133
import Theorems.Thm_OAI_CycleClique_patterns_15_8_0_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_8_10_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_8_1_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_8_2_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_8_3_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_8_4_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_8_5_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_8_6_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_8_7_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_8_8_verified
import Theorems.Thm_OAI_CycleClique_patterns_15_8_9_verified

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates053
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1691_checked : certificate_1691.Valid 15 8 15 certificate_1691_q certificate_1691_edges 7 5 [] := by decide +kernel
theorem certificate_1691_valid : certificate_1691.Valid 15 8 (patternOrder [[],[1,1],[1,1,3]]) (patternClique [[],[1,1],[1,1,3]]) (patternEdges [[],[1,1],[1,1,3]]) (patternAmount [[],[1,1],[1,1,3]]) (patternEdgeCount [[],[1,1],[1,1,3]]) [] := certificate_1691_checked

theorem certificate_1692_checked : certificate_1692.Valid 15 8 14 certificate_1692_q certificate_1692_edges 6 5 [] := by decide +kernel
theorem certificate_1692_valid : certificate_1692.Valid 15 8 (patternOrder [[],[1,1],[1,2,1]]) (patternClique [[],[1,1],[1,2,1]]) (patternEdges [[],[1,1],[1,2,1]]) (patternAmount [[],[1,1],[1,2,1]]) (patternEdgeCount [[],[1,1],[1,2,1]]) [] := certificate_1692_checked

theorem certificate_1693_checked : certificate_1693.Valid 15 8 15 certificate_1693_q certificate_1693_edges 7 5 [] := by decide +kernel
theorem certificate_1693_valid : certificate_1693.Valid 15 8 (patternOrder [[],[1,1],[1,2,2]]) (patternClique [[],[1,1],[1,2,2]]) (patternEdges [[],[1,1],[1,2,2]]) (patternAmount [[],[1,1],[1,2,2]]) (patternEdgeCount [[],[1,1],[1,2,2]]) [] := certificate_1693_checked

theorem certificate_1694_checked : certificate_1694.Valid 15 8 15 certificate_1694_q certificate_1694_edges 7 5 [] := by decide +kernel
theorem certificate_1694_valid : certificate_1694.Valid 15 8 (patternOrder [[],[1,1],[1,3,1]]) (patternClique [[],[1,1],[1,3,1]]) (patternEdges [[],[1,1],[1,3,1]]) (patternAmount [[],[1,1],[1,3,1]]) (patternEdgeCount [[],[1,1],[1,3,1]]) [] := certificate_1694_checked

theorem certificate_1695_checked : certificate_1695.Valid 15 8 14 certificate_1695_q certificate_1695_edges 6 4 [] := by decide +kernel
theorem certificate_1695_valid : certificate_1695.Valid 15 8 (patternOrder [[],[1,1],[2],[2]]) (patternClique [[],[1,1],[2],[2]]) (patternEdges [[],[1,1],[2],[2]]) (patternAmount [[],[1,1],[2],[2]]) (patternEdgeCount [[],[1,1],[2],[2]]) [] := certificate_1695_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates054
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1696_checked : certificate_1696.Valid 15 8 15 certificate_1696_q certificate_1696_edges 7 4 [] := by decide +kernel
theorem certificate_1696_valid : certificate_1696.Valid 15 8 (patternOrder [[],[1,1],[2],[3]]) (patternClique [[],[1,1],[2],[3]]) (patternEdges [[],[1,1],[2],[3]]) (patternAmount [[],[1,1],[2],[3]]) (patternEdgeCount [[],[1,1],[2],[3]]) [] := certificate_1696_checked

theorem certificate_1697_checked : certificate_1697.Valid 15 8 15 certificate_1697_q certificate_1697_edges 7 5 [] := by decide +kernel
theorem certificate_1697_valid : certificate_1697.Valid 15 8 (patternOrder [[],[1,1],[2,1,2]]) (patternClique [[],[1,1],[2,1,2]]) (patternEdges [[],[1,1],[2,1,2]]) (patternAmount [[],[1,1],[2,1,2]]) (patternEdgeCount [[],[1,1],[2,1,2]]) [] := certificate_1697_checked

theorem certificate_1698_checked : certificate_1698.Valid 15 8 14 certificate_1698_q certificate_1698_edges 6 5 [] := by decide +kernel
theorem certificate_1698_valid : certificate_1698.Valid 15 8 (patternOrder [[],[1,1,1],[1,2]]) (patternClique [[],[1,1,1],[1,2]]) (patternEdges [[],[1,1,1],[1,2]]) (patternAmount [[],[1,1,1],[1,2]]) (patternEdgeCount [[],[1,1,1],[1,2]]) [] := certificate_1698_checked

theorem certificate_1699_checked : certificate_1699.Valid 15 8 15 certificate_1699_q certificate_1699_edges 7 5 [] := by decide +kernel
theorem certificate_1699_valid : certificate_1699.Valid 15 8 (patternOrder [[],[1,1,1],[1,3]]) (patternClique [[],[1,1,1],[1,3]]) (patternEdges [[],[1,1,1],[1,3]]) (patternAmount [[],[1,1,1],[1,3]]) (patternEdgeCount [[],[1,1,1],[1,3]]) [] := certificate_1699_checked

theorem certificate_1700_checked : certificate_1700.Valid 15 8 15 certificate_1700_q certificate_1700_edges 7 5 [] := by decide +kernel
theorem certificate_1700_valid : certificate_1700.Valid 15 8 (patternOrder [[],[1,1,1],[2,2]]) (patternClique [[],[1,1,1],[2,2]]) (patternEdges [[],[1,1,1],[2,2]]) (patternAmount [[],[1,1,1],[2,2]]) (patternEdgeCount [[],[1,1,1],[2,2]]) [] := certificate_1700_checked

theorem certificate_1701_checked : certificate_1701.Valid 15 8 14 certificate_1701_q certificate_1701_edges 6 5 [] := by decide +kernel
theorem certificate_1701_valid : certificate_1701.Valid 15 8 (patternOrder [[],[1,1,1,1],[2]]) (patternClique [[],[1,1,1,1],[2]]) (patternEdges [[],[1,1,1,1],[2]]) (patternAmount [[],[1,1,1,1],[2]]) (patternEdgeCount [[],[1,1,1,1],[2]]) [] := certificate_1701_checked

theorem certificate_1702_checked : certificate_1702.Valid 15 8 15 certificate_1702_q certificate_1702_edges 7 5 [] := by decide +kernel
theorem certificate_1702_valid : certificate_1702.Valid 15 8 (patternOrder [[],[1,1,1,1],[3]]) (patternClique [[],[1,1,1,1],[3]]) (patternEdges [[],[1,1,1,1],[3]]) (patternAmount [[],[1,1,1,1],[3]]) (patternEdgeCount [[],[1,1,1,1],[3]]) [] := certificate_1702_checked

theorem certificate_1703_checked : certificate_1703.Valid 15 8 14 certificate_1703_q certificate_1703_edges 6 6 [] := by decide +kernel
theorem certificate_1703_valid : certificate_1703.Valid 15 8 (patternOrder [[],[1,1,1,1,1,1]]) (patternClique [[],[1,1,1,1,1,1]]) (patternEdges [[],[1,1,1,1,1,1]]) (patternAmount [[],[1,1,1,1,1,1]]) (patternEdgeCount [[],[1,1,1,1,1,1]]) [] := certificate_1703_checked

theorem certificate_1704_checked : certificate_1704.Valid 15 8 15 certificate_1704_q certificate_1704_edges 7 6 [] := by decide +kernel
theorem certificate_1704_valid : certificate_1704.Valid 15 8 (patternOrder [[],[1,1,1,1,1,2]]) (patternClique [[],[1,1,1,1,1,2]]) (patternEdges [[],[1,1,1,1,1,2]]) (patternAmount [[],[1,1,1,1,1,2]]) (patternEdgeCount [[],[1,1,1,1,1,2]]) [] := certificate_1704_checked

theorem certificate_1705_checked : certificate_1705.Valid 15 8 15 certificate_1705_q certificate_1705_edges 7 6 [] := by decide +kernel
theorem certificate_1705_valid : certificate_1705.Valid 15 8 (patternOrder [[],[1,1,1,1,2,1]]) (patternClique [[],[1,1,1,1,2,1]]) (patternEdges [[],[1,1,1,1,2,1]]) (patternAmount [[],[1,1,1,1,2,1]]) (patternEdgeCount [[],[1,1,1,1,2,1]]) [] := certificate_1705_checked

theorem certificate_1706_checked : certificate_1706.Valid 15 8 15 certificate_1706_q certificate_1706_edges 7 5 [] := by decide +kernel
theorem certificate_1706_valid : certificate_1706.Valid 15 8 (patternOrder [[],[1,1,1,2],[2]]) (patternClique [[],[1,1,1,2],[2]]) (patternEdges [[],[1,1,1,2],[2]]) (patternAmount [[],[1,1,1,2],[2]]) (patternEdgeCount [[],[1,1,1,2],[2]]) [] := certificate_1706_checked

theorem certificate_1707_checked : certificate_1707.Valid 15 8 15 certificate_1707_q certificate_1707_edges 7 6 [] := by decide +kernel
theorem certificate_1707_valid : certificate_1707.Valid 15 8 (patternOrder [[],[1,1,1,2,1,1]]) (patternClique [[],[1,1,1,2,1,1]]) (patternEdges [[],[1,1,1,2,1,1]]) (patternAmount [[],[1,1,1,2,1,1]]) (patternEdgeCount [[],[1,1,1,2,1,1]]) [] := certificate_1707_checked

theorem certificate_1708_checked : certificate_1708.Valid 15 8 15 certificate_1708_q certificate_1708_edges 7 5 [] := by decide +kernel
theorem certificate_1708_valid : certificate_1708.Valid 15 8 (patternOrder [[],[1,1,2],[1,2]]) (patternClique [[],[1,1,2],[1,2]]) (patternEdges [[],[1,1,2],[1,2]]) (patternAmount [[],[1,1,2],[1,2]]) (patternEdgeCount [[],[1,1,2],[1,2]]) [] := certificate_1708_checked

theorem certificate_1709_checked : certificate_1709.Valid 15 8 15 certificate_1709_q certificate_1709_edges 7 5 [] := by decide +kernel
theorem certificate_1709_valid : certificate_1709.Valid 15 8 (patternOrder [[],[1,1,2,1],[2]]) (patternClique [[],[1,1,2,1],[2]]) (patternEdges [[],[1,1,2,1],[2]]) (patternAmount [[],[1,1,2,1],[2]]) (patternEdgeCount [[],[1,1,2,1],[2]]) [] := certificate_1709_checked

theorem certificate_1710_checked : certificate_1710.Valid 15 8 15 certificate_1710_q certificate_1710_edges 7 5 [] := by decide +kernel
theorem certificate_1710_valid : certificate_1710.Valid 15 8 (patternOrder [[],[1,2],[1,2,1]]) (patternClique [[],[1,2],[1,2,1]]) (patternEdges [[],[1,2],[1,2,1]]) (patternAmount [[],[1,2],[1,2,1]]) (patternEdgeCount [[],[1,2],[1,2,1]]) [] := certificate_1710_checked

theorem certificate_1711_checked : certificate_1711.Valid 15 8 15 certificate_1711_q certificate_1711_edges 7 4 [] := by decide +kernel
theorem certificate_1711_valid : certificate_1711.Valid 15 8 (patternOrder [[],[1,2],[2],[2]]) (patternClique [[],[1,2],[2],[2]]) (patternEdges [[],[1,2],[2],[2]]) (patternAmount [[],[1,2],[2],[2]]) (patternEdgeCount [[],[1,2],[2],[2]]) [] := certificate_1711_checked

theorem certificate_1712_checked : certificate_1712.Valid 15 8 12 certificate_1712_q certificate_1712_edges 4 4 [] := by decide +kernel
theorem certificate_1712_valid : certificate_1712.Valid 15 8 (patternOrder [[1],[1],[1],[1]]) (patternClique [[1],[1],[1],[1]]) (patternEdges [[1],[1],[1],[1]]) (patternAmount [[1],[1],[1],[1]]) (patternEdgeCount [[1],[1],[1],[1]]) [] := certificate_1712_checked

theorem certificate_1713_checked : certificate_1713.Valid 15 8 13 certificate_1713_q certificate_1713_edges 5 4 [] := by decide +kernel
theorem certificate_1713_valid : certificate_1713.Valid 15 8 (patternOrder [[1],[1],[1],[2]]) (patternClique [[1],[1],[1],[2]]) (patternEdges [[1],[1],[1],[2]]) (patternAmount [[1],[1],[1],[2]]) (patternEdgeCount [[1],[1],[1],[2]]) [] := certificate_1713_checked

theorem certificate_1714_checked : certificate_1714.Valid 15 8 14 certificate_1714_q certificate_1714_edges 6 4 [] := by decide +kernel
theorem certificate_1714_valid : certificate_1714.Valid 15 8 (patternOrder [[1],[1],[1],[3]]) (patternClique [[1],[1],[1],[3]]) (patternEdges [[1],[1],[1],[3]]) (patternAmount [[1],[1],[1],[3]]) (patternEdgeCount [[1],[1],[1],[3]]) [] := certificate_1714_checked

theorem certificate_1715_checked : certificate_1715.Valid 15 8 15 certificate_1715_q certificate_1715_edges 7 4 [] := by decide +kernel
theorem certificate_1715_valid : certificate_1715.Valid 15 8 (patternOrder [[1],[1],[1],[4]]) (patternClique [[1],[1],[1],[4]]) (patternEdges [[1],[1],[1],[4]]) (patternAmount [[1],[1],[1],[4]]) (patternEdgeCount [[1],[1],[1],[4]]) [] := certificate_1715_checked

theorem certificate_1716_checked : certificate_1716.Valid 15 8 13 certificate_1716_q certificate_1716_edges 5 5 [] := by decide +kernel
theorem certificate_1716_valid : certificate_1716.Valid 15 8 (patternOrder [[1],[1],[1,1,1]]) (patternClique [[1],[1],[1,1,1]]) (patternEdges [[1],[1],[1,1,1]]) (patternAmount [[1],[1],[1,1,1]]) (patternEdgeCount [[1],[1],[1,1,1]]) [] := certificate_1716_checked

theorem certificate_1717_checked : certificate_1717.Valid 15 8 14 certificate_1717_q certificate_1717_edges 6 5 [] := by decide +kernel
theorem certificate_1717_valid : certificate_1717.Valid 15 8 (patternOrder [[1],[1],[1,1,2]]) (patternClique [[1],[1],[1,1,2]]) (patternEdges [[1],[1],[1,1,2]]) (patternAmount [[1],[1],[1,1,2]]) (patternEdgeCount [[1],[1],[1,1,2]]) [] := certificate_1717_checked

theorem certificate_1718_checked : certificate_1718.Valid 15 8 15 certificate_1718_q certificate_1718_edges 7 5 [] := by decide +kernel
theorem certificate_1718_valid : certificate_1718.Valid 15 8 (patternOrder [[1],[1],[1,1,3]]) (patternClique [[1],[1],[1,1,3]]) (patternEdges [[1],[1],[1,1,3]]) (patternAmount [[1],[1],[1,1,3]]) (patternEdgeCount [[1],[1],[1,1,3]]) [] := certificate_1718_checked

theorem certificate_1719_checked : certificate_1719.Valid 15 8 14 certificate_1719_q certificate_1719_edges 6 5 [] := by decide +kernel
theorem certificate_1719_valid : certificate_1719.Valid 15 8 (patternOrder [[1],[1],[1,2,1]]) (patternClique [[1],[1],[1,2,1]]) (patternEdges [[1],[1],[1,2,1]]) (patternAmount [[1],[1],[1,2,1]]) (patternEdgeCount [[1],[1],[1,2,1]]) [] := certificate_1719_checked

theorem certificate_1720_checked : certificate_1720.Valid 15 8 15 certificate_1720_q certificate_1720_edges 7 5 [] := by decide +kernel
theorem certificate_1720_valid : certificate_1720.Valid 15 8 (patternOrder [[1],[1],[1,2,2]]) (patternClique [[1],[1],[1,2,2]]) (patternEdges [[1],[1],[1,2,2]]) (patternAmount [[1],[1],[1,2,2]]) (patternEdgeCount [[1],[1],[1,2,2]]) [] := certificate_1720_checked

theorem certificate_1721_checked : certificate_1721.Valid 15 8 15 certificate_1721_q certificate_1721_edges 7 5 [] := by decide +kernel
theorem certificate_1721_valid : certificate_1721.Valid 15 8 (patternOrder [[1],[1],[1,3,1]]) (patternClique [[1],[1],[1,3,1]]) (patternEdges [[1],[1],[1,3,1]]) (patternAmount [[1],[1],[1,3,1]]) (patternEdgeCount [[1],[1],[1,3,1]]) [] := certificate_1721_checked

theorem certificate_1722_checked : certificate_1722.Valid 15 8 14 certificate_1722_q certificate_1722_edges 6 4 [] := by decide +kernel
theorem certificate_1722_valid : certificate_1722.Valid 15 8 (patternOrder [[1],[1],[2],[2]]) (patternClique [[1],[1],[2],[2]]) (patternEdges [[1],[1],[2],[2]]) (patternAmount [[1],[1],[2],[2]]) (patternEdgeCount [[1],[1],[2],[2]]) [] := certificate_1722_checked

theorem certificate_1723_checked : certificate_1723.Valid 15 8 15 certificate_1723_q certificate_1723_edges 7 4 [] := by decide +kernel
theorem certificate_1723_valid : certificate_1723.Valid 15 8 (patternOrder [[1],[1],[2],[3]]) (patternClique [[1],[1],[2],[3]]) (patternEdges [[1],[1],[2],[3]]) (patternAmount [[1],[1],[2],[3]]) (patternEdgeCount [[1],[1],[2],[3]]) [] := certificate_1723_checked

theorem certificate_1724_checked : certificate_1724.Valid 15 8 15 certificate_1724_q certificate_1724_edges 7 5 [] := by decide +kernel
theorem certificate_1724_valid : certificate_1724.Valid 15 8 (patternOrder [[1],[1],[2,1,2]]) (patternClique [[1],[1],[2,1,2]]) (patternEdges [[1],[1],[2,1,2]]) (patternAmount [[1],[1],[2,1,2]]) (patternEdgeCount [[1],[1],[2,1,2]]) [] := certificate_1724_checked

theorem certificate_1725_checked : certificate_1725.Valid 15 8 13 certificate_1725_q certificate_1725_edges 5 5 [] := by decide +kernel
theorem certificate_1725_valid : certificate_1725.Valid 15 8 (patternOrder [[1],[1,1],[1,1]]) (patternClique [[1],[1,1],[1,1]]) (patternEdges [[1],[1,1],[1,1]]) (patternAmount [[1],[1,1],[1,1]]) (patternEdgeCount [[1],[1,1],[1,1]]) [] := certificate_1725_checked

theorem certificate_1726_checked : certificate_1726.Valid 15 8 14 certificate_1726_q certificate_1726_edges 6 5 [] := by decide +kernel
theorem certificate_1726_valid : certificate_1726.Valid 15 8 (patternOrder [[1],[1,1],[1,2]]) (patternClique [[1],[1,1],[1,2]]) (patternEdges [[1],[1,1],[1,2]]) (patternAmount [[1],[1,1],[1,2]]) (patternEdgeCount [[1],[1,1],[1,2]]) [] := certificate_1726_checked

theorem certificate_1727_checked : certificate_1727.Valid 15 8 15 certificate_1727_q certificate_1727_edges 7 5 [] := by decide +kernel
theorem certificate_1727_valid : certificate_1727.Valid 15 8 (patternOrder [[1],[1,1],[1,3]]) (patternClique [[1],[1,1],[1,3]]) (patternEdges [[1],[1,1],[1,3]]) (patternAmount [[1],[1,1],[1,3]]) (patternEdgeCount [[1],[1,1],[1,3]]) [] := certificate_1727_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates055
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_1728_checked : certificate_1728.Valid 15 8 15 certificate_1728_q certificate_1728_edges 7 5 [] := by decide +kernel
theorem certificate_1728_valid : certificate_1728.Valid 15 8 (patternOrder [[1],[1,1],[2,2]]) (patternClique [[1],[1,1],[2,2]]) (patternEdges [[1],[1,1],[2,2]]) (patternAmount [[1],[1,1],[2,2]]) (patternEdgeCount [[1],[1,1],[2,2]]) [] := certificate_1728_checked

theorem certificate_1729_checked : certificate_1729.Valid 15 8 14 certificate_1729_q certificate_1729_edges 6 5 [] := by decide +kernel
theorem certificate_1729_valid : certificate_1729.Valid 15 8 (patternOrder [[1],[1,1,1],[2]]) (patternClique [[1],[1,1,1],[2]]) (patternEdges [[1],[1,1,1],[2]]) (patternAmount [[1],[1,1,1],[2]]) (patternEdgeCount [[1],[1,1,1],[2]]) [] := certificate_1729_checked

theorem certificate_1730_checked : certificate_1730.Valid 15 8 15 certificate_1730_q certificate_1730_edges 7 5 [] := by decide +kernel
theorem certificate_1730_valid : certificate_1730.Valid 15 8 (patternOrder [[1],[1,1,1],[3]]) (patternClique [[1],[1,1,1],[3]]) (patternEdges [[1],[1,1,1],[3]]) (patternAmount [[1],[1,1,1],[3]]) (patternEdgeCount [[1],[1,1,1],[3]]) [] := certificate_1730_checked

theorem certificate_1731_checked : certificate_1731.Valid 15 8 14 certificate_1731_q certificate_1731_edges 6 6 [] := by decide +kernel
theorem certificate_1731_valid : certificate_1731.Valid 15 8 (patternOrder [[1],[1,1,1,1,1]]) (patternClique [[1],[1,1,1,1,1]]) (patternEdges [[1],[1,1,1,1,1]]) (patternAmount [[1],[1,1,1,1,1]]) (patternEdgeCount [[1],[1,1,1,1,1]]) [] := certificate_1731_checked

theorem certificate_1732_checked : certificate_1732.Valid 15 8 15 certificate_1732_q certificate_1732_edges 7 6 [] := by decide +kernel
theorem certificate_1732_valid : certificate_1732.Valid 15 8 (patternOrder [[1],[1,1,1,1,2]]) (patternClique [[1],[1,1,1,1,2]]) (patternEdges [[1],[1,1,1,1,2]]) (patternAmount [[1],[1,1,1,1,2]]) (patternEdgeCount [[1],[1,1,1,1,2]]) [] := certificate_1732_checked

theorem certificate_1733_checked : certificate_1733.Valid 15 8 15 certificate_1733_q certificate_1733_edges 7 6 [] := by decide +kernel
theorem certificate_1733_valid : certificate_1733.Valid 15 8 (patternOrder [[1],[1,1,1,2,1]]) (patternClique [[1],[1,1,1,2,1]]) (patternEdges [[1],[1,1,1,2,1]]) (patternAmount [[1],[1,1,1,2,1]]) (patternEdgeCount [[1],[1,1,1,2,1]]) [] := certificate_1733_checked

theorem certificate_1734_checked : certificate_1734.Valid 15 8 15 certificate_1734_q certificate_1734_edges 7 5 [] := by decide +kernel
theorem certificate_1734_valid : certificate_1734.Valid 15 8 (patternOrder [[1],[1,1,2],[2]]) (patternClique [[1],[1,1,2],[2]]) (patternEdges [[1],[1,1,2],[2]]) (patternAmount [[1],[1,1,2],[2]]) (patternEdgeCount [[1],[1,1,2],[2]]) [] := certificate_1734_checked

theorem certificate_1735_checked : certificate_1735.Valid 15 8 15 certificate_1735_q certificate_1735_edges 7 6 [] := by decide +kernel
theorem certificate_1735_valid : certificate_1735.Valid 15 8 (patternOrder [[1],[1,1,2,1,1]]) (patternClique [[1],[1,1,2,1,1]]) (patternEdges [[1],[1,1,2,1,1]]) (patternAmount [[1],[1,1,2,1,1]]) (patternEdgeCount [[1],[1,1,2,1,1]]) [] := certificate_1735_checked

theorem certificate_1736_checked : certificate_1736.Valid 15 8 15 certificate_1736_q certificate_1736_edges 7 5 [] := by decide +kernel
theorem certificate_1736_valid : certificate_1736.Valid 15 8 (patternOrder [[1],[1,2],[1,2]]) (patternClique [[1],[1,2],[1,2]]) (patternEdges [[1],[1,2],[1,2]]) (patternAmount [[1],[1,2],[1,2]]) (patternEdgeCount [[1],[1,2],[1,2]]) [] := certificate_1736_checked

theorem certificate_1737_checked : certificate_1737.Valid 15 8 15 certificate_1737_q certificate_1737_edges 7 5 [] := by decide +kernel
theorem certificate_1737_valid : certificate_1737.Valid 15 8 (patternOrder [[1],[1,2,1],[2]]) (patternClique [[1],[1,2,1],[2]]) (patternEdges [[1],[1,2,1],[2]]) (patternAmount [[1],[1,2,1],[2]]) (patternEdgeCount [[1],[1,2,1],[2]]) [] := certificate_1737_checked

theorem certificate_1738_checked : certificate_1738.Valid 15 8 15 certificate_1738_q certificate_1738_edges 7 4 [] := by decide +kernel
theorem certificate_1738_valid : certificate_1738.Valid 15 8 (patternOrder [[1],[2],[2],[2]]) (patternClique [[1],[2],[2],[2]]) (patternEdges [[1],[2],[2],[2]]) (patternAmount [[1],[2],[2],[2]]) (patternEdgeCount [[1],[2],[2],[2]]) [] := certificate_1738_checked

theorem certificate_1739_checked : certificate_1739.Valid 15 8 14 certificate_1739_q certificate_1739_edges 6 5 [] := by decide +kernel
theorem certificate_1739_valid : certificate_1739.Valid 15 8 (patternOrder [[1,1],[1,1],[2]]) (patternClique [[1,1],[1,1],[2]]) (patternEdges [[1,1],[1,1],[2]]) (patternAmount [[1,1],[1,1],[2]]) (patternEdgeCount [[1,1],[1,1],[2]]) [] := certificate_1739_checked

theorem certificate_1740_checked : certificate_1740.Valid 15 8 15 certificate_1740_q certificate_1740_edges 7 5 [] := by decide +kernel
theorem certificate_1740_valid : certificate_1740.Valid 15 8 (patternOrder [[1,1],[1,1],[3]]) (patternClique [[1,1],[1,1],[3]]) (patternEdges [[1,1],[1,1],[3]]) (patternAmount [[1,1],[1,1],[3]]) (patternEdgeCount [[1,1],[1,1],[3]]) [] := certificate_1740_checked

theorem certificate_1741_checked : certificate_1741.Valid 15 8 14 certificate_1741_q certificate_1741_edges 6 6 [] := by decide +kernel
theorem certificate_1741_valid : certificate_1741.Valid 15 8 (patternOrder [[1,1],[1,1,1,1]]) (patternClique [[1,1],[1,1,1,1]]) (patternEdges [[1,1],[1,1,1,1]]) (patternAmount [[1,1],[1,1,1,1]]) (patternEdgeCount [[1,1],[1,1,1,1]]) [] := certificate_1741_checked

theorem certificate_1742_checked : certificate_1742.Valid 15 8 15 certificate_1742_q certificate_1742_edges 7 6 [] := by decide +kernel
theorem certificate_1742_valid : certificate_1742.Valid 15 8 (patternOrder [[1,1],[1,1,1,2]]) (patternClique [[1,1],[1,1,1,2]]) (patternEdges [[1,1],[1,1,1,2]]) (patternAmount [[1,1],[1,1,1,2]]) (patternEdgeCount [[1,1],[1,1,1,2]]) [] := certificate_1742_checked

theorem certificate_1743_checked : certificate_1743.Valid 15 8 15 certificate_1743_q certificate_1743_edges 7 6 [] := by decide +kernel
theorem certificate_1743_valid : certificate_1743.Valid 15 8 (patternOrder [[1,1],[1,1,2,1]]) (patternClique [[1,1],[1,1,2,1]]) (patternEdges [[1,1],[1,1,2,1]]) (patternAmount [[1,1],[1,1,2,1]]) (patternEdgeCount [[1,1],[1,1,2,1]]) [] := certificate_1743_checked

theorem certificate_1744_checked : certificate_1744.Valid 15 8 15 certificate_1744_q certificate_1744_edges 7 5 [] := by decide +kernel
theorem certificate_1744_valid : certificate_1744.Valid 15 8 (patternOrder [[1,1],[1,2],[2]]) (patternClique [[1,1],[1,2],[2]]) (patternEdges [[1,1],[1,2],[2]]) (patternAmount [[1,1],[1,2],[2]]) (patternEdgeCount [[1,1],[1,2],[2]]) [] := certificate_1744_checked

theorem certificate_1745_checked : certificate_1745.Valid 15 8 14 certificate_1745_q certificate_1745_edges 6 6 [] := by decide +kernel
theorem certificate_1745_valid : certificate_1745.Valid 15 8 (patternOrder [[1,1,1],[1,1,1]]) (patternClique [[1,1,1],[1,1,1]]) (patternEdges [[1,1,1],[1,1,1]]) (patternAmount [[1,1,1],[1,1,1]]) (patternEdgeCount [[1,1,1],[1,1,1]]) [] := certificate_1745_checked

theorem certificate_1746_checked : certificate_1746.Valid 15 8 15 certificate_1746_q certificate_1746_edges 7 6 [] := by decide +kernel
theorem certificate_1746_valid : certificate_1746.Valid 15 8 (patternOrder [[1,1,1],[1,1,2]]) (patternClique [[1,1,1],[1,1,2]]) (patternEdges [[1,1,1],[1,1,2]]) (patternAmount [[1,1,1],[1,1,2]]) (patternEdgeCount [[1,1,1],[1,1,2]]) [] := certificate_1746_checked

theorem certificate_1747_checked : certificate_1747.Valid 15 8 15 certificate_1747_q certificate_1747_edges 7 6 [] := by decide +kernel
theorem certificate_1747_valid : certificate_1747.Valid 15 8 (patternOrder [[1,1,1],[1,2,1]]) (patternClique [[1,1,1],[1,2,1]]) (patternEdges [[1,1,1],[1,2,1]]) (patternAmount [[1,1,1],[1,2,1]]) (patternEdgeCount [[1,1,1],[1,2,1]]) [] := certificate_1747_checked

theorem certificate_1748_checked : certificate_1748.Valid 15 8 15 certificate_1748_q certificate_1748_edges 7 5 [] := by decide +kernel
theorem certificate_1748_valid : certificate_1748.Valid 15 8 (patternOrder [[1,1,1],[2],[2]]) (patternClique [[1,1,1],[2],[2]]) (patternEdges [[1,1,1],[2],[2]]) (patternAmount [[1,1,1],[2],[2]]) (patternEdgeCount [[1,1,1],[2],[2]]) [] := certificate_1748_checked

theorem certificate_1749_checked : certificate_1749.Valid 15 8 15 certificate_1749_q certificate_1749_edges 7 6 [] := by decide +kernel
theorem certificate_1749_valid : certificate_1749.Valid 15 8 (patternOrder [[1,1,1,1],[1,2]]) (patternClique [[1,1,1,1],[1,2]]) (patternEdges [[1,1,1,1],[1,2]]) (patternAmount [[1,1,1,1],[1,2]]) (patternEdgeCount [[1,1,1,1],[1,2]]) [] := certificate_1749_checked

theorem certificate_1750_checked : certificate_1750.Valid 15 8 15 certificate_1750_q certificate_1750_edges 7 6 [] := by decide +kernel
theorem certificate_1750_valid : certificate_1750.Valid 15 8 (patternOrder [[1,1,1,1,1],[2]]) (patternClique [[1,1,1,1,1],[2]]) (patternEdges [[1,1,1,1,1],[2]]) (patternAmount [[1,1,1,1,1],[2]]) (patternEdgeCount [[1,1,1,1,1],[2]]) [] := certificate_1750_checked

theorem certificate_1751_checked : certificate_1751.Valid 15 8 15 certificate_1751_q certificate_1751_edges 7 7 [] := by decide +kernel
theorem certificate_1751_valid : certificate_1751.Valid 15 8 (patternOrder [[1,1,1,1,1,1,1]]) (patternClique [[1,1,1,1,1,1,1]]) (patternEdges [[1,1,1,1,1,1,1]]) (patternAmount [[1,1,1,1,1,1,1]]) (patternEdgeCount [[1,1,1,1,1,1,1]]) [] := certificate_1751_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns15x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_15_8_11_verified : ∀ D ∈ patterns_15_8_11, PatternVerified 15 8 D := by

  simp only [patterns_15_8_11, List.forall_mem_cons]

  exact ⟨⟨certificate_1691, certificate_1691_valid⟩, ⟨⟨certificate_1692, certificate_1692_valid⟩, ⟨⟨certificate_1693, certificate_1693_valid⟩, ⟨⟨certificate_1694, certificate_1694_valid⟩, ⟨⟨certificate_1695, certificate_1695_valid⟩, ⟨⟨certificate_1696, certificate_1696_valid⟩, ⟨⟨certificate_1697, certificate_1697_valid⟩, ⟨⟨certificate_1698, certificate_1698_valid⟩, ⟨⟨certificate_1699, certificate_1699_valid⟩, ⟨⟨certificate_1700, certificate_1700_valid⟩, ⟨⟨certificate_1701, certificate_1701_valid⟩, ⟨⟨certificate_1702, certificate_1702_valid⟩, ⟨⟨certificate_1703, certificate_1703_valid⟩, ⟨⟨certificate_1704, certificate_1704_valid⟩, ⟨⟨certificate_1705, certificate_1705_valid⟩, ⟨⟨certificate_1706, certificate_1706_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_8_12_verified : ∀ D ∈ patterns_15_8_12, PatternVerified 15 8 D := by

  simp only [patterns_15_8_12, List.forall_mem_cons]

  exact ⟨⟨certificate_1707, certificate_1707_valid⟩, ⟨⟨certificate_1708, certificate_1708_valid⟩, ⟨⟨certificate_1709, certificate_1709_valid⟩, ⟨⟨certificate_1710, certificate_1710_valid⟩, ⟨⟨certificate_1711, certificate_1711_valid⟩, ⟨⟨certificate_1712, certificate_1712_valid⟩, ⟨⟨certificate_1713, certificate_1713_valid⟩, ⟨⟨certificate_1714, certificate_1714_valid⟩, ⟨⟨certificate_1715, certificate_1715_valid⟩, ⟨⟨certificate_1716, certificate_1716_valid⟩, ⟨⟨certificate_1717, certificate_1717_valid⟩, ⟨⟨certificate_1718, certificate_1718_valid⟩, ⟨⟨certificate_1719, certificate_1719_valid⟩, ⟨⟨certificate_1720, certificate_1720_valid⟩, ⟨⟨certificate_1721, certificate_1721_valid⟩, ⟨⟨certificate_1722, certificate_1722_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_8_13_verified : ∀ D ∈ patterns_15_8_13, PatternVerified 15 8 D := by

  simp only [patterns_15_8_13, List.forall_mem_cons]

  exact ⟨⟨certificate_1723, certificate_1723_valid⟩, ⟨⟨certificate_1724, certificate_1724_valid⟩, ⟨⟨certificate_1725, certificate_1725_valid⟩, ⟨⟨certificate_1726, certificate_1726_valid⟩, ⟨⟨certificate_1727, certificate_1727_valid⟩, ⟨⟨certificate_1728, certificate_1728_valid⟩, ⟨⟨certificate_1729, certificate_1729_valid⟩, ⟨⟨certificate_1730, certificate_1730_valid⟩, ⟨⟨certificate_1731, certificate_1731_valid⟩, ⟨⟨certificate_1732, certificate_1732_valid⟩, ⟨⟨certificate_1733, certificate_1733_valid⟩, ⟨⟨certificate_1734, certificate_1734_valid⟩, ⟨⟨certificate_1735, certificate_1735_valid⟩, ⟨⟨certificate_1736, certificate_1736_valid⟩, ⟨⟨certificate_1737, certificate_1737_valid⟩, ⟨⟨certificate_1738, certificate_1738_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_8_14_verified : ∀ D ∈ patterns_15_8_14, PatternVerified 15 8 D := by

  simp only [patterns_15_8_14, List.forall_mem_cons]

  exact ⟨⟨certificate_1739, certificate_1739_valid⟩, ⟨⟨certificate_1740, certificate_1740_valid⟩, ⟨⟨certificate_1741, certificate_1741_valid⟩, ⟨⟨certificate_1742, certificate_1742_valid⟩, ⟨⟨certificate_1743, certificate_1743_valid⟩, ⟨⟨certificate_1744, certificate_1744_valid⟩, ⟨⟨certificate_1745, certificate_1745_valid⟩, ⟨⟨certificate_1746, certificate_1746_valid⟩, ⟨⟨certificate_1747, certificate_1747_valid⟩, ⟨⟨certificate_1748, certificate_1748_valid⟩, ⟨⟨certificate_1749, certificate_1749_valid⟩, ⟨⟨certificate_1750, certificate_1750_valid⟩, ⟨⟨certificate_1751, certificate_1751_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_8_verified : ∀ D ∈ patterns_15_8, PatternVerified 15 8 D := by

  simp only [patterns_15_8, List.forall_mem_append]

  exact ⟨patterns_15_8_0_verified, ⟨patterns_15_8_1_verified, ⟨patterns_15_8_2_verified, ⟨patterns_15_8_3_verified, ⟨patterns_15_8_4_verified, ⟨patterns_15_8_5_verified, ⟨patterns_15_8_6_verified, ⟨patterns_15_8_7_verified, ⟨patterns_15_8_8_verified, ⟨patterns_15_8_9_verified, ⟨patterns_15_8_10_verified, ⟨patterns_15_8_11_verified, ⟨patterns_15_8_12_verified, ⟨patterns_15_8_13_verified, ⟨patterns_15_8_14_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_8_coverage : patternChoices 8 7 [] = patterns_15_8 := by decide +kernel

theorem finite_patterns_15_8_oai : ∀ D ∈ patternChoices 8 (15-8) [], PatternVerified 15 8 D := by

  rw [patterns_15_8_coverage]

  exact patterns_15_8_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_15_8_oai := @OAI.CycleClique.finite_patterns_15_8_oai
