-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Quadratic.B_ASE
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:21:43.669979+00:00
-- url     : https://prove2.me/submissions/bb460449-6de8-4dc4-aa02-872872d4fe40

import Mathlib
import Definitions.Def_OAIQ091C005
import Definitions.Def_OAIQ091C012
import Theorems.Thm_OAI_PositiveEinsteinFour_Quadratic_combine_quadratic_nonneg
import Theorems.Thm_OAI_PositiveEinsteinFour_quadratic_form_nonneg_of_det

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates00
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The finite matrix certificates for the quadratic coupling estimate. -/

namespace PositiveEinsteinFour.Quadratic

open Potential

noncomputable section

private theorem B_ASE_hc0 (x y : ℝ) : 0 ≤ (801184320 * x ^ 2 + 2 * (-411481728) * x * y + 268058655 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 801184320 268058655 (-411481728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc1 (x y : ℝ) : 0 ≤ (8214628800 * x ^ 2 + 2 * (-4609025856) * x * y + 3173049120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 8214628800 3173049120 (-4609025856)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc2 (x y : ℝ) : 0 ≤ (36441336000 * x ^ 2 + 2 * (-22148058240) * x * y + 16173052200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 36441336000 16173052200 (-22148058240)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc3 (x y : ℝ) : 0 ≤ (91489281600 * x ^ 2 + 2 * (-59794467648) * x * y + 46429159680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 91489281600 46429159680 (-59794467648)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc4 (x y : ℝ) : 0 ≤ (142481379840 * x ^ 2 + 2 * (-99599797632) * x * y + 82527394560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 142481379840 82527394560 (-99599797632)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc5 (x y : ℝ) : 0 ≤ (141421989120 * x ^ 2 + 2 * (-105489283584) * x * y + 93954693120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 141421989120 93954693120 (-105489283584)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc6 (x y : ℝ) : 0 ≤ (87917245440 * x ^ 2 + 2 * (-70186266624) * x * y + 68211588480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 87917245440 68211588480 (-70186266624)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc7 (x y : ℝ) : 0 ≤ (31795461120 * x ^ 2 + 2 * (-27574459392) * x * y + 30182983680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 31795461120 30182983680 (-27574459392)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc8 (x y : ℝ) : 0 ≤ (5472952320 * x ^ 2 + 2 * (-5447534592) * x * y + 7247950080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 5472952320 7247950080 (-5447534592)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc9 (x y : ℝ) : 0 ≤ (192737280 * x ^ 2 + 2 * (-325902336) * x * y + 688128000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 192737280 688128000 (-325902336)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc10 (x y : ℝ) : 0 ≤ (6659768160 * x ^ 2 + 2 * (-3774480192) * x * y + 2668414545 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6659768160 2668414545 (-3774480192)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc11 (x y : ℝ) : 0 ≤ (60646594240 * x ^ 2 + 2 * (-37331662752) * x * y + 27635018260 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 60646594240 27635018260 (-37331662752)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc12 (x y : ℝ) : 0 ≤ (235423411680 * x ^ 2 + 2 * (-155814545568) * x * y + 121565829680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 235423411680 121565829680 (-155814545568)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc13 (x y : ℝ) : 0 ≤ (507118147840 * x ^ 2 + 2 * (-357917622720) * x * y + 295612856080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 507118147840 295612856080 (-357917622720)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc14 (x y : ℝ) : 0 ≤ (659659999360 * x ^ 2 + 2 * (-493466728320) * x * y + 433564336480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 659659999360 433564336480 (-493466728320)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc15 (x y : ℝ) : 0 ≤ (526172846080 * x ^ 2 + 2 * (-415755199488) * x * y + 391746174400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 526172846080 391746174400 (-415755199488)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc16 (x y : ℝ) : 0 ≤ (247457405440 * x ^ 2 + 2 * (-206650360320) * x * y + 212023863040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 247457405440 212023863040 (-206650360320)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc17 (x y : ℝ) : 0 ≤ (60737986560 * x ^ 2 + 2 * (-54076234752) * x * y + 62300025600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 60737986560 62300025600 (-54076234752)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc18 (x y : ℝ) : 0 ≤ (5474990080 * x ^ 2 + 2 * (-5374605312) * x * y + 7471182080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 5474990080 7471182080 (-5374605312)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc19 (x y : ℝ) : 0 ≤ (24731126870 * x ^ 2 + 2 * (-15706834722) * x * y + 12111070085 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 24731126870 12111070085 (-15706834722)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc20 (x y : ℝ) : 0 ≤ (197409465390 * x ^ 2 + 2 * (-134329715382) * x * y + 106918811160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 197409465390 106918811160 (-134329715382)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc21 (x y : ℝ) : 0 ≤ (657946610000 * x ^ 2 + 2 * (-475149772500) * x * y + 394891295780 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 657946610000 394891295780 (-475149772500)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc22 (x y : ℝ) : 0 ≤ (1183535463800 * x ^ 2 + 2 * (-900172885536) * x * y + 787188651920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1183535463800 787188651920 (-900172885536)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc23 (x y : ℝ) : 0 ≤ (1235628716960 * x ^ 2 + 2 * (-983906926368) * x * y + 911786934320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1235628716960 911786934320 (-983906926368)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc24 (x y : ℝ) : 0 ≤ (743250805280 * x ^ 2 + 2 * (-617063256096) * x * y + 611770981760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 743250805280 611770981760 (-617063256096)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc25 (x y : ℝ) : 0 ≤ (235335540480 * x ^ 2 + 2 * (-203336929728) * x * y + 219136635840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 235335540480 219136635840 (-203336929728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc26 (x y : ℝ) : 0 ≤ (29446259840 * x ^ 2 + 2 * (-26534885376) * x * y + 32047020800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 29446259840 32047020800 (-26534885376)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc27 (x y : ℝ) : 0 ≤ (54548120435 * x ^ 2 + 2 * (-38984838126) * x * y + 32521501695 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 54548120435 32521501695 (-38984838126)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc28 (x y : ℝ) : 0 ≤ (373454270660 * x ^ 2 + 2 * (-280638182172) * x * y + 238451526660 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 373454270660 238451526660 (-280638182172)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc29 (x y : ℝ) : 0 ≤ (1037775174300 * x ^ 2 + 2 * (-814280610348) * x * y + 715975698860 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1037775174300 715975698860 (-814280610348)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc30 (x y : ℝ) : 0 ≤ (1495013327520 * x ^ 2 + 2 * (-1217537869200) * x * y + 1119956796960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1495013327520 1119956796960 (-1217537869200)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc31 (x y : ℝ) : 0 ≤ (1173383726480 * x ^ 2 + 2 * (-986761126464) * x * y + 958489932240 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1173383726480 958489932240 (-986761126464)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc32 (x y : ℝ) : 0 ≤ (472784120640 * x ^ 2 + 2 * (-408725519232) * x * y + 423899289920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 472784120640 423899289920 (-408725519232)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc33 (x y : ℝ) : 0 ≤ (75537958720 * x ^ 2 + 2 * (-66864259008) * x * y + 75298628160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 75537958720 75298628160 (-66864259008)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc34 (x y : ℝ) : 0 ≤ (79451682980 * x ^ 2 + 2 * (-63339743556) * x * y + 56332131420 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 79451682980 56332131420 (-63339743556)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc35 (x y : ℝ) : 0 ≤ (451880195880 * x ^ 2 + 2 * (-371289053736) * x * y + 333163531520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 451880195880 333163531520 (-371289053736)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc36 (x y : ℝ) : 0 ≤ (1002011957360 * x ^ 2 + 2 * (-845391756012) * x * y + 779672365120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1002011957360 779672365120 (-845391756012)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc37 (x y : ℝ) : 0 ≤ (1081077082560 * x ^ 2 + 2 * (-932931661272) * x * y + 896060984800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1081077082560 896060984800 (-932931661272)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc38 (x y : ℝ) : 0 ≤ (565844359040 * x ^ 2 + 2 * (-497405434032) * x * y + 503138530240 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 565844359040 503138530240 (-497405434032)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc39 (x y : ℝ) : 0 ≤ (114337192320 * x ^ 2 + 2 * (-101908790112) * x * y + 109914167680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 114337192320 109914167680 (-101908790112)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc40 (x y : ℝ) : 0 ≤ (79529686180 * x ^ 2 + 2 * (-69363073866) * x * y + 64738861720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 79529686180 64738861720 (-69363073866)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc41 (x y : ℝ) : 0 ≤ (358965127920 * x ^ 2 + 2 * (-317049593826) * x * y + 297050642880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 358965127920 297050642880 (-317049593826)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc42 (x y : ℝ) : 0 ≤ (593165310800 * x ^ 2 + 2 * (-530059262892) * x * y + 508283378000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 593165310800 508283378000 (-530059262892)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc43 (x y : ℝ) : 0 ≤ (424718441600 * x ^ 2 + 2 * (-383184135048) * x * y + 381534474560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 424718441600 381534474560 (-383184135048)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc44 (x y : ℝ) : 0 ≤ (110901781760 * x ^ 2 + 2 * (-100688609424) * x * y + 105398889920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 110901781760 105398889920 (-100688609424)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc45 (x y : ℝ) : 0 ≤ (54593850440 * x ^ 2 + 2 * (-50805842730) * x * y + 49084262220 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 54593850440 49084262220 (-50805842730)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc46 (x y : ℝ) : 0 ≤ (182522999000 * x ^ 2 + 2 * (-169736385612) * x * y + 164381042160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 182522999000 164381042160 (-169736385612)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc47 (x y : ℝ) : 0 ≤ (199079036160 * x ^ 2 + 2 * (-185153217840) * x * y + 183172827440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 199079036160 183172827440 (-185153217840)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc48 (x y : ℝ) : 0 ≤ (70745924320 * x ^ 2 + 2 * (-65739496224) * x * y + 67424628480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 70745924320 67424628480 (-65739496224)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc49 (x y : ℝ) : 0 ≤ (24623273060 * x ^ 2 + 2 * (-23835810708) * x * y + 23585381220 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 24623273060 23585381220 (-23835810708)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc50 (x y : ℝ) : 0 ≤ (54049738640 * x ^ 2 + 2 * (-51818589756) * x * y + 51458780560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 54049738640 51458780560 (-51818589756)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc51 (x y : ℝ) : 0 ≤ (29114982800 * x ^ 2 + 2 * (-27688385784) * x * y + 28084634000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 29114982800 28084634000 (-27688385784)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc52 (x y : ℝ) : 0 ≤ (6563470400 * x ^ 2 + 2 * (-6461362596) * x * y + 6499073600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6563470400 6499073600 (-6461362596)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc53 (x y : ℝ) : 0 ≤ (7088328000 * x ^ 2 + 2 * (-6873847920) * x * y + 6959534400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7088328000 6959534400 (-6873847920)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc54 (x y : ℝ) : 0 ≤ (780436800 * x ^ 2 + 2 * (-767062440) * x * y + 780436800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 780436800 780436800 (-767062440)
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem B_ASE_entry11 (z w : ℝ) : 4423680 * Hdiag (1 - z / 2) ((1 - w) / 2) =
      801184320 * ((1 - z - w) ^ 9) +
      8214628800 * (w * (1 - z - w) ^ 8) +
      36441336000 * (w ^ 2 * (1 - z - w) ^ 7) +
      91489281600 * (w ^ 3 * (1 - z - w) ^ 6) +
      142481379840 * (w ^ 4 * (1 - z - w) ^ 5) +
      141421989120 * (w ^ 5 * (1 - z - w) ^ 4) +
      87917245440 * (w ^ 6 * (1 - z - w) ^ 3) +
      31795461120 * (w ^ 7 * (1 - z - w) ^ 2) +
      5472952320 * (w ^ 8 * (1 - z - w)) +
      192737280 * (w ^ 9) +
      6659768160 * (z * (1 - z - w) ^ 8) +
      60646594240 * (z * w * (1 - z - w) ^ 7) +
      235423411680 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      507118147840 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      659659999360 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      526172846080 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      247457405440 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      60737986560 * (z * w ^ 7 * (1 - z - w)) +
      5474990080 * (z * w ^ 8) +
      24731126870 * (z ^ 2 * (1 - z - w) ^ 7) +
      197409465390 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      657946610000 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      1183535463800 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      1235628716960 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      743250805280 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      235335540480 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      29446259840 * (z ^ 2 * w ^ 7) +
      54548120435 * (z ^ 3 * (1 - z - w) ^ 6) +
      373454270660 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      1037775174300 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      1495013327520 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      1173383726480 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      472784120640 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      75537958720 * (z ^ 3 * w ^ 6) +
      79451682980 * (z ^ 4 * (1 - z - w) ^ 5) +
      451880195880 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      1002011957360 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      1081077082560 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      565844359040 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      114337192320 * (z ^ 4 * w ^ 5) +
      79529686180 * (z ^ 5 * (1 - z - w) ^ 4) +
      358965127920 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      593165310800 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      424718441600 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      110901781760 * (z ^ 5 * w ^ 4) +
      54593850440 * (z ^ 6 * (1 - z - w) ^ 3) +
      182522999000 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      199079036160 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      70745924320 * (z ^ 6 * w ^ 3) +
      24623273060 * (z ^ 7 * (1 - z - w) ^ 2) +
      54049738640 * (z ^ 7 * w * (1 - z - w)) +
      29114982800 * (z ^ 7 * w ^ 2) +
      6563470400 * (z ^ 8 * (1 - z - w)) +
      7088328000 * (z ^ 8 * w) +
      780436800 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_ASE_entry22 (z w : ℝ) : 4423680 * Hdiag ((1 - w) / 2) (1 - z / 2) =
      268058655 * ((1 - z - w) ^ 9) +
      3173049120 * (w * (1 - z - w) ^ 8) +
      16173052200 * (w ^ 2 * (1 - z - w) ^ 7) +
      46429159680 * (w ^ 3 * (1 - z - w) ^ 6) +
      82527394560 * (w ^ 4 * (1 - z - w) ^ 5) +
      93954693120 * (w ^ 5 * (1 - z - w) ^ 4) +
      68211588480 * (w ^ 6 * (1 - z - w) ^ 3) +
      30182983680 * (w ^ 7 * (1 - z - w) ^ 2) +
      7247950080 * (w ^ 8 * (1 - z - w)) +
      688128000 * (w ^ 9) +
      2668414545 * (z * (1 - z - w) ^ 8) +
      27635018260 * (z * w * (1 - z - w) ^ 7) +
      121565829680 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      295612856080 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      433564336480 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      391746174400 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      212023863040 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      62300025600 * (z * w ^ 7 * (1 - z - w)) +
      7471182080 * (z * w ^ 8) +
      12111070085 * (z ^ 2 * (1 - z - w) ^ 7) +
      106918811160 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      394891295780 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      787188651920 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      911786934320 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      611770981760 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      219136635840 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      32047020800 * (z ^ 2 * w ^ 7) +
      32521501695 * (z ^ 3 * (1 - z - w) ^ 6) +
      238451526660 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      715975698860 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      1119956796960 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      958489932240 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      423899289920 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      75298628160 * (z ^ 3 * w ^ 6) +
      56332131420 * (z ^ 4 * (1 - z - w) ^ 5) +
      333163531520 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      779672365120 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      896060984800 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      503138530240 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      109914167680 * (z ^ 4 * w ^ 5) +
      64738861720 * (z ^ 5 * (1 - z - w) ^ 4) +
      297050642880 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      508283378000 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      381534474560 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      105398889920 * (z ^ 5 * w ^ 4) +
      49084262220 * (z ^ 6 * (1 - z - w) ^ 3) +
      164381042160 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      183172827440 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      67424628480 * (z ^ 6 * w ^ 3) +
      23585381220 * (z ^ 7 * (1 - z - w) ^ 2) +
      51458780560 * (z ^ 7 * w * (1 - z - w)) +
      28084634000 * (z ^ 7 * w ^ 2) +
      6499073600 * (z ^ 8 * (1 - z - w)) +
      6959534400 * (z ^ 8 * w) +
      780436800 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_ASE_entry12 (z w : ℝ) : 4423680 * Hmixed (1 - z / 2) ((1 - w) / 2) =
      (-411481728) * ((1 - z - w) ^ 9) +
      (-4609025856) * (w * (1 - z - w) ^ 8) +
      (-22148058240) * (w ^ 2 * (1 - z - w) ^ 7) +
      (-59794467648) * (w ^ 3 * (1 - z - w) ^ 6) +
      (-99599797632) * (w ^ 4 * (1 - z - w) ^ 5) +
      (-105489283584) * (w ^ 5 * (1 - z - w) ^ 4) +
      (-70186266624) * (w ^ 6 * (1 - z - w) ^ 3) +
      (-27574459392) * (w ^ 7 * (1 - z - w) ^ 2) +
      (-5447534592) * (w ^ 8 * (1 - z - w)) +
      (-325902336) * (w ^ 9) +
      (-3774480192) * (z * (1 - z - w) ^ 8) +
      (-37331662752) * (z * w * (1 - z - w) ^ 7) +
      (-155814545568) * (z * w ^ 2 * (1 - z - w) ^ 6) +
      (-357917622720) * (z * w ^ 3 * (1 - z - w) ^ 5) +
      (-493466728320) * (z * w ^ 4 * (1 - z - w) ^ 4) +
      (-415755199488) * (z * w ^ 5 * (1 - z - w) ^ 3) +
      (-206650360320) * (z * w ^ 6 * (1 - z - w) ^ 2) +
      (-54076234752) * (z * w ^ 7 * (1 - z - w)) +
      (-5374605312) * (z * w ^ 8) +
      (-15706834722) * (z ^ 2 * (1 - z - w) ^ 7) +
      (-134329715382) * (z ^ 2 * w * (1 - z - w) ^ 6) +
      (-475149772500) * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      (-900172885536) * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      (-983906926368) * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      (-617063256096) * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      (-203336929728) * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      (-26534885376) * (z ^ 2 * w ^ 7) +
      (-38984838126) * (z ^ 3 * (1 - z - w) ^ 6) +
      (-280638182172) * (z ^ 3 * w * (1 - z - w) ^ 5) +
      (-814280610348) * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      (-1217537869200) * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      (-986761126464) * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      (-408725519232) * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      (-66864259008) * (z ^ 3 * w ^ 6) +
      (-63339743556) * (z ^ 4 * (1 - z - w) ^ 5) +
      (-371289053736) * (z ^ 4 * w * (1 - z - w) ^ 4) +
      (-845391756012) * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      (-932931661272) * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      (-497405434032) * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      (-101908790112) * (z ^ 4 * w ^ 5) +
      (-69363073866) * (z ^ 5 * (1 - z - w) ^ 4) +
      (-317049593826) * (z ^ 5 * w * (1 - z - w) ^ 3) +
      (-530059262892) * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      (-383184135048) * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      (-100688609424) * (z ^ 5 * w ^ 4) +
      (-50805842730) * (z ^ 6 * (1 - z - w) ^ 3) +
      (-169736385612) * (z ^ 6 * w * (1 - z - w) ^ 2) +
      (-185153217840) * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      (-65739496224) * (z ^ 6 * w ^ 3) +
      (-23835810708) * (z ^ 7 * (1 - z - w) ^ 2) +
      (-51818589756) * (z ^ 7 * w * (1 - z - w)) +
      (-27688385784) * (z ^ 7 * w ^ 2) +
      (-6461362596) * (z ^ 8 * (1 - z - w)) +
      (-6873847920) * (z ^ 8 * w) +
      (-767062440) * (z ^ 9) := by
  simp only [Hmixed, mixedNumerator, Sbound, denominator, kappaB]
  ring

private theorem B_ASE_entry11_list (z w : ℝ) :
    4423680 * Hdiag (1 - z / 2) ((1 - w) / 2) = ((B_ASE_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [B_ASE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_ASE_entry11 z w

private theorem B_ASE_entry22_list (z w : ℝ) :
    4423680 * Hdiag ((1 - w) / 2) (1 - z / 2) = ((B_ASE_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [B_ASE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_ASE_entry22 z w

private theorem B_ASE_entry12_list (z w : ℝ) :
    4423680 * Hmixed (1 - z / 2) ((1 - w) / 2) = ((B_ASE_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [B_ASE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_ASE_entry12 z w

private theorem B_ASE_oai {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag (1 - z / 2) ((1 - w) / 2) * x ^ 2 + 2 * Hmixed (1 - z / 2) ((1 - w) / 2) * x * y + Hdiag ((1 - w) / 2) (1 - z / 2) * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (B_ASE_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (B_ASE_hc0 x y) (by positivity),
      mul_nonneg (B_ASE_hc1 x y) (by positivity),
      mul_nonneg (B_ASE_hc2 x y) (by positivity),
      mul_nonneg (B_ASE_hc3 x y) (by positivity),
      mul_nonneg (B_ASE_hc4 x y) (by positivity),
      mul_nonneg (B_ASE_hc5 x y) (by positivity),
      mul_nonneg (B_ASE_hc6 x y) (by positivity),
      mul_nonneg (B_ASE_hc7 x y) (by positivity),
      mul_nonneg (B_ASE_hc8 x y) (by positivity),
      mul_nonneg (B_ASE_hc9 x y) (by positivity),
      mul_nonneg (B_ASE_hc10 x y) (by positivity),
      mul_nonneg (B_ASE_hc11 x y) (by positivity),
      mul_nonneg (B_ASE_hc12 x y) (by positivity),
      mul_nonneg (B_ASE_hc13 x y) (by positivity),
      mul_nonneg (B_ASE_hc14 x y) (by positivity),
      mul_nonneg (B_ASE_hc15 x y) (by positivity),
      mul_nonneg (B_ASE_hc16 x y) (by positivity),
      mul_nonneg (B_ASE_hc17 x y) (by positivity),
      mul_nonneg (B_ASE_hc18 x y) (by positivity),
      mul_nonneg (B_ASE_hc19 x y) (by positivity),
      mul_nonneg (B_ASE_hc20 x y) (by positivity),
      mul_nonneg (B_ASE_hc21 x y) (by positivity),
      mul_nonneg (B_ASE_hc22 x y) (by positivity),
      mul_nonneg (B_ASE_hc23 x y) (by positivity),
      mul_nonneg (B_ASE_hc24 x y) (by positivity),
      mul_nonneg (B_ASE_hc25 x y) (by positivity),
      mul_nonneg (B_ASE_hc26 x y) (by positivity),
      mul_nonneg (B_ASE_hc27 x y) (by positivity),
      mul_nonneg (B_ASE_hc28 x y) (by positivity),
      mul_nonneg (B_ASE_hc29 x y) (by positivity),
      mul_nonneg (B_ASE_hc30 x y) (by positivity),
      mul_nonneg (B_ASE_hc31 x y) (by positivity),
      mul_nonneg (B_ASE_hc32 x y) (by positivity),
      mul_nonneg (B_ASE_hc33 x y) (by positivity),
      mul_nonneg (B_ASE_hc34 x y) (by positivity),
      mul_nonneg (B_ASE_hc35 x y) (by positivity),
      mul_nonneg (B_ASE_hc36 x y) (by positivity),
      mul_nonneg (B_ASE_hc37 x y) (by positivity),
      mul_nonneg (B_ASE_hc38 x y) (by positivity),
      mul_nonneg (B_ASE_hc39 x y) (by positivity),
      mul_nonneg (B_ASE_hc40 x y) (by positivity),
      mul_nonneg (B_ASE_hc41 x y) (by positivity),
      mul_nonneg (B_ASE_hc42 x y) (by positivity),
      mul_nonneg (B_ASE_hc43 x y) (by positivity),
      mul_nonneg (B_ASE_hc44 x y) (by positivity),
      mul_nonneg (B_ASE_hc45 x y) (by positivity),
      mul_nonneg (B_ASE_hc46 x y) (by positivity),
      mul_nonneg (B_ASE_hc47 x y) (by positivity),
      mul_nonneg (B_ASE_hc48 x y) (by positivity),
      mul_nonneg (B_ASE_hc49 x y) (by positivity),
      mul_nonneg (B_ASE_hc50 x y) (by positivity),
      mul_nonneg (B_ASE_hc51 x y) (by positivity),
      mul_nonneg (B_ASE_hc52 x y) (by positivity),
      mul_nonneg (B_ASE_hc53 x y) (by positivity),
      mul_nonneg (B_ASE_hc54 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (B_ASE_data z w) x y hcoeff
  rw [← B_ASE_entry11_list, ← B_ASE_entry12_list, ← B_ASE_entry22_list] at hpos
  nlinarith only [hpos]

end

end PositiveEinsteinFour.Quadratic
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Quadratic.B_ASE_oai := @OAI.PositiveEinsteinFour.Quadratic.B_ASE_oai
