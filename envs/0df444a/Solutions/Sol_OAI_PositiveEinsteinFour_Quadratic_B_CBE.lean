-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Quadratic.B_CBE
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:22:29.444625+00:00
-- url     : https://prove2.me/submissions/ddd0a348-80bc-4013-a3b7-5e080e43d531

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

private theorem B_CBE_hc0 (x y : ℝ) : 0 ≤ (801184320 * x ^ 2 + 2 * (-411481728) * x * y + 268058655 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 801184320 268058655 (-411481728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc1 (x y : ℝ) : 0 ≤ (8562733920 * x ^ 2 + 2 * (-4043672640) * x * y + 2424699900 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 8562733920 2424699900 (-4043672640)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc2 (x y : ℝ) : 0 ≤ (41306927990 * x ^ 2 + 2 * (-18200711394) * x * y + 10173524930 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 41306927990 10173524930 (-18200711394)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc3 (x y : ℝ) : 0 ≤ (117734863255 * x ^ 2 + 2 * (-49253308176) * x * y + 26323350300 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 117734863255 26323350300 (-49253308176)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc4 (x y : ℝ) : 0 ≤ (218089833145 * x ^ 2 + 2 * (-88160628018) * x * y + 46666997155 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 218089833145 46666997155 (-88160628018)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc5 (x y : ℝ) : 0 ≤ (272150628440 * x ^ 2 + 2 * (-108010148874) * x * y + 58940711680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 272150628440 58940711680 (-108010148874)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc6 (x y : ℝ) : 0 ≤ (229268099560 * x ^ 2 + 2 * (-90535912416) * x * y + 53082247440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 229268099560 53082247440 (-90535912416)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc7 (x y : ℝ) : 0 ≤ (126700975140 * x ^ 2 + 2 * (-50337642738) * x * y + 33154198640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 126700975140 33154198640 (-50337642738)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc8 (x y : ℝ) : 0 ≤ (42696211500 * x ^ 2 + 2 * (-17244612132) * x * y + 13529485940 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 42696211500 13529485940 (-17244612132)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc9 (x y : ℝ) : 0 ≤ (7406401920 * x ^ 2 + 2 * (-3087266892) * x * y + 3206825040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7406401920 3206825040 (-3087266892)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc10 (x y : ℝ) : 0 ≤ (393346160 * x ^ 2 + 2 * (-178693632) * x * y + 329471440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 393346160 329471440 (-178693632)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc11 (x y : ℝ) : 0 ≤ (7007873280 * x ^ 2 + 2 * (-3209126976) * x * y + 1920065325 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7007873280 1920065325 (-3209126976)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc12 (x y : ℝ) : 0 ≤ (67365565600 * x ^ 2 + 2 * (-28132139808) * x * y + 15181140175 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 67365565600 15181140175 (-28132139808)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc13 (x y : ℝ) : 0 ≤ (288182431260 * x ^ 2 + 2 * (-112332778152) * x * y + 56215690575 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 288182431260 56215690575 (-112332778152)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc14 (x y : ℝ) : 0 ≤ (714403928815 * x ^ 2 + 2 * (-266661879312) * x * y + 130051701445 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 714403928815 130051701445 (-266661879312)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc15 (x y : ℝ) : 0 ≤ (1120635267720 * x ^ 2 + 2 * (-410215838064) * x * y + 207097920020 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1120635267720 207097920020 (-410215838064)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc16 (x y : ℝ) : 0 ≤ (1140070612440 * x ^ 2 + 2 * (-417500433960) * x * y + 231339973620 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1140070612440 231339973620 (-417500433960)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc17 (x y : ℝ) : 0 ≤ (739294413040 * x ^ 2 + 2 * (-275202297480) * x * y + 176689548020 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 739294413040 176689548020 (-275202297480)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc18 (x y : ℝ) : 0 ≤ (285623877140 * x ^ 2 + 2 * (-109649733144) * x * y + 86812409740 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 285623877140 86812409740 (-109649733144)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc19 (x y : ℝ) : 0 ≤ (55470434640 * x ^ 2 + 2 * (-22431923856) * x * y + 24395377920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 55470434640 24395377920 (-22431923856)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc20 (x y : ℝ) : 0 ≤ (3126466320 * x ^ 2 + 2 * (-1447778304) * x * y + 2933376880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3126466320 2933376880 (-1447778304)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc21 (x y : ℝ) : 0 ≤ (26584506240 * x ^ 2 + 2 * (-10454658624) * x * y + 5656719270 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 26584506240 5656719270 (-10454658624)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc22 (x y : ℝ) : 0 ≤ (226799460000 * x ^ 2 + 2 * (-80644455744) * x * y + 37905178180 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 226799460000 37905178180 (-80644455744)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc23 (x y : ℝ) : 0 ≤ (845266860550 * x ^ 2 + 2 * (-282146938362) * x * y + 122489558390 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 845266860550 122489558390 (-282146938362)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc24 (x y : ℝ) : 0 ≤ (1778215931360 * x ^ 2 + 2 * (-578579785308) * x * y + 256297489880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1778215931360 256297489880 (-578579785308)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc25 (x y : ℝ) : 0 ≤ (2279143529040 * x ^ 2 + 2 * (-745978027176) * x * y + 372083389800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2279143529040 372083389800 (-745978027176)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc26 (x y : ℝ) : 0 ≤ (1788549165360 * x ^ 2 + 2 * (-602996442390) * x * y + 364816194000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1788549165360 364816194000 (-602996442390)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc27 (x y : ℝ) : 0 ≤ (812120570600 * x ^ 2 + 2 * (-287401557276) * x * y + 225136329320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 812120570600 225136329320 (-287401557276)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc28 (x y : ℝ) : 0 ≤ (180759057120 * x ^ 2 + 2 * (-68832498252) * x * y + 77525043680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 180759057120 77525043680 (-68832498252)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc29 (x y : ℝ) : 0 ≤ (11207911520 * x ^ 2 + 2 * (-5072000256) * x * y + 11177908960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 11207911520 11177908960 (-5072000256)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc30 (x y : ℝ) : 0 ≤ (57424677120 * x ^ 2 + 2 * (-18240186432) * x * y + 8752198440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 57424677120 8752198440 (-18240186432)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc31 (x y : ℝ) : 0 ≤ (427408481760 * x ^ 2 + 2 * (-121902009504) * x * y + 46960006840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 427408481760 46960006840 (-121902009504)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc32 (x y : ℝ) : 0 ≤ (1354979833680 * x ^ 2 + 2 * (-369635775972) * x * y + 132511404600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1354979833680 132511404600 (-369635775972)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc33 (x y : ℝ) : 0 ≤ (2335284584520 * x ^ 2 + 2 * (-644290848684) * x * y + 264455406040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2335284584520 264455406040 (-644290848684)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc34 (x y : ℝ) : 0 ≤ (2314380041840 * x ^ 2 + 2 * (-671796834156) * x * y + 361053363840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2314380041840 361053363840 (-671796834156)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc35 (x y : ℝ) : 0 ≤ (1273781484400 * x ^ 2 + 2 * (-399373018968) * x * y + 300412453200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1273781484400 300412453200 (-399373018968)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc36 (x y : ℝ) : 0 ≤ (332954019200 * x ^ 2 + 2 * (-115979530680) * x * y + 133372143040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 332954019200 133372143040 (-115979530680)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc37 (x y : ℝ) : 0 ≤ (23260046400 * x ^ 2 + 2 * (-10085577984) * x * y + 23861243840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 23260046400 23861243840 (-10085577984)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc38 (x y : ℝ) : 0 ≤ (77762971200 * x ^ 2 + 2 * (-17789831232) * x * y + 7541591760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 77762971200 7541591760 (-17789831232)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc39 (x y : ℝ) : 0 ≤ (493437357440 * x ^ 2 + 2 * (-101591457984) * x * y + 28214978720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 493437357440 28214978720 (-101591457984)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc40 (x y : ℝ) : 0 ≤ (1285576703920 * x ^ 2 + 2 * (-267283549584) * x * y + 74673287920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1285576703920 74673287920 (-267283549584)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc41 (x y : ℝ) : 0 ≤ (1718237028160 * x ^ 2 + 2 * (-391066386192) * x * y + 165890628160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1718237028160 165890628160 (-391066386192)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc42 (x y : ℝ) : 0 ≤ (1196224464480 * x ^ 2 + 2 * (-310896101904) * x * y + 214524771680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1196224464480 214524771680 (-310896101904)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc43 (x y : ℝ) : 0 ≤ (378170711680 * x ^ 2 + 2 * (-115836715344) * x * y + 133928609920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 378170711680 133928609920 (-115836715344)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc44 (x y : ℝ) : 0 ≤ (30228862080 * x ^ 2 + 2 * (-12498736896) * x * y + 31279050880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 30228862080 31279050880 (-12498736896)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc45 (x y : ℝ) : 0 ≤ (68316026880 * x ^ 2 + 2 * (-8488967808) * x * y + 3815876160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 68316026880 3815876160 (-8488967808)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc46 (x y : ℝ) : 0 ≤ (357444307200 * x ^ 2 + 2 * (-42153516672) * x * y + 5956595200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 357444307200 5956595200 (-42153516672)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc47 (x y : ℝ) : 0 ≤ (724822974400 * x ^ 2 + 2 * (-103067609184) * x * y + 24963448640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 724822974400 24963448640 (-103067609184)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc48 (x y : ℝ) : 0 ≤ (681702796160 * x ^ 2 + 2 * (-127313018976) * x * y + 75229811840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 681702796160 75229811840 (-127313018976)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc49 (x y : ℝ) : 0 ≤ (271322538240 * x ^ 2 + 2 * (-67980349344) * x * y + 78316302080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 271322538240 78316302080 (-67980349344)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc50 (x y : ℝ) : 0 ≤ (25031959040 * x ^ 2 + 2 * (-9913962240) * x * y + 25833786880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 25031959040 25833786880 (-9913962240)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc51 (x y : ℝ) : 0 ≤ (38811640320 * x ^ 2 + 2 * (-95439360) * x * y + 1914585600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 38811640320 1914585600 (-95439360)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc52 (x y : ℝ) : 0 ≤ (158722022400 * x ^ 2 + 2 * (-3819116544) * x * y + 520084480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 158722022400 520084480 (-3819116544)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc53 (x y : ℝ) : 0 ≤ (226916362240 * x ^ 2 + 2 * (-18862228608) * x * y + 10060011520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 226916362240 10060011520 (-18862228608)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc54 (x y : ℝ) : 0 ≤ (120937564160 * x ^ 2 + 2 * (-20769705984) * x * y + 25004124160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 120937564160 25004124160 (-20769705984)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc55 (x y : ℝ) : 0 ≤ (12853027840 * x ^ 2 + 2 * (-4925164032) * x * y + 13148922880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 12853027840 13148922880 (-4925164032)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc56 (x y : ℝ) : 0 ≤ (13695129600 * x ^ 2 + 2 * 1846354944 * x * y + 1661306880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 13695129600 1661306880 1846354944
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc57 (x y : ℝ) : 0 ≤ (39557816320 * x ^ 2 + 2 * 2675395584 * x * y + 1792000000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 39557816320 1792000000 2675395584
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc58 (x y : ℝ) : 0 ≤ (31551016960 * x ^ 2 + 2 * (-1632589824) * x * y + 4175810560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 31551016960 4175810560 (-1632589824)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc59 (x y : ℝ) : 0 ≤ (3734077440 * x ^ 2 + 2 * (-1402601472) * x * y + 3776348160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3734077440 3776348160 (-1402601472)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc60 (x y : ℝ) : 0 ≤ (2713436160 * x ^ 2 + 2 * 744124416 * x * y + 998522880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2713436160 998522880 744124416
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc61 (x y : ℝ) : 0 ≤ (4254597120 * x ^ 2 + 2 * 586432512 * x * y + 824770560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4254597120 824770560 586432512
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc62 (x y : ℝ) : 0 ≤ (469401600 * x ^ 2 + 2 * (-175325184) * x * y + 469401600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 469401600 469401600 (-175325184)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc63 (x y : ℝ) : 0 ≤ (230031360 * x ^ 2 + 2 * 84639744 * x * y + 230031360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 230031360 230031360 84639744
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem B_CBE_entry11 (z w : ℝ) : 4423680 * Hdiag (1 + w / 2) ((1 + z) / 2) =
      801184320 * ((1 - z - w) ^ 10) +
      8562733920 * (w * (1 - z - w) ^ 9) +
      41306927990 * (w ^ 2 * (1 - z - w) ^ 8) +
      117734863255 * (w ^ 3 * (1 - z - w) ^ 7) +
      218089833145 * (w ^ 4 * (1 - z - w) ^ 6) +
      272150628440 * (w ^ 5 * (1 - z - w) ^ 5) +
      229268099560 * (w ^ 6 * (1 - z - w) ^ 4) +
      126700975140 * (w ^ 7 * (1 - z - w) ^ 3) +
      42696211500 * (w ^ 8 * (1 - z - w) ^ 2) +
      7406401920 * (w ^ 9 * (1 - z - w)) +
      393346160 * (w ^ 10) +
      7007873280 * (z * (1 - z - w) ^ 9) +
      67365565600 * (z * w * (1 - z - w) ^ 8) +
      288182431260 * (z * w ^ 2 * (1 - z - w) ^ 7) +
      714403928815 * (z * w ^ 3 * (1 - z - w) ^ 6) +
      1120635267720 * (z * w ^ 4 * (1 - z - w) ^ 5) +
      1140070612440 * (z * w ^ 5 * (1 - z - w) ^ 4) +
      739294413040 * (z * w ^ 6 * (1 - z - w) ^ 3) +
      285623877140 * (z * w ^ 7 * (1 - z - w) ^ 2) +
      55470434640 * (z * w ^ 8 * (1 - z - w)) +
      3126466320 * (z * w ^ 9) +
      26584506240 * (z ^ 2 * (1 - z - w) ^ 8) +
      226799460000 * (z ^ 2 * w * (1 - z - w) ^ 7) +
      845266860550 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 6) +
      1778215931360 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 5) +
      2279143529040 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 4) +
      1788549165360 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 3) +
      812120570600 * (z ^ 2 * w ^ 6 * (1 - z - w) ^ 2) +
      180759057120 * (z ^ 2 * w ^ 7 * (1 - z - w)) +
      11207911520 * (z ^ 2 * w ^ 8) +
      57424677120 * (z ^ 3 * (1 - z - w) ^ 7) +
      427408481760 * (z ^ 3 * w * (1 - z - w) ^ 6) +
      1354979833680 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 5) +
      2335284584520 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 4) +
      2314380041840 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 3) +
      1273781484400 * (z ^ 3 * w ^ 5 * (1 - z - w) ^ 2) +
      332954019200 * (z ^ 3 * w ^ 6 * (1 - z - w)) +
      23260046400 * (z ^ 3 * w ^ 7) +
      77762971200 * (z ^ 4 * (1 - z - w) ^ 6) +
      493437357440 * (z ^ 4 * w * (1 - z - w) ^ 5) +
      1285576703920 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 4) +
      1718237028160 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 3) +
      1196224464480 * (z ^ 4 * w ^ 4 * (1 - z - w) ^ 2) +
      378170711680 * (z ^ 4 * w ^ 5 * (1 - z - w)) +
      30228862080 * (z ^ 4 * w ^ 6) +
      68316026880 * (z ^ 5 * (1 - z - w) ^ 5) +
      357444307200 * (z ^ 5 * w * (1 - z - w) ^ 4) +
      724822974400 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 3) +
      681702796160 * (z ^ 5 * w ^ 3 * (1 - z - w) ^ 2) +
      271322538240 * (z ^ 5 * w ^ 4 * (1 - z - w)) +
      25031959040 * (z ^ 5 * w ^ 5) +
      38811640320 * (z ^ 6 * (1 - z - w) ^ 4) +
      158722022400 * (z ^ 6 * w * (1 - z - w) ^ 3) +
      226916362240 * (z ^ 6 * w ^ 2 * (1 - z - w) ^ 2) +
      120937564160 * (z ^ 6 * w ^ 3 * (1 - z - w)) +
      12853027840 * (z ^ 6 * w ^ 4) +
      13695129600 * (z ^ 7 * (1 - z - w) ^ 3) +
      39557816320 * (z ^ 7 * w * (1 - z - w) ^ 2) +
      31551016960 * (z ^ 7 * w ^ 2 * (1 - z - w)) +
      3734077440 * (z ^ 7 * w ^ 3) +
      2713436160 * (z ^ 8 * (1 - z - w) ^ 2) +
      4254597120 * (z ^ 8 * w * (1 - z - w)) +
      469401600 * (z ^ 8 * w ^ 2) +
      230031360 * (z ^ 9 * (1 - z - w)) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_CBE_entry22 (z w : ℝ) : 4423680 * Hdiag ((1 + z) / 2) (1 + w / 2) =
      268058655 * ((1 - z - w) ^ 10) +
      2424699900 * (w * (1 - z - w) ^ 9) +
      10173524930 * (w ^ 2 * (1 - z - w) ^ 8) +
      26323350300 * (w ^ 3 * (1 - z - w) ^ 7) +
      46666997155 * (w ^ 4 * (1 - z - w) ^ 6) +
      58940711680 * (w ^ 5 * (1 - z - w) ^ 5) +
      53082247440 * (w ^ 6 * (1 - z - w) ^ 4) +
      33154198640 * (w ^ 7 * (1 - z - w) ^ 3) +
      13529485940 * (w ^ 8 * (1 - z - w) ^ 2) +
      3206825040 * (w ^ 9 * (1 - z - w)) +
      329471440 * (w ^ 10) +
      1920065325 * (z * (1 - z - w) ^ 9) +
      15181140175 * (z * w * (1 - z - w) ^ 8) +
      56215690575 * (z * w ^ 2 * (1 - z - w) ^ 7) +
      130051701445 * (z * w ^ 3 * (1 - z - w) ^ 6) +
      207097920020 * (z * w ^ 4 * (1 - z - w) ^ 5) +
      231339973620 * (z * w ^ 5 * (1 - z - w) ^ 4) +
      176689548020 * (z * w ^ 6 * (1 - z - w) ^ 3) +
      86812409740 * (z * w ^ 7 * (1 - z - w) ^ 2) +
      24395377920 * (z * w ^ 8 * (1 - z - w)) +
      2933376880 * (z * w ^ 9) +
      5656719270 * (z ^ 2 * (1 - z - w) ^ 8) +
      37905178180 * (z ^ 2 * w * (1 - z - w) ^ 7) +
      122489558390 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 6) +
      256297489880 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 5) +
      372083389800 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 4) +
      364816194000 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 3) +
      225136329320 * (z ^ 2 * w ^ 6 * (1 - z - w) ^ 2) +
      77525043680 * (z ^ 2 * w ^ 7 * (1 - z - w)) +
      11177908960 * (z ^ 2 * w ^ 8) +
      8752198440 * (z ^ 3 * (1 - z - w) ^ 7) +
      46960006840 * (z ^ 3 * w * (1 - z - w) ^ 6) +
      132511404600 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 5) +
      264455406040 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 4) +
      361053363840 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 3) +
      300412453200 * (z ^ 3 * w ^ 5 * (1 - z - w) ^ 2) +
      133372143040 * (z ^ 3 * w ^ 6 * (1 - z - w)) +
      23861243840 * (z ^ 3 * w ^ 7) +
      7541591760 * (z ^ 4 * (1 - z - w) ^ 6) +
      28214978720 * (z ^ 4 * w * (1 - z - w) ^ 5) +
      74673287920 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 4) +
      165890628160 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 3) +
      214524771680 * (z ^ 4 * w ^ 4 * (1 - z - w) ^ 2) +
      133928609920 * (z ^ 4 * w ^ 5 * (1 - z - w)) +
      31279050880 * (z ^ 4 * w ^ 6) +
      3815876160 * (z ^ 5 * (1 - z - w) ^ 5) +
      5956595200 * (z ^ 5 * w * (1 - z - w) ^ 4) +
      24963448640 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 3) +
      75229811840 * (z ^ 5 * w ^ 3 * (1 - z - w) ^ 2) +
      78316302080 * (z ^ 5 * w ^ 4 * (1 - z - w)) +
      25833786880 * (z ^ 5 * w ^ 5) +
      1914585600 * (z ^ 6 * (1 - z - w) ^ 4) +
      520084480 * (z ^ 6 * w * (1 - z - w) ^ 3) +
      10060011520 * (z ^ 6 * w ^ 2 * (1 - z - w) ^ 2) +
      25004124160 * (z ^ 6 * w ^ 3 * (1 - z - w)) +
      13148922880 * (z ^ 6 * w ^ 4) +
      1661306880 * (z ^ 7 * (1 - z - w) ^ 3) +
      1792000000 * (z ^ 7 * w * (1 - z - w) ^ 2) +
      4175810560 * (z ^ 7 * w ^ 2 * (1 - z - w)) +
      3776348160 * (z ^ 7 * w ^ 3) +
      998522880 * (z ^ 8 * (1 - z - w) ^ 2) +
      824770560 * (z ^ 8 * w * (1 - z - w)) +
      469401600 * (z ^ 8 * w ^ 2) +
      230031360 * (z ^ 9 * (1 - z - w)) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_CBE_entry12 (z w : ℝ) : 4423680 * Hmixed (1 + w / 2) ((1 + z) / 2) =
      (-411481728) * ((1 - z - w) ^ 10) +
      (-4043672640) * (w * (1 - z - w) ^ 9) +
      (-18200711394) * (w ^ 2 * (1 - z - w) ^ 8) +
      (-49253308176) * (w ^ 3 * (1 - z - w) ^ 7) +
      (-88160628018) * (w ^ 4 * (1 - z - w) ^ 6) +
      (-108010148874) * (w ^ 5 * (1 - z - w) ^ 5) +
      (-90535912416) * (w ^ 6 * (1 - z - w) ^ 4) +
      (-50337642738) * (w ^ 7 * (1 - z - w) ^ 3) +
      (-17244612132) * (w ^ 8 * (1 - z - w) ^ 2) +
      (-3087266892) * (w ^ 9 * (1 - z - w)) +
      (-178693632) * (w ^ 10) +
      (-3209126976) * (z * (1 - z - w) ^ 9) +
      (-28132139808) * (z * w * (1 - z - w) ^ 8) +
      (-112332778152) * (z * w ^ 2 * (1 - z - w) ^ 7) +
      (-266661879312) * (z * w ^ 3 * (1 - z - w) ^ 6) +
      (-410215838064) * (z * w ^ 4 * (1 - z - w) ^ 5) +
      (-417500433960) * (z * w ^ 5 * (1 - z - w) ^ 4) +
      (-275202297480) * (z * w ^ 6 * (1 - z - w) ^ 3) +
      (-109649733144) * (z * w ^ 7 * (1 - z - w) ^ 2) +
      (-22431923856) * (z * w ^ 8 * (1 - z - w)) +
      (-1447778304) * (z * w ^ 9) +
      (-10454658624) * (z ^ 2 * (1 - z - w) ^ 8) +
      (-80644455744) * (z ^ 2 * w * (1 - z - w) ^ 7) +
      (-282146938362) * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 6) +
      (-578579785308) * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 5) +
      (-745978027176) * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 4) +
      (-602996442390) * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 3) +
      (-287401557276) * (z ^ 2 * w ^ 6 * (1 - z - w) ^ 2) +
      (-68832498252) * (z ^ 2 * w ^ 7 * (1 - z - w)) +
      (-5072000256) * (z ^ 2 * w ^ 8) +
      (-18240186432) * (z ^ 3 * (1 - z - w) ^ 7) +
      (-121902009504) * (z ^ 3 * w * (1 - z - w) ^ 6) +
      (-369635775972) * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 5) +
      (-644290848684) * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 4) +
      (-671796834156) * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 3) +
      (-399373018968) * (z ^ 3 * w ^ 5 * (1 - z - w) ^ 2) +
      (-115979530680) * (z ^ 3 * w ^ 6 * (1 - z - w)) +
      (-10085577984) * (z ^ 3 * w ^ 7) +
      (-17789831232) * (z ^ 4 * (1 - z - w) ^ 6) +
      (-101591457984) * (z ^ 4 * w * (1 - z - w) ^ 5) +
      (-267283549584) * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 4) +
      (-391066386192) * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 3) +
      (-310896101904) * (z ^ 4 * w ^ 4 * (1 - z - w) ^ 2) +
      (-115836715344) * (z ^ 4 * w ^ 5 * (1 - z - w)) +
      (-12498736896) * (z ^ 4 * w ^ 6) +
      (-8488967808) * (z ^ 5 * (1 - z - w) ^ 5) +
      (-42153516672) * (z ^ 5 * w * (1 - z - w) ^ 4) +
      (-103067609184) * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 3) +
      (-127313018976) * (z ^ 5 * w ^ 3 * (1 - z - w) ^ 2) +
      (-67980349344) * (z ^ 5 * w ^ 4 * (1 - z - w)) +
      (-9913962240) * (z ^ 5 * w ^ 5) +
      (-95439360) * (z ^ 6 * (1 - z - w) ^ 4) +
      (-3819116544) * (z ^ 6 * w * (1 - z - w) ^ 3) +
      (-18862228608) * (z ^ 6 * w ^ 2 * (1 - z - w) ^ 2) +
      (-20769705984) * (z ^ 6 * w ^ 3 * (1 - z - w)) +
      (-4925164032) * (z ^ 6 * w ^ 4) +
      1846354944 * (z ^ 7 * (1 - z - w) ^ 3) +
      2675395584 * (z ^ 7 * w * (1 - z - w) ^ 2) +
      (-1632589824) * (z ^ 7 * w ^ 2 * (1 - z - w)) +
      (-1402601472) * (z ^ 7 * w ^ 3) +
      744124416 * (z ^ 8 * (1 - z - w) ^ 2) +
      586432512 * (z ^ 8 * w * (1 - z - w)) +
      (-175325184) * (z ^ 8 * w ^ 2) +
      84639744 * (z ^ 9 * (1 - z - w)) := by
  simp only [Hmixed, mixedNumerator, Sbound, denominator, kappaB]
  ring

private theorem B_CBE_entry11_list (z w : ℝ) :
    4423680 * Hdiag (1 + w / 2) ((1 + z) / 2) = ((B_CBE_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [B_CBE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_CBE_entry11 z w

private theorem B_CBE_entry22_list (z w : ℝ) :
    4423680 * Hdiag ((1 + z) / 2) (1 + w / 2) = ((B_CBE_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [B_CBE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_CBE_entry22 z w

private theorem B_CBE_entry12_list (z w : ℝ) :
    4423680 * Hmixed (1 + w / 2) ((1 + z) / 2) = ((B_CBE_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [B_CBE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_CBE_entry12 z w

private theorem B_CBE_oai {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag (1 + w / 2) ((1 + z) / 2) * x ^ 2 + 2 * Hmixed (1 + w / 2) ((1 + z) / 2) * x * y + Hdiag ((1 + z) / 2) (1 + w / 2) * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (B_CBE_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (B_CBE_hc0 x y) (by positivity),
      mul_nonneg (B_CBE_hc1 x y) (by positivity),
      mul_nonneg (B_CBE_hc2 x y) (by positivity),
      mul_nonneg (B_CBE_hc3 x y) (by positivity),
      mul_nonneg (B_CBE_hc4 x y) (by positivity),
      mul_nonneg (B_CBE_hc5 x y) (by positivity),
      mul_nonneg (B_CBE_hc6 x y) (by positivity),
      mul_nonneg (B_CBE_hc7 x y) (by positivity),
      mul_nonneg (B_CBE_hc8 x y) (by positivity),
      mul_nonneg (B_CBE_hc9 x y) (by positivity),
      mul_nonneg (B_CBE_hc10 x y) (by positivity),
      mul_nonneg (B_CBE_hc11 x y) (by positivity),
      mul_nonneg (B_CBE_hc12 x y) (by positivity),
      mul_nonneg (B_CBE_hc13 x y) (by positivity),
      mul_nonneg (B_CBE_hc14 x y) (by positivity),
      mul_nonneg (B_CBE_hc15 x y) (by positivity),
      mul_nonneg (B_CBE_hc16 x y) (by positivity),
      mul_nonneg (B_CBE_hc17 x y) (by positivity),
      mul_nonneg (B_CBE_hc18 x y) (by positivity),
      mul_nonneg (B_CBE_hc19 x y) (by positivity),
      mul_nonneg (B_CBE_hc20 x y) (by positivity),
      mul_nonneg (B_CBE_hc21 x y) (by positivity),
      mul_nonneg (B_CBE_hc22 x y) (by positivity),
      mul_nonneg (B_CBE_hc23 x y) (by positivity),
      mul_nonneg (B_CBE_hc24 x y) (by positivity),
      mul_nonneg (B_CBE_hc25 x y) (by positivity),
      mul_nonneg (B_CBE_hc26 x y) (by positivity),
      mul_nonneg (B_CBE_hc27 x y) (by positivity),
      mul_nonneg (B_CBE_hc28 x y) (by positivity),
      mul_nonneg (B_CBE_hc29 x y) (by positivity),
      mul_nonneg (B_CBE_hc30 x y) (by positivity),
      mul_nonneg (B_CBE_hc31 x y) (by positivity),
      mul_nonneg (B_CBE_hc32 x y) (by positivity),
      mul_nonneg (B_CBE_hc33 x y) (by positivity),
      mul_nonneg (B_CBE_hc34 x y) (by positivity),
      mul_nonneg (B_CBE_hc35 x y) (by positivity),
      mul_nonneg (B_CBE_hc36 x y) (by positivity),
      mul_nonneg (B_CBE_hc37 x y) (by positivity),
      mul_nonneg (B_CBE_hc38 x y) (by positivity),
      mul_nonneg (B_CBE_hc39 x y) (by positivity),
      mul_nonneg (B_CBE_hc40 x y) (by positivity),
      mul_nonneg (B_CBE_hc41 x y) (by positivity),
      mul_nonneg (B_CBE_hc42 x y) (by positivity),
      mul_nonneg (B_CBE_hc43 x y) (by positivity),
      mul_nonneg (B_CBE_hc44 x y) (by positivity),
      mul_nonneg (B_CBE_hc45 x y) (by positivity),
      mul_nonneg (B_CBE_hc46 x y) (by positivity),
      mul_nonneg (B_CBE_hc47 x y) (by positivity),
      mul_nonneg (B_CBE_hc48 x y) (by positivity),
      mul_nonneg (B_CBE_hc49 x y) (by positivity),
      mul_nonneg (B_CBE_hc50 x y) (by positivity),
      mul_nonneg (B_CBE_hc51 x y) (by positivity),
      mul_nonneg (B_CBE_hc52 x y) (by positivity),
      mul_nonneg (B_CBE_hc53 x y) (by positivity),
      mul_nonneg (B_CBE_hc54 x y) (by positivity),
      mul_nonneg (B_CBE_hc55 x y) (by positivity),
      mul_nonneg (B_CBE_hc56 x y) (by positivity),
      mul_nonneg (B_CBE_hc57 x y) (by positivity),
      mul_nonneg (B_CBE_hc58 x y) (by positivity),
      mul_nonneg (B_CBE_hc59 x y) (by positivity),
      mul_nonneg (B_CBE_hc60 x y) (by positivity),
      mul_nonneg (B_CBE_hc61 x y) (by positivity),
      mul_nonneg (B_CBE_hc62 x y) (by positivity),
      mul_nonneg (B_CBE_hc63 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (B_CBE_data z w) x y hcoeff
  rw [← B_CBE_entry11_list, ← B_CBE_entry12_list, ← B_CBE_entry22_list] at hpos
  nlinarith only [hpos]

end

end PositiveEinsteinFour.Quadratic
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Quadratic.B_CBE_oai := @OAI.PositiveEinsteinFour.Quadratic.B_CBE_oai
