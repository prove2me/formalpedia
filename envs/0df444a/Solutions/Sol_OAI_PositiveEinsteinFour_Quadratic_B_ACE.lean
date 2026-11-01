-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Quadratic.B_ACE
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:19:51.775291+00:00
-- url     : https://prove2.me/submissions/b73017a7-026e-47c7-8567-25b1595b8115

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

private theorem B_ACE_hc0 (x y : ℝ) : 0 ≤ (801184320 * x ^ 2 + 2 * (-411481728) * x * y + 268058655 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 801184320 268058655 (-411481728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc1 (x y : ℝ) : 0 ≤ (7007873280 * x ^ 2 + 2 * (-3209126976) * x * y + 1920065325 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7007873280 1920065325 (-3209126976)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc2 (x y : ℝ) : 0 ≤ (26584506240 * x ^ 2 + 2 * (-10454658624) * x * y + 5656719270 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 26584506240 5656719270 (-10454658624)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc3 (x y : ℝ) : 0 ≤ (57424677120 * x ^ 2 + 2 * (-18240186432) * x * y + 8752198440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 57424677120 8752198440 (-18240186432)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc4 (x y : ℝ) : 0 ≤ (77762971200 * x ^ 2 + 2 * (-17789831232) * x * y + 7541591760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 77762971200 7541591760 (-17789831232)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc5 (x y : ℝ) : 0 ≤ (68316026880 * x ^ 2 + 2 * (-8488967808) * x * y + 3815876160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 68316026880 3815876160 (-8488967808)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc6 (x y : ℝ) : 0 ≤ (38811640320 * x ^ 2 + 2 * (-95439360) * x * y + 1914585600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 38811640320 1914585600 (-95439360)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc7 (x y : ℝ) : 0 ≤ (13695129600 * x ^ 2 + 2 * 1846354944 * x * y + 1661306880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 13695129600 1661306880 1846354944
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc8 (x y : ℝ) : 0 ≤ (2713436160 * x ^ 2 + 2 * 744124416 * x * y + 998522880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2713436160 998522880 744124416
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc9 (x y : ℝ) : 0 ≤ (230031360 * x ^ 2 + 2 * 84639744 * x * y + 230031360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 230031360 230031360 84639744
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc11 (x y : ℝ) : 0 ≤ (7460952480 * x ^ 2 + 2 * (-4185961920) * x * y + 2936473200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7460952480 2936473200 (-4185961920)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc12 (x y : ℝ) : 0 ≤ (58776153440 * x ^ 2 + 2 * (-29632145760) * x * y + 19380035675 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 58776153440 19380035675 (-29632145760)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc13 (x y : ℝ) : 0 ≤ (198552639840 * x ^ 2 + 2 * (-86630082240) * x * y + 52602330140 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 198552639840 52602330140 (-86630082240)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc14 (x y : ℝ) : 0 ≤ (376536997920 * x ^ 2 + 2 * (-133460600544) * x * y + 75570771320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 376536997920 75570771320 (-133460600544)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc15 (x y : ℝ) : 0 ≤ (439718296960 * x ^ 2 + 2 * (-111886516800) * x * y + 62284122400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 439718296960 62284122400 (-111886516800)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc16 (x y : ℝ) : 0 ≤ (325715961600 * x ^ 2 + 2 * (-42736161408) * x * y + 32202166400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 325715961600 32202166400 (-42736161408)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc17 (x y : ℝ) : 0 ≤ (151771100160 * x ^ 2 + 2 * 3055601664 * x * y + 14796600320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 151771100160 14796600320 3055601664
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc18 (x y : ℝ) : 0 ≤ (42612961280 * x ^ 2 + 2 * 8402734080 * x * y + 8175841280 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 42612961280 8175841280 8402734080
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc19 (x y : ℝ) : 0 ≤ (6599147520 * x ^ 2 + 2 * 2390065152 * x * y + 3169320960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6599147520 3169320960 2390065152
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc20 (x y : ℝ) : 0 ≤ (460062720 * x ^ 2 + 2 * 169279488 * x * y + 460062720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 460062720 460062720 169279488
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc21 (x y : ℝ) : 0 ≤ (31390895030 * x ^ 2 + 2 * (-19481314914) * x * y + 14779484630 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 31390895030 14779484630 (-19481314914)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc22 (x y : ℝ) : 0 ≤ (219467133980 * x ^ 2 + 2 * (-124332825768) * x * y + 89806854575 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 219467133980 89806854575 (-124332825768)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc23 (x y : ℝ) : 0 ≤ (647539119430 * x ^ 2 + 2 * (-324046323834) * x * y + 225369622110 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 647539119430 225369622110 (-324046323834)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc24 (x y : ℝ) : 0 ≤ (1049750930640 * x ^ 2 + 2 * (-438987322212) * x * y + 304175991480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1049750930640 304175991480 (-438987322212)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc25 (x y : ℝ) : 0 ≤ (1016981401520 * x ^ 2 + 2 * (-318758843664) * x * y + 245019006320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1016981401520 245019006320 (-318758843664)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc26 (x y : ℝ) : 0 ≤ (597909592000 * x ^ 2 + 2 * (-105398188128) * x * y + 129945733440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 597909592000 129945733440 (-105398188128)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc27 (x y : ℝ) : 0 ≤ (206063595520 * x ^ 2 + 2 * 1761926016 * x * y + 52889559040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 206063595520 52889559040 1761926016
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc28 (x y : ℝ) : 0 ≤ (37661306880 * x ^ 2 + 2 * 9822087168 * x * y + 16943493120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 37661306880 16943493120 9822087168
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc29 (x y : ℝ) : 0 ≤ (2813952000 * x ^ 2 + 2 * 1628307456 * x * y + 2813952000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2813952000 2813952000 1628307456
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc30 (x y : ℝ) : 0 ≤ (79279247305 * x ^ 2 + 2 * (-54691672848) * x * y + 44632571780 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 79279247305 44632571780 (-54691672848)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc31 (x y : ℝ) : 0 ≤ (484497605785 * x ^ 2 + 2 * (-311730684192) * x * y + 246964165405 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 484497605785 246964165405 (-311730684192)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc32 (x y : ℝ) : 0 ≤ (1223690550760 * x ^ 2 + 2 * (-716736256092) * x * y + 563752476640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1223690550760 563752476640 (-716736256092)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc33 (x y : ℝ) : 0 ≤ (1648914440280 * x ^ 2 + 2 * (-845198541756) * x * y + 693673792760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1648914440280 693673792760 (-845198541756)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc34 (x y : ℝ) : 0 ≤ (1270957697600 * x ^ 2 + 2 * (-529916688240) * x * y + 509551208000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1270957697600 509551208000 (-529916688240)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc35 (x y : ℝ) : 0 ≤ (553853827840 * x ^ 2 + 2 * (-158525660640) * x * y + 236862688000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 553853827840 236862688000 (-158525660640)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc36 (x y : ℝ) : 0 ≤ (124036106240 * x ^ 2 + 2 * (-11903869440) * x * y + 70261647360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 124036106240 70261647360 (-11903869440)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc37 (x y : ℝ) : 0 ≤ (10697728000 * x ^ 2 + 2 * 2206679040 * x * y + 10697728000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 10697728000 10697728000 2206679040
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc38 (x y : ℝ) : 0 ≤ (133999803415 * x ^ 2 + 2 * (-102324581682) * x * y + 88853633115 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 133999803415 88853633115 (-102324581682)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc39 (x y : ℝ) : 0 ≤ (703211491460 * x ^ 2 + 2 * (-512628000720) * x * y + 438296407780 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 703211491460 438296407780 (-512628000720)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc40 (x y : ℝ) : 0 ≤ (1483794037240 * x ^ 2 + 2 * (-1017766526376) * x * y + 880557686400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1483794037240 880557686400 (-1017766526376)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc41 (x y : ℝ) : 0 ≤ (1603758818480 * x ^ 2 + 2 * (-1013083964844) * x * y + 933496331520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1603758818480 933496331520 (-1013083964844)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc42 (x y : ℝ) : 0 ≤ (928767682400 * x ^ 2 + 2 * (-521545831728) * x * y + 564123637600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 928767682400 564123637600 (-521545831728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc43 (x y : ℝ) : 0 ≤ (269451366400 * x ^ 2 + 2 * (-125744474784) * x * y + 191617484800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 269451366400 191617484800 (-125744474784)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc44 (x y : ℝ) : 0 ≤ (29853414400 * x ^ 2 + 2 * (-9808763904) * x * y + 29853414400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 29853414400 29853414400 (-9808763904)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc45 (x y : ℝ) : 0 ≤ (158981369160 * x ^ 2 + 2 * (-132702817422) * x * y + 121070993140 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 158981369160 121070993140 (-132702817422)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc46 (x y : ℝ) : 0 ≤ (699438681620 * x ^ 2 + 2 * (-569326452792) * x * y + 515756895280 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 699438681620 515756895280 (-569326452792)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc47 (x y : ℝ) : 0 ≤ (1190397082640 * x ^ 2 + 2 * (-938999538186) * x * y + 868221822640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1190397082640 868221822640 (-938999538186)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc48 (x y : ℝ) : 0 ≤ (975402834800 * x ^ 2 + 2 * (-740212696656) * x * y + 730966062960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 975402834800 730966062960 (-740212696656)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc49 (x y : ℝ) : 0 ≤ (381839208960 * x ^ 2 + 2 * (-276355602480) * x * y + 313815472640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 381839208960 313815472640 (-276355602480)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc50 (x y : ℝ) : 0 ≤ (56389672960 * x ^ 2 + 2 * (-38526237120) * x * y + 56389672960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 56389672960 56389672960 (-38526237120)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc51 (x y : ℝ) : 0 ≤ (134123536620 * x ^ 2 + 2 * (-120168916596) * x * y + 113823123940 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 134123536620 113823123940 (-120168916596)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc52 (x y : ℝ) : 0 ≤ (476906315600 * x ^ 2 + 2 * (-423759510600) * x * y + 400069044260 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 476906315600 400069044260 (-423759510600)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc53 (x y : ℝ) : 0 ≤ (617240360680 * x ^ 2 + 2 * (-543451931640) * x * y + 524496538600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 617240360680 524496538600 (-543451931640)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc54 (x y : ℝ) : 0 ≤ (343495425280 * x ^ 2 + 2 * (-300022081320) * x * y + 307365658880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 343495425280 307365658880 (-300022081320)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc55 (x y : ℝ) : 0 ≤ (68951052800 * x ^ 2 + 2 * (-60037960992) * x * y + 68951052800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 68951052800 68951052800 (-60037960992)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc56 (x y : ℝ) : 0 ≤ (79217123500 * x ^ 2 + 2 * (-74641653438) * x * y + 72669643440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 79217123500 72669643440 (-74641653438)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc57 (x y : ℝ) : 0 ≤ (214106730300 * x ^ 2 + 2 * (-202459134552) * x * y + 196592656700 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 214106730300 196592656700 (-202459134552)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc58 (x y : ℝ) : 0 ≤ (188065196800 * x ^ 2 + 2 * (-178796890332) * x * y + 177051147520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 188065196800 177051147520 (-178796890332)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc59 (x y : ℝ) : 0 ≤ (53579553280 * x ^ 2 + 2 * (-51462587952) * x * y + 53579553280 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 53579553280 53579553280 (-51462587952)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc60 (x y : ℝ) : 0 ≤ (31186743460 * x ^ 2 + 2 * (-30297173304) * x * y + 30084454820 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 31186743460 30084454820 (-30297173304)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc61 (x y : ℝ) : 0 ≤ (57045436800 * x ^ 2 + 2 * (-56034892944) * x * y + 55420430720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 57045436800 55420430720 (-56034892944)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc62 (x y : ℝ) : 0 ≤ (25547210560 * x ^ 2 + 2 * (-25443326376) * x * y + 25547210560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 25547210560 25547210560 (-25443326376)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc63 (x y : ℝ) : 0 ≤ (7343907200 * x ^ 2 + 2 * (-7228425036) * x * y + 7279510400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7343907200 7279510400 (-7228425036)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc64 (x y : ℝ) : 0 ≤ (6819049600 * x ^ 2 + 2 * (-6815939712) * x * y + 6819049600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6819049600 6819049600 (-6815939712)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc65 (x y : ℝ) : 0 ≤ (780436800 * x ^ 2 + 2 * (-767062440) * x * y + 780436800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 780436800 780436800 (-767062440)
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem B_ACE_entry11 (z w : ℝ) : 4423680 * Hdiag (1 - z / 2) ((1 + w) / 2) =
      801184320 * ((1 - z - w) ^ 10) +
      7007873280 * (w * (1 - z - w) ^ 9) +
      26584506240 * (w ^ 2 * (1 - z - w) ^ 8) +
      57424677120 * (w ^ 3 * (1 - z - w) ^ 7) +
      77762971200 * (w ^ 4 * (1 - z - w) ^ 6) +
      68316026880 * (w ^ 5 * (1 - z - w) ^ 5) +
      38811640320 * (w ^ 6 * (1 - z - w) ^ 4) +
      13695129600 * (w ^ 7 * (1 - z - w) ^ 3) +
      2713436160 * (w ^ 8 * (1 - z - w) ^ 2) +
      230031360 * (w ^ 9 * (1 - z - w)) +
      7460952480 * (z * (1 - z - w) ^ 9) +
      58776153440 * (z * w * (1 - z - w) ^ 8) +
      198552639840 * (z * w ^ 2 * (1 - z - w) ^ 7) +
      376536997920 * (z * w ^ 3 * (1 - z - w) ^ 6) +
      439718296960 * (z * w ^ 4 * (1 - z - w) ^ 5) +
      325715961600 * (z * w ^ 5 * (1 - z - w) ^ 4) +
      151771100160 * (z * w ^ 6 * (1 - z - w) ^ 3) +
      42612961280 * (z * w ^ 7 * (1 - z - w) ^ 2) +
      6599147520 * (z * w ^ 8 * (1 - z - w)) +
      460062720 * (z * w ^ 9) +
      31390895030 * (z ^ 2 * (1 - z - w) ^ 8) +
      219467133980 * (z ^ 2 * w * (1 - z - w) ^ 7) +
      647539119430 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 6) +
      1049750930640 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 5) +
      1016981401520 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 4) +
      597909592000 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 3) +
      206063595520 * (z ^ 2 * w ^ 6 * (1 - z - w) ^ 2) +
      37661306880 * (z ^ 2 * w ^ 7 * (1 - z - w)) +
      2813952000 * (z ^ 2 * w ^ 8) +
      79279247305 * (z ^ 3 * (1 - z - w) ^ 7) +
      484497605785 * (z ^ 3 * w * (1 - z - w) ^ 6) +
      1223690550760 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 5) +
      1648914440280 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 4) +
      1270957697600 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 3) +
      553853827840 * (z ^ 3 * w ^ 5 * (1 - z - w) ^ 2) +
      124036106240 * (z ^ 3 * w ^ 6 * (1 - z - w)) +
      10697728000 * (z ^ 3 * w ^ 7) +
      133999803415 * (z ^ 4 * (1 - z - w) ^ 6) +
      703211491460 * (z ^ 4 * w * (1 - z - w) ^ 5) +
      1483794037240 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 4) +
      1603758818480 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 3) +
      928767682400 * (z ^ 4 * w ^ 4 * (1 - z - w) ^ 2) +
      269451366400 * (z ^ 4 * w ^ 5 * (1 - z - w)) +
      29853414400 * (z ^ 4 * w ^ 6) +
      158981369160 * (z ^ 5 * (1 - z - w) ^ 5) +
      699438681620 * (z ^ 5 * w * (1 - z - w) ^ 4) +
      1190397082640 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 3) +
      975402834800 * (z ^ 5 * w ^ 3 * (1 - z - w) ^ 2) +
      381839208960 * (z ^ 5 * w ^ 4 * (1 - z - w)) +
      56389672960 * (z ^ 5 * w ^ 5) +
      134123536620 * (z ^ 6 * (1 - z - w) ^ 4) +
      476906315600 * (z ^ 6 * w * (1 - z - w) ^ 3) +
      617240360680 * (z ^ 6 * w ^ 2 * (1 - z - w) ^ 2) +
      343495425280 * (z ^ 6 * w ^ 3 * (1 - z - w)) +
      68951052800 * (z ^ 6 * w ^ 4) +
      79217123500 * (z ^ 7 * (1 - z - w) ^ 3) +
      214106730300 * (z ^ 7 * w * (1 - z - w) ^ 2) +
      188065196800 * (z ^ 7 * w ^ 2 * (1 - z - w)) +
      53579553280 * (z ^ 7 * w ^ 3) +
      31186743460 * (z ^ 8 * (1 - z - w) ^ 2) +
      57045436800 * (z ^ 8 * w * (1 - z - w)) +
      25547210560 * (z ^ 8 * w ^ 2) +
      7343907200 * (z ^ 9 * (1 - z - w)) +
      6819049600 * (z ^ 9 * w) +
      780436800 * (z ^ 10) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_ACE_entry22 (z w : ℝ) : 4423680 * Hdiag ((1 + w) / 2) (1 - z / 2) =
      268058655 * ((1 - z - w) ^ 10) +
      1920065325 * (w * (1 - z - w) ^ 9) +
      5656719270 * (w ^ 2 * (1 - z - w) ^ 8) +
      8752198440 * (w ^ 3 * (1 - z - w) ^ 7) +
      7541591760 * (w ^ 4 * (1 - z - w) ^ 6) +
      3815876160 * (w ^ 5 * (1 - z - w) ^ 5) +
      1914585600 * (w ^ 6 * (1 - z - w) ^ 4) +
      1661306880 * (w ^ 7 * (1 - z - w) ^ 3) +
      998522880 * (w ^ 8 * (1 - z - w) ^ 2) +
      230031360 * (w ^ 9 * (1 - z - w)) +
      2936473200 * (z * (1 - z - w) ^ 9) +
      19380035675 * (z * w * (1 - z - w) ^ 8) +
      52602330140 * (z * w ^ 2 * (1 - z - w) ^ 7) +
      75570771320 * (z * w ^ 3 * (1 - z - w) ^ 6) +
      62284122400 * (z * w ^ 4 * (1 - z - w) ^ 5) +
      32202166400 * (z * w ^ 5 * (1 - z - w) ^ 4) +
      14796600320 * (z * w ^ 6 * (1 - z - w) ^ 3) +
      8175841280 * (z * w ^ 7 * (1 - z - w) ^ 2) +
      3169320960 * (z * w ^ 8 * (1 - z - w)) +
      460062720 * (z * w ^ 9) +
      14779484630 * (z ^ 2 * (1 - z - w) ^ 8) +
      89806854575 * (z ^ 2 * w * (1 - z - w) ^ 7) +
      225369622110 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 6) +
      304175991480 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 5) +
      245019006320 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 4) +
      129945733440 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 3) +
      52889559040 * (z ^ 2 * w ^ 6 * (1 - z - w) ^ 2) +
      16943493120 * (z ^ 2 * w ^ 7 * (1 - z - w)) +
      2813952000 * (z ^ 2 * w ^ 8) +
      44632571780 * (z ^ 3 * (1 - z - w) ^ 7) +
      246964165405 * (z ^ 3 * w * (1 - z - w) ^ 6) +
      563752476640 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 5) +
      693673792760 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 4) +
      509551208000 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 3) +
      236862688000 * (z ^ 3 * w ^ 5 * (1 - z - w) ^ 2) +
      70261647360 * (z ^ 3 * w ^ 6 * (1 - z - w)) +
      10697728000 * (z ^ 3 * w ^ 7) +
      88853633115 * (z ^ 4 * (1 - z - w) ^ 6) +
      438296407780 * (z ^ 4 * w * (1 - z - w) ^ 5) +
      880557686400 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 4) +
      933496331520 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 3) +
      564123637600 * (z ^ 4 * w ^ 4 * (1 - z - w) ^ 2) +
      191617484800 * (z ^ 4 * w ^ 5 * (1 - z - w)) +
      29853414400 * (z ^ 4 * w ^ 6) +
      121070993140 * (z ^ 5 * (1 - z - w) ^ 5) +
      515756895280 * (z ^ 5 * w * (1 - z - w) ^ 4) +
      868221822640 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 3) +
      730966062960 * (z ^ 5 * w ^ 3 * (1 - z - w) ^ 2) +
      313815472640 * (z ^ 5 * w ^ 4 * (1 - z - w)) +
      56389672960 * (z ^ 5 * w ^ 5) +
      113823123940 * (z ^ 6 * (1 - z - w) ^ 4) +
      400069044260 * (z ^ 6 * w * (1 - z - w) ^ 3) +
      524496538600 * (z ^ 6 * w ^ 2 * (1 - z - w) ^ 2) +
      307365658880 * (z ^ 6 * w ^ 3 * (1 - z - w)) +
      68951052800 * (z ^ 6 * w ^ 4) +
      72669643440 * (z ^ 7 * (1 - z - w) ^ 3) +
      196592656700 * (z ^ 7 * w * (1 - z - w) ^ 2) +
      177051147520 * (z ^ 7 * w ^ 2 * (1 - z - w)) +
      53579553280 * (z ^ 7 * w ^ 3) +
      30084454820 * (z ^ 8 * (1 - z - w) ^ 2) +
      55420430720 * (z ^ 8 * w * (1 - z - w)) +
      25547210560 * (z ^ 8 * w ^ 2) +
      7279510400 * (z ^ 9 * (1 - z - w)) +
      6819049600 * (z ^ 9 * w) +
      780436800 * (z ^ 10) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_ACE_entry12 (z w : ℝ) : 4423680 * Hmixed (1 - z / 2) ((1 + w) / 2) =
      (-411481728) * ((1 - z - w) ^ 10) +
      (-3209126976) * (w * (1 - z - w) ^ 9) +
      (-10454658624) * (w ^ 2 * (1 - z - w) ^ 8) +
      (-18240186432) * (w ^ 3 * (1 - z - w) ^ 7) +
      (-17789831232) * (w ^ 4 * (1 - z - w) ^ 6) +
      (-8488967808) * (w ^ 5 * (1 - z - w) ^ 5) +
      (-95439360) * (w ^ 6 * (1 - z - w) ^ 4) +
      1846354944 * (w ^ 7 * (1 - z - w) ^ 3) +
      744124416 * (w ^ 8 * (1 - z - w) ^ 2) +
      84639744 * (w ^ 9 * (1 - z - w)) +
      (-4185961920) * (z * (1 - z - w) ^ 9) +
      (-29632145760) * (z * w * (1 - z - w) ^ 8) +
      (-86630082240) * (z * w ^ 2 * (1 - z - w) ^ 7) +
      (-133460600544) * (z * w ^ 3 * (1 - z - w) ^ 6) +
      (-111886516800) * (z * w ^ 4 * (1 - z - w) ^ 5) +
      (-42736161408) * (z * w ^ 5 * (1 - z - w) ^ 4) +
      3055601664 * (z * w ^ 6 * (1 - z - w) ^ 3) +
      8402734080 * (z * w ^ 7 * (1 - z - w) ^ 2) +
      2390065152 * (z * w ^ 8 * (1 - z - w)) +
      169279488 * (z * w ^ 9) +
      (-19481314914) * (z ^ 2 * (1 - z - w) ^ 8) +
      (-124332825768) * (z ^ 2 * w * (1 - z - w) ^ 7) +
      (-324046323834) * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 6) +
      (-438987322212) * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 5) +
      (-318758843664) * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 4) +
      (-105398188128) * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 3) +
      1761926016 * (z ^ 2 * w ^ 6 * (1 - z - w) ^ 2) +
      9822087168 * (z ^ 2 * w ^ 7 * (1 - z - w)) +
      1628307456 * (z ^ 2 * w ^ 8) +
      (-54691672848) * (z ^ 3 * (1 - z - w) ^ 7) +
      (-311730684192) * (z ^ 3 * w * (1 - z - w) ^ 6) +
      (-716736256092) * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 5) +
      (-845198541756) * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 4) +
      (-529916688240) * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 3) +
      (-158525660640) * (z ^ 3 * w ^ 5 * (1 - z - w) ^ 2) +
      (-11903869440) * (z ^ 3 * w ^ 6 * (1 - z - w)) +
      2206679040 * (z ^ 3 * w ^ 7) +
      (-102324581682) * (z ^ 4 * (1 - z - w) ^ 6) +
      (-512628000720) * (z ^ 4 * w * (1 - z - w) ^ 5) +
      (-1017766526376) * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 4) +
      (-1013083964844) * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 3) +
      (-521545831728) * (z ^ 4 * w ^ 4 * (1 - z - w) ^ 2) +
      (-125744474784) * (z ^ 4 * w ^ 5 * (1 - z - w)) +
      (-9808763904) * (z ^ 4 * w ^ 6) +
      (-132702817422) * (z ^ 5 * (1 - z - w) ^ 5) +
      (-569326452792) * (z ^ 5 * w * (1 - z - w) ^ 4) +
      (-938999538186) * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 3) +
      (-740212696656) * (z ^ 5 * w ^ 3 * (1 - z - w) ^ 2) +
      (-276355602480) * (z ^ 5 * w ^ 4 * (1 - z - w)) +
      (-38526237120) * (z ^ 5 * w ^ 5) +
      (-120168916596) * (z ^ 6 * (1 - z - w) ^ 4) +
      (-423759510600) * (z ^ 6 * w * (1 - z - w) ^ 3) +
      (-543451931640) * (z ^ 6 * w ^ 2 * (1 - z - w) ^ 2) +
      (-300022081320) * (z ^ 6 * w ^ 3 * (1 - z - w)) +
      (-60037960992) * (z ^ 6 * w ^ 4) +
      (-74641653438) * (z ^ 7 * (1 - z - w) ^ 3) +
      (-202459134552) * (z ^ 7 * w * (1 - z - w) ^ 2) +
      (-178796890332) * (z ^ 7 * w ^ 2 * (1 - z - w)) +
      (-51462587952) * (z ^ 7 * w ^ 3) +
      (-30297173304) * (z ^ 8 * (1 - z - w) ^ 2) +
      (-56034892944) * (z ^ 8 * w * (1 - z - w)) +
      (-25443326376) * (z ^ 8 * w ^ 2) +
      (-7228425036) * (z ^ 9 * (1 - z - w)) +
      (-6815939712) * (z ^ 9 * w) +
      (-767062440) * (z ^ 10) := by
  simp only [Hmixed, mixedNumerator, Sbound, denominator, kappaB]
  ring

private theorem B_ACE_entry11_list (z w : ℝ) :
    4423680 * Hdiag (1 - z / 2) ((1 + w) / 2) = ((B_ACE_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [B_ACE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_ACE_entry11 z w

private theorem B_ACE_entry22_list (z w : ℝ) :
    4423680 * Hdiag ((1 + w) / 2) (1 - z / 2) = ((B_ACE_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [B_ACE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_ACE_entry22 z w

private theorem B_ACE_entry12_list (z w : ℝ) :
    4423680 * Hmixed (1 - z / 2) ((1 + w) / 2) = ((B_ACE_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [B_ACE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_ACE_entry12 z w

private theorem B_ACE_oai {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag (1 - z / 2) ((1 + w) / 2) * x ^ 2 + 2 * Hmixed (1 - z / 2) ((1 + w) / 2) * x * y + Hdiag ((1 + w) / 2) (1 - z / 2) * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (B_ACE_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (B_ACE_hc0 x y) (by positivity),
      mul_nonneg (B_ACE_hc1 x y) (by positivity),
      mul_nonneg (B_ACE_hc2 x y) (by positivity),
      mul_nonneg (B_ACE_hc3 x y) (by positivity),
      mul_nonneg (B_ACE_hc4 x y) (by positivity),
      mul_nonneg (B_ACE_hc5 x y) (by positivity),
      mul_nonneg (B_ACE_hc6 x y) (by positivity),
      mul_nonneg (B_ACE_hc7 x y) (by positivity),
      mul_nonneg (B_ACE_hc8 x y) (by positivity),
      mul_nonneg (B_ACE_hc9 x y) (by positivity),
      mul_nonneg (B_ACE_hc11 x y) (by positivity),
      mul_nonneg (B_ACE_hc12 x y) (by positivity),
      mul_nonneg (B_ACE_hc13 x y) (by positivity),
      mul_nonneg (B_ACE_hc14 x y) (by positivity),
      mul_nonneg (B_ACE_hc15 x y) (by positivity),
      mul_nonneg (B_ACE_hc16 x y) (by positivity),
      mul_nonneg (B_ACE_hc17 x y) (by positivity),
      mul_nonneg (B_ACE_hc18 x y) (by positivity),
      mul_nonneg (B_ACE_hc19 x y) (by positivity),
      mul_nonneg (B_ACE_hc20 x y) (by positivity),
      mul_nonneg (B_ACE_hc21 x y) (by positivity),
      mul_nonneg (B_ACE_hc22 x y) (by positivity),
      mul_nonneg (B_ACE_hc23 x y) (by positivity),
      mul_nonneg (B_ACE_hc24 x y) (by positivity),
      mul_nonneg (B_ACE_hc25 x y) (by positivity),
      mul_nonneg (B_ACE_hc26 x y) (by positivity),
      mul_nonneg (B_ACE_hc27 x y) (by positivity),
      mul_nonneg (B_ACE_hc28 x y) (by positivity),
      mul_nonneg (B_ACE_hc29 x y) (by positivity),
      mul_nonneg (B_ACE_hc30 x y) (by positivity),
      mul_nonneg (B_ACE_hc31 x y) (by positivity),
      mul_nonneg (B_ACE_hc32 x y) (by positivity),
      mul_nonneg (B_ACE_hc33 x y) (by positivity),
      mul_nonneg (B_ACE_hc34 x y) (by positivity),
      mul_nonneg (B_ACE_hc35 x y) (by positivity),
      mul_nonneg (B_ACE_hc36 x y) (by positivity),
      mul_nonneg (B_ACE_hc37 x y) (by positivity),
      mul_nonneg (B_ACE_hc38 x y) (by positivity),
      mul_nonneg (B_ACE_hc39 x y) (by positivity),
      mul_nonneg (B_ACE_hc40 x y) (by positivity),
      mul_nonneg (B_ACE_hc41 x y) (by positivity),
      mul_nonneg (B_ACE_hc42 x y) (by positivity),
      mul_nonneg (B_ACE_hc43 x y) (by positivity),
      mul_nonneg (B_ACE_hc44 x y) (by positivity),
      mul_nonneg (B_ACE_hc45 x y) (by positivity),
      mul_nonneg (B_ACE_hc46 x y) (by positivity),
      mul_nonneg (B_ACE_hc47 x y) (by positivity),
      mul_nonneg (B_ACE_hc48 x y) (by positivity),
      mul_nonneg (B_ACE_hc49 x y) (by positivity),
      mul_nonneg (B_ACE_hc50 x y) (by positivity),
      mul_nonneg (B_ACE_hc51 x y) (by positivity),
      mul_nonneg (B_ACE_hc52 x y) (by positivity),
      mul_nonneg (B_ACE_hc53 x y) (by positivity),
      mul_nonneg (B_ACE_hc54 x y) (by positivity),
      mul_nonneg (B_ACE_hc55 x y) (by positivity),
      mul_nonneg (B_ACE_hc56 x y) (by positivity),
      mul_nonneg (B_ACE_hc57 x y) (by positivity),
      mul_nonneg (B_ACE_hc58 x y) (by positivity),
      mul_nonneg (B_ACE_hc59 x y) (by positivity),
      mul_nonneg (B_ACE_hc60 x y) (by positivity),
      mul_nonneg (B_ACE_hc61 x y) (by positivity),
      mul_nonneg (B_ACE_hc62 x y) (by positivity),
      mul_nonneg (B_ACE_hc63 x y) (by positivity),
      mul_nonneg (B_ACE_hc64 x y) (by positivity),
      mul_nonneg (B_ACE_hc65 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (B_ACE_data z w) x y hcoeff
  rw [← B_ACE_entry11_list, ← B_ACE_entry12_list, ← B_ACE_entry22_list] at hpos
  nlinarith only [hpos]

end

end PositiveEinsteinFour.Quadratic
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Quadratic.B_ACE_oai := @OAI.PositiveEinsteinFour.Quadratic.B_ACE_oai
