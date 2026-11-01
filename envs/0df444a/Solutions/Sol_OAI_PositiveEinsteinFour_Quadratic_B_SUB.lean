-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Quadratic.B_SUB
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:29:59.225833+00:00
-- url     : https://prove2.me/submissions/3313a8f3-1296-49a3-b44e-d8d5bf7220a3

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

private theorem B_SUB_hc0 (x y : ℝ) : 0 ≤ (49168270 * x ^ 2 + 2 * (-22336704) * x * y + 41183930 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 49168270 41183930 (-22336704)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc1 (x y : ℝ) : 0 ≤ (543388840 * x ^ 2 + 2 * (-243425088) * x * y + 415822560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 543388840 415822560 (-243425088)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc2 (x y : ℝ) : 0 ≤ (2673339480 * x ^ 2 + 2 * (-1153680480) * x * y + 1794425480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2673339480 1794425480 (-1153680480)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc3 (x y : ℝ) : 0 ≤ (7760123200 * x ^ 2 + 2 * (-3112849152) * x * y + 4314525920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7760123200 4314525920 (-3112849152)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc4 (x y : ℝ) : 0 ≤ (14806380960 * x ^ 2 + 2 * (-5245682976) * x * y + 6303251040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 14806380960 6303251040 (-5245682976)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc5 (x y : ℝ) : 0 ≤ (19443891840 * x ^ 2 + 2 * (-5679671040) * x * y + 5702181120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 19443891840 5702181120 (-5679671040)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc6 (x y : ℝ) : 0 ≤ (17677765760 * x ^ 2 + 2 * (-3893891328) * x * y + 3095873920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 17677765760 3095873920 (-3893891328)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc7 (x y : ℝ) : 0 ≤ (10734141440 * x ^ 2 + 2 * (-1583225856) * x * y + 913528320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 10734141440 913528320 (-1583225856)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc8 (x y : ℝ) : 0 ≤ (3931484160 * x ^ 2 + 2 * (-322748928) * x * y + 114227200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3931484160 114227200 (-322748928)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc9 (x y : ℝ) : 0 ≤ (656629760 * x ^ 2 + 2 * (-19169280) * x * y + 2867200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 656629760 2867200 (-19169280)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc10 (x y : ℝ) : 0 ≤ (1411623920 * x ^ 2 + 2 * (-568507731) * x * y + 393850220 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1411623920 393850220 (-568507731)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc11 (x y : ℝ) : 0 ≤ (13273615880 * x ^ 2 + 2 * (-5483286111) * x * y + 3716574680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 13273615880 3716574680 (-5483286111)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc12 (x y : ℝ) : 0 ≤ (53824274400 * x ^ 2 + 2 * (-22430970468) * x * y + 14697336080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 53824274400 14697336080 (-22430970468)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc13 (x y : ℝ) : 0 ≤ (123134689280 * x ^ 2 + 2 * (-50644725144) * x * y + 31604568320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 123134689280 31604568320 (-50644725144)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc14 (x y : ℝ) : 0 ≤ (174270951680 * x ^ 2 + 2 * (-68544068208) * x * y + 40055151680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 174270951680 40055151680 (-68544068208)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc15 (x y : ℝ) : 0 ≤ (156863665280 * x ^ 2 + 2 * (-56169060720) * x * y + 30163859840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 156863665280 30163859840 (-56169060720)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc16 (x y : ℝ) : 0 ≤ (88221780480 * x ^ 2 + 2 * (-26440593984) * x * y + 12790106880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 88221780480 12790106880 (-26440593984)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc17 (x y : ℝ) : 0 ≤ (28595973120 * x ^ 2 + 2 * (-6077335296) * x * y + 2610508800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 28595973120 2610508800 (-6077335296)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc18 (x y : ℝ) : 0 ≤ (4140032000 * x ^ 2 + 2 * (-390266880) * x * y + 159129600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4140032000 159129600 (-390266880)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc19 (x y : ℝ) : 0 ≤ (7469862110 * x ^ 2 + 2 * (-3079817403) * x * y + 1669286890 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7469862110 1669286890 (-3079817403)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc20 (x y : ℝ) : 0 ≤ (60205371080 * x ^ 2 + 2 * (-25619389440) * x * y + 14032682720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 60205371080 14032682720 (-25619389440)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc21 (x y : ℝ) : 0 ≤ (203544223600 * x ^ 2 + 2 * (-87982309740) * x * y + 48056590480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 203544223600 48056590480 (-87982309740)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc22 (x y : ℝ) : 0 ≤ (373399956320 * x ^ 2 + 2 * (-160643005848) * x * y + 86336007200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 373399956320 86336007200 (-160643005848)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc23 (x y : ℝ) : 0 ≤ (400157511840 * x ^ 2 + 2 * (-166234328256) * x * y + 86884020960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 400157511840 86884020960 (-166234328256)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc24 (x y : ℝ) : 0 ≤ (249290947840 * x ^ 2 + 2 * (-94812150432) * x * y + 47859667840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 249290947840 47859667840 (-94812150432)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc25 (x y : ℝ) : 0 ≤ (82949318400 * x ^ 2 + 2 * (-25713724800) * x * y + 12663558400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 82949318400 12663558400 (-25713724800)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc26 (x y : ℝ) : 0 ≤ (11227755520 * x ^ 2 + 2 * (-1935458304) * x * y + 1048238080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 11227755520 1048238080 (-1935458304)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc27 (x y : ℝ) : 0 ≤ (18701432940 * x ^ 2 + 2 * (-8380386078) * x * y + 4477312320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 18701432940 4477312320 (-8380386078)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc28 (x y : ℝ) : 0 ≤ (125716400880 * x ^ 2 + 2 * (-57907053450) * x * y + 31599593360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 125716400880 31599593360 (-57907053450)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc29 (x y : ℝ) : 0 ≤ (341672107600 * x ^ 2 + 2 * (-159635026176) * x * y + 88142738800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 341672107600 88142738800 (-159635026176)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc30 (x y : ℝ) : 0 ≤ (476720688000 * x ^ 2 + 2 * (-221770504608) * x * y + 123060686720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 476720688000 123060686720 (-221770504608)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc31 (x y : ℝ) : 0 ≤ (355101402880 * x ^ 2 + 2 * (-159320425824) * x * y + 88912475840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 355101402880 88912475840 (-159320425824)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc32 (x y : ℝ) : 0 ≤ (130187968000 * x ^ 2 + 2 * (-52398289248) * x * y + 30131228160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 130187968000 30131228160 (-52398289248)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc33 (x y : ℝ) : 0 ≤ (17145254400 * x ^ 2 + 2 * (-4728342528) * x * y + 3266539520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 17145254400 3266539520 (-4728342528)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc34 (x y : ℝ) : 0 ≤ (27140741400 * x ^ 2 + 2 * (-13757379354) * x * y + 8132644800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 27140741400 8132644800 (-13757379354)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc35 (x y : ℝ) : 0 ≤ (146059566320 * x ^ 2 + 2 * (-75561729732) * x * y + 45703501360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 146059566320 45703501360 (-75561729732)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc36 (x y : ℝ) : 0 ≤ (300518359280 * x ^ 2 + 2 * (-157336610328) * x * y + 97358206160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 300518359280 97358206160 (-157336610328)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc37 (x y : ℝ) : 0 ≤ (289056963520 * x ^ 2 + 2 * (-150986683632) * x * y + 96381975040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 289056963520 96381975040 (-150986683632)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc38 (x y : ℝ) : 0 ≤ (123778866240 * x ^ 2 + 2 * (-62428893696) * x * y + 42621838400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 123778866240 42621838400 (-62428893696)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc39 (x y : ℝ) : 0 ≤ (16242622720 * x ^ 2 + 2 * (-6906190848) * x * y + 6034667520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 16242622720 6034667520 (-6906190848)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc40 (x y : ℝ) : 0 ≤ (24392653680 * x ^ 2 + 2 * (-14312214684) * x * y + 9813151200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 24392653680 9813151200 (-14312214684)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc41 (x y : ℝ) : 0 ≤ (98710177600 * x ^ 2 + 2 * (-58990890096) * x * y + 41738952960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 98710177600 41738952960 (-58990890096)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc42 (x y : ℝ) : 0 ≤ (138513159520 * x ^ 2 + 2 * (-84419254128) * x * y + 62620629760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 138513159520 62620629760 (-84419254128)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc43 (x y : ℝ) : 0 ≤ (74496707200 * x ^ 2 + 2 * (-46499686656) * x * y + 37887058560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 74496707200 37887058560 (-46499686656)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc44 (x y : ℝ) : 0 ≤ (9946865280 * x ^ 2 + 2 * (-6514311168) * x * y + 7120701440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 9946865280 7120701440 (-6514311168)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc45 (x y : ℝ) : 0 ≤ (13580183000 * x ^ 2 + 2 * (-9337286520) * x * y + 7571487400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 13580183000 7571487400 (-9337286520)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc46 (x y : ℝ) : 0 ≤ (37110996800 * x ^ 2 + 2 * (-26376268896) * x * y + 22690404320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 37110996800 22690404320 (-26376268896)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc47 (x y : ℝ) : 0 ≤ (28376274400 * x ^ 2 + 2 * (-21625075680) * x * y + 20857274720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 28376274400 20857274720 (-21625075680)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc48 (x y : ℝ) : 0 ≤ (4029969280 * x ^ 2 + 2 * (-4056941568) * x * y + 5443379200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4029969280 5443379200 (-4056941568)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc49 (x y : ℝ) : 0 ≤ (4394016400 * x ^ 2 + 2 * (-3585031680) * x * y + 3522363040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4394016400 3522363040 (-3585031680)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc50 (x y : ℝ) : 0 ≤ (6436015680 * x ^ 2 + 2 * (-5805189888) * x * y + 6506192960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6436015680 6506192960 (-5805189888)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc51 (x y : ℝ) : 0 ≤ (1115109440 * x ^ 2 + 2 * (-1628974080) * x * y + 2615101440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1115109440 2615101440 (-1628974080)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc52 (x y : ℝ) : 0 ≤ (683864320 * x ^ 2 + 2 * (-690057984) * x * y + 878089760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 683864320 878089760 (-690057984)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc53 (x y : ℝ) : 0 ≤ (216320000 * x ^ 2 + 2 * (-384872448) * x * y + 718336000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 216320000 718336000 (-384872448)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc54 (x y : ℝ) : 0 ≤ (24092160 * x ^ 2 + 2 * (-40737792) * x * y + 86016000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 24092160 86016000 (-40737792)
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem B_SUB_entry11 (z w : ℝ) : 552960 * Hdiag ((3 - z + w) / 2) ((1 - z - w) / 2) =
      49168270 * ((1 - z - w) ^ 9) +
      543388840 * (w * (1 - z - w) ^ 8) +
      2673339480 * (w ^ 2 * (1 - z - w) ^ 7) +
      7760123200 * (w ^ 3 * (1 - z - w) ^ 6) +
      14806380960 * (w ^ 4 * (1 - z - w) ^ 5) +
      19443891840 * (w ^ 5 * (1 - z - w) ^ 4) +
      17677765760 * (w ^ 6 * (1 - z - w) ^ 3) +
      10734141440 * (w ^ 7 * (1 - z - w) ^ 2) +
      3931484160 * (w ^ 8 * (1 - z - w)) +
      656629760 * (w ^ 9) +
      1411623920 * (z * (1 - z - w) ^ 8) +
      13273615880 * (z * w * (1 - z - w) ^ 7) +
      53824274400 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      123134689280 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      174270951680 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      156863665280 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      88221780480 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      28595973120 * (z * w ^ 7 * (1 - z - w)) +
      4140032000 * (z * w ^ 8) +
      7469862110 * (z ^ 2 * (1 - z - w) ^ 7) +
      60205371080 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      203544223600 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      373399956320 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      400157511840 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      249290947840 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      82949318400 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      11227755520 * (z ^ 2 * w ^ 7) +
      18701432940 * (z ^ 3 * (1 - z - w) ^ 6) +
      125716400880 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      341672107600 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      476720688000 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      355101402880 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      130187968000 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      17145254400 * (z ^ 3 * w ^ 6) +
      27140741400 * (z ^ 4 * (1 - z - w) ^ 5) +
      146059566320 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      300518359280 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      289056963520 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      123778866240 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      16242622720 * (z ^ 4 * w ^ 5) +
      24392653680 * (z ^ 5 * (1 - z - w) ^ 4) +
      98710177600 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      138513159520 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      74496707200 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      9946865280 * (z ^ 5 * w ^ 4) +
      13580183000 * (z ^ 6 * (1 - z - w) ^ 3) +
      37110996800 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      28376274400 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      4029969280 * (z ^ 6 * w ^ 3) +
      4394016400 * (z ^ 7 * (1 - z - w) ^ 2) +
      6436015680 * (z ^ 7 * w * (1 - z - w)) +
      1115109440 * (z ^ 7 * w ^ 2) +
      683864320 * (z ^ 8 * (1 - z - w)) +
      216320000 * (z ^ 8 * w) +
      24092160 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_SUB_entry22 (z w : ℝ) : 552960 * Hdiag ((1 - z - w) / 2) ((3 - z + w) / 2) =
      41183930 * ((1 - z - w) ^ 9) +
      415822560 * (w * (1 - z - w) ^ 8) +
      1794425480 * (w ^ 2 * (1 - z - w) ^ 7) +
      4314525920 * (w ^ 3 * (1 - z - w) ^ 6) +
      6303251040 * (w ^ 4 * (1 - z - w) ^ 5) +
      5702181120 * (w ^ 5 * (1 - z - w) ^ 4) +
      3095873920 * (w ^ 6 * (1 - z - w) ^ 3) +
      913528320 * (w ^ 7 * (1 - z - w) ^ 2) +
      114227200 * (w ^ 8 * (1 - z - w)) +
      2867200 * (w ^ 9) +
      393850220 * (z * (1 - z - w) ^ 8) +
      3716574680 * (z * w * (1 - z - w) ^ 7) +
      14697336080 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      31604568320 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      40055151680 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      30163859840 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      12790106880 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      2610508800 * (z * w ^ 7 * (1 - z - w)) +
      159129600 * (z * w ^ 8) +
      1669286890 * (z ^ 2 * (1 - z - w) ^ 7) +
      14032682720 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      48056590480 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      86336007200 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      86884020960 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      47859667840 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      12663558400 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      1048238080 * (z ^ 2 * w ^ 7) +
      4477312320 * (z ^ 3 * (1 - z - w) ^ 6) +
      31599593360 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      88142738800 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      123060686720 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      88912475840 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      30131228160 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      3266539520 * (z ^ 3 * w ^ 6) +
      8132644800 * (z ^ 4 * (1 - z - w) ^ 5) +
      45703501360 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      97358206160 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      96381975040 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      42621838400 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      6034667520 * (z ^ 4 * w ^ 5) +
      9813151200 * (z ^ 5 * (1 - z - w) ^ 4) +
      41738952960 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      62620629760 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      37887058560 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      7120701440 * (z ^ 5 * w ^ 4) +
      7571487400 * (z ^ 6 * (1 - z - w) ^ 3) +
      22690404320 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      20857274720 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      5443379200 * (z ^ 6 * w ^ 3) +
      3522363040 * (z ^ 7 * (1 - z - w) ^ 2) +
      6506192960 * (z ^ 7 * w * (1 - z - w)) +
      2615101440 * (z ^ 7 * w ^ 2) +
      878089760 * (z ^ 8 * (1 - z - w)) +
      718336000 * (z ^ 8 * w) +
      86016000 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_SUB_entry12 (z w : ℝ) : 552960 * Hmixed ((3 - z + w) / 2) ((1 - z - w) / 2) =
      (-22336704) * ((1 - z - w) ^ 9) +
      (-243425088) * (w * (1 - z - w) ^ 8) +
      (-1153680480) * (w ^ 2 * (1 - z - w) ^ 7) +
      (-3112849152) * (w ^ 3 * (1 - z - w) ^ 6) +
      (-5245682976) * (w ^ 4 * (1 - z - w) ^ 5) +
      (-5679671040) * (w ^ 5 * (1 - z - w) ^ 4) +
      (-3893891328) * (w ^ 6 * (1 - z - w) ^ 3) +
      (-1583225856) * (w ^ 7 * (1 - z - w) ^ 2) +
      (-322748928) * (w ^ 8 * (1 - z - w)) +
      (-19169280) * (w ^ 9) +
      (-568507731) * (z * (1 - z - w) ^ 8) +
      (-5483286111) * (z * w * (1 - z - w) ^ 7) +
      (-22430970468) * (z * w ^ 2 * (1 - z - w) ^ 6) +
      (-50644725144) * (z * w ^ 3 * (1 - z - w) ^ 5) +
      (-68544068208) * (z * w ^ 4 * (1 - z - w) ^ 4) +
      (-56169060720) * (z * w ^ 5 * (1 - z - w) ^ 3) +
      (-26440593984) * (z * w ^ 6 * (1 - z - w) ^ 2) +
      (-6077335296) * (z * w ^ 7 * (1 - z - w)) +
      (-390266880) * (z * w ^ 8) +
      (-3079817403) * (z ^ 2 * (1 - z - w) ^ 7) +
      (-25619389440) * (z ^ 2 * w * (1 - z - w) ^ 6) +
      (-87982309740) * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      (-160643005848) * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      (-166234328256) * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      (-94812150432) * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      (-25713724800) * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      (-1935458304) * (z ^ 2 * w ^ 7) +
      (-8380386078) * (z ^ 3 * (1 - z - w) ^ 6) +
      (-57907053450) * (z ^ 3 * w * (1 - z - w) ^ 5) +
      (-159635026176) * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      (-221770504608) * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      (-159320425824) * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      (-52398289248) * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      (-4728342528) * (z ^ 3 * w ^ 6) +
      (-13757379354) * (z ^ 4 * (1 - z - w) ^ 5) +
      (-75561729732) * (z ^ 4 * w * (1 - z - w) ^ 4) +
      (-157336610328) * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      (-150986683632) * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      (-62428893696) * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      (-6906190848) * (z ^ 4 * w ^ 5) +
      (-14312214684) * (z ^ 5 * (1 - z - w) ^ 4) +
      (-58990890096) * (z ^ 5 * w * (1 - z - w) ^ 3) +
      (-84419254128) * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      (-46499686656) * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      (-6514311168) * (z ^ 5 * w ^ 4) +
      (-9337286520) * (z ^ 6 * (1 - z - w) ^ 3) +
      (-26376268896) * (z ^ 6 * w * (1 - z - w) ^ 2) +
      (-21625075680) * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      (-4056941568) * (z ^ 6 * w ^ 3) +
      (-3585031680) * (z ^ 7 * (1 - z - w) ^ 2) +
      (-5805189888) * (z ^ 7 * w * (1 - z - w)) +
      (-1628974080) * (z ^ 7 * w ^ 2) +
      (-690057984) * (z ^ 8 * (1 - z - w)) +
      (-384872448) * (z ^ 8 * w) +
      (-40737792) * (z ^ 9) := by
  simp only [Hmixed, mixedNumerator, Sbound, denominator, kappaB]
  ring

private theorem B_SUB_entry11_list (z w : ℝ) :
    552960 * Hdiag ((3 - z + w) / 2) ((1 - z - w) / 2) = ((B_SUB_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [B_SUB_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_SUB_entry11 z w

private theorem B_SUB_entry22_list (z w : ℝ) :
    552960 * Hdiag ((1 - z - w) / 2) ((3 - z + w) / 2) = ((B_SUB_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [B_SUB_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_SUB_entry22 z w

private theorem B_SUB_entry12_list (z w : ℝ) :
    552960 * Hmixed ((3 - z + w) / 2) ((1 - z - w) / 2) = ((B_SUB_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [B_SUB_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_SUB_entry12 z w

private theorem B_SUB_oai {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag ((3 - z + w) / 2) ((1 - z - w) / 2) * x ^ 2 + 2 * Hmixed ((3 - z + w) / 2) ((1 - z - w) / 2) * x * y + Hdiag ((1 - z - w) / 2) ((3 - z + w) / 2) * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (B_SUB_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (B_SUB_hc0 x y) (by positivity),
      mul_nonneg (B_SUB_hc1 x y) (by positivity),
      mul_nonneg (B_SUB_hc2 x y) (by positivity),
      mul_nonneg (B_SUB_hc3 x y) (by positivity),
      mul_nonneg (B_SUB_hc4 x y) (by positivity),
      mul_nonneg (B_SUB_hc5 x y) (by positivity),
      mul_nonneg (B_SUB_hc6 x y) (by positivity),
      mul_nonneg (B_SUB_hc7 x y) (by positivity),
      mul_nonneg (B_SUB_hc8 x y) (by positivity),
      mul_nonneg (B_SUB_hc9 x y) (by positivity),
      mul_nonneg (B_SUB_hc10 x y) (by positivity),
      mul_nonneg (B_SUB_hc11 x y) (by positivity),
      mul_nonneg (B_SUB_hc12 x y) (by positivity),
      mul_nonneg (B_SUB_hc13 x y) (by positivity),
      mul_nonneg (B_SUB_hc14 x y) (by positivity),
      mul_nonneg (B_SUB_hc15 x y) (by positivity),
      mul_nonneg (B_SUB_hc16 x y) (by positivity),
      mul_nonneg (B_SUB_hc17 x y) (by positivity),
      mul_nonneg (B_SUB_hc18 x y) (by positivity),
      mul_nonneg (B_SUB_hc19 x y) (by positivity),
      mul_nonneg (B_SUB_hc20 x y) (by positivity),
      mul_nonneg (B_SUB_hc21 x y) (by positivity),
      mul_nonneg (B_SUB_hc22 x y) (by positivity),
      mul_nonneg (B_SUB_hc23 x y) (by positivity),
      mul_nonneg (B_SUB_hc24 x y) (by positivity),
      mul_nonneg (B_SUB_hc25 x y) (by positivity),
      mul_nonneg (B_SUB_hc26 x y) (by positivity),
      mul_nonneg (B_SUB_hc27 x y) (by positivity),
      mul_nonneg (B_SUB_hc28 x y) (by positivity),
      mul_nonneg (B_SUB_hc29 x y) (by positivity),
      mul_nonneg (B_SUB_hc30 x y) (by positivity),
      mul_nonneg (B_SUB_hc31 x y) (by positivity),
      mul_nonneg (B_SUB_hc32 x y) (by positivity),
      mul_nonneg (B_SUB_hc33 x y) (by positivity),
      mul_nonneg (B_SUB_hc34 x y) (by positivity),
      mul_nonneg (B_SUB_hc35 x y) (by positivity),
      mul_nonneg (B_SUB_hc36 x y) (by positivity),
      mul_nonneg (B_SUB_hc37 x y) (by positivity),
      mul_nonneg (B_SUB_hc38 x y) (by positivity),
      mul_nonneg (B_SUB_hc39 x y) (by positivity),
      mul_nonneg (B_SUB_hc40 x y) (by positivity),
      mul_nonneg (B_SUB_hc41 x y) (by positivity),
      mul_nonneg (B_SUB_hc42 x y) (by positivity),
      mul_nonneg (B_SUB_hc43 x y) (by positivity),
      mul_nonneg (B_SUB_hc44 x y) (by positivity),
      mul_nonneg (B_SUB_hc45 x y) (by positivity),
      mul_nonneg (B_SUB_hc46 x y) (by positivity),
      mul_nonneg (B_SUB_hc47 x y) (by positivity),
      mul_nonneg (B_SUB_hc48 x y) (by positivity),
      mul_nonneg (B_SUB_hc49 x y) (by positivity),
      mul_nonneg (B_SUB_hc50 x y) (by positivity),
      mul_nonneg (B_SUB_hc51 x y) (by positivity),
      mul_nonneg (B_SUB_hc52 x y) (by positivity),
      mul_nonneg (B_SUB_hc53 x y) (by positivity),
      mul_nonneg (B_SUB_hc54 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (B_SUB_data z w) x y hcoeff
  rw [← B_SUB_entry11_list, ← B_SUB_entry12_list, ← B_SUB_entry22_list] at hpos
  nlinarith only [hpos]

end

end PositiveEinsteinFour.Quadratic
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Quadratic.B_SUB_oai := @OAI.PositiveEinsteinFour.Quadratic.B_SUB_oai
