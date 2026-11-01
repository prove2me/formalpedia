-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Quadratic.axial_matrix_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T18:54:51.730342+00:00
-- url     : https://prove2.me/submissions/769bad73-b3e6-48e7-867e-2098f804e998

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

private theorem A_OSC_hc0 (x y : ℝ) : 0 ≤ (17252710400 * x ^ 2 + 2 * 0 * x * y + 3450542080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 17252710400 3450542080 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc1 (x y : ℝ) : 0 ≤ (158056814080 * x ^ 2 + 2 * 0 * x * y + 31611362816 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 158056814080 31611362816 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc2 (x y : ℝ) : 0 ≤ (479164067840 * x ^ 2 + 2 * 16412221440 * x * y + 108962590720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 479164067840 108962590720 16412221440
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc3 (x y : ℝ) : 0 ≤ (715874263040 * x ^ 2 + 2 * 75585669120 * x * y + 202056613888 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 715874263040 202056613888 75585669120
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc4 (x y : ℝ) : 0 ≤ (621716700160 * x ^ 2 + 2 * 139843399680 * x * y + 228817943552 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 621716700160 228817943552 139843399680
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc5 (x y : ℝ) : 0 ≤ (359540042240 * x ^ 2 + 2 * 131761336320 * x * y + 163584352768 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 359540042240 163584352768 131761336320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc6 (x y : ℝ) : 0 ≤ (155718743040 * x ^ 2 + 2 * 65896980480 * x * y + 71196115968 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 155718743040 71196115968 65896980480
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc7 (x y : ℝ) : 0 ≤ (46921236480 * x ^ 2 + 2 * 16428533760 * x * y + 16728219648 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 46921236480 16728219648 16428533760
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc8 (x y : ℝ) : 0 ≤ (6540134400 * x ^ 2 + 2 * 1622937600 * x * y + 1553356800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6540134400 1553356800 1622937600
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc9 (x y : ℝ) : 0 ≤ (115729146880 * x ^ 2 + 2 * 0 * x * y + 23145829376 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 115729146880 23145829376 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc10 (x y : ℝ) : 0 ≤ (868924433920 * x ^ 2 + 2 * 32824442880 * x * y + 200044441088 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 868924433920 200044441088 32824442880
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc11 (x y : ℝ) : 0 ≤ (2199990382080 * x ^ 2 + 2 * 228584908800 * x * y + 618105681408 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2199990382080 618105681408 228584908800
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc12 (x y : ℝ) : 0 ≤ (2777259973120 * x ^ 2 + 2 * 569280360960 * x * y + 981187455488 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2777259973120 981187455488 569280360960
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc13 (x y : ℝ) : 0 ≤ (2096990801920 * x ^ 2 + 2 * 678715292160 * x * y + 893889413120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2096990801920 893889413120 678715292160
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc14 (x y : ℝ) : 0 ≤ (1065675640320 * x ^ 2 + 2 * 413946155520 * x * y + 469378856448 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1065675640320 469378856448 413946155520
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc15 (x y : ℝ) : 0 ≤ (352909432320 * x ^ 2 + 2 * 122889991680 * x * y + 129556729344 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 352909432320 129556729344 122889991680
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc16 (x y : ℝ) : 0 ≤ (53759715840 * x ^ 2 + 2 * 14139233280 * x * y + 14086900224 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 53759715840 14086900224 14139233280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc17 (x y : ℝ) : 0 ≤ (317429568480 * x ^ 2 + 2 * 16412221440 * x * y + 76615690848 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 317429568480 76615690848 16412221440
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc18 (x y : ℝ) : 0 ≤ (2004721901600 * x ^ 2 + 2 * 230412810240 * x * y + 580514306464 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2004721901600 580514306464 230412810240
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc19 (x y : ℝ) : 0 ≤ (4293146296480 * x ^ 2 + 2 * 870472316160 * x * y + 1510341325856 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4293146296480 1510341325856 870472316160
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc20 (x y : ℝ) : 0 ≤ (4635392834400 * x ^ 2 + 2 * 1402601150880 * x * y + 1912483495776 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4635392834400 1912483495776 1402601150880
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc21 (x y : ℝ) : 0 ≤ (2977183602080 * x ^ 2 + 2 * 1087456210560 * x * y + 1280348492704 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2977183602080 1280348492704 1087456210560
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc22 (x y : ℝ) : 0 ≤ (1143655466560 * x ^ 2 + 2 * 395407510560 * x * y + 430117149632 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1143655466560 430117149632 395407510560
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc23 (x y : ℝ) : 0 ≤ (196010735520 * x ^ 2 + 2 * 54080723520 * x * y + 55809442464 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 196010735520 55809442464 54080723520
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc24 (x y : ℝ) : 0 ≤ (480178552960 * x ^ 2 + 2 * 77413570560 * x * y + 156379793024 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 480178552960 156379793024 77413570560
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc25 (x y : ℝ) : 0 ≤ (2603039483520 * x ^ 2 + 2 * 592477148160 * x * y + 964724061312 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2603039483520 964724061312 592477148160
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc26 (x y : ℝ) : 0 ≤ (4741503929600 * x ^ 2 + 2 * 1453216430880 * x * y + 1974404593792 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4741503929600 1974404593792 1453216430880
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc27 (x y : ℝ) : 0 ≤ (4260670908800 * x ^ 2 + 2 * 1528657741440 * x * y + 1830675210112 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4260670908800 1830675210112 1528657741440
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc28 (x y : ℝ) : 0 ≤ (2038681949120 * x ^ 2 + 2 * 709121944800 * x * y + 787479157024 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2038681949120 787479157024 709121944800
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc29 (x y : ℝ) : 0 ≤ (410625264960 * x ^ 2 + 2 * 118617056640 * x * y + 125658517536 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 410625264960 125658517536 118617056640
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc30 (x y : ℝ) : 0 ≤ (454056140000 * x ^ 2 + 2 * 151441793280 * x * y + 204476183392 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 454056140000 204476183392 151441793280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc31 (x y : ℝ) : 0 ≤ (2133392931580 * x ^ 2 + 2 * 754683896160 * x * y + 962254704716 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2133392931580 962254704716 754683896160
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc32 (x y : ℝ) : 0 ≤ (3203939071020 * x ^ 2 + 2 * 1212283815210 * x * y + 1428624843972 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3203939071020 1428624843972 1212283815210
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc33 (x y : ℝ) : 0 ≤ (2117912965930 * x ^ 2 + 2 * 765276701850 * x * y + 851201225066 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2117912965930 851201225066 765276701850
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc34 (x y : ℝ) : 0 ≤ (534168603450 * x ^ 2 + 2 * 163163833200 * x * y + 174955046445 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 534168603450 174955046445 163163833200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc35 (x y : ℝ) : 0 ≤ (287785218300 * x ^ 2 + 2 * 157114660320 * x * y + 169619374668 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 287785218300 169619374668 157114660320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc36 (x y : ℝ) : 0 ≤ (1135771302200 * x ^ 2 + 2 * 514070353620 * x * y + 565947886312 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1135771302200 565947886312 514070353620
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc37 (x y : ℝ) : 0 ≤ (1246501965850 * x ^ 2 + 2 * 496822876110 * x * y + 537161025002 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1246501965850 537161025002 496822876110
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc38 (x y : ℝ) : 0 ≤ (434606482500 * x ^ 2 + 2 * 144110577600 * x * y + 153232839840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 434606482500 153232839840 144110577600
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc39 (x y : ℝ) : 0 ≤ (124979975180 * x ^ 2 + 2 * 91037244330 * x * y + 85773208228 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 124979975180 85773208228 91037244330
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc40 (x y : ℝ) : 0 ≤ (364138717400 * x ^ 2 + 2 * 179606086830 * x * y + 180175149520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 364138717400 180175149520 179606086830
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc41 (x y : ℝ) : 0 ≤ (210441454290 * x ^ 2 + 2 * 79790093280 * x * y + 81685041804 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 210441454290 81685041804 79790093280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc42 (x y : ℝ) : 0 ≤ (34535039080 * x ^ 2 + 2 * 27884020410 * x * y + 24024832496 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 34535039080 24024832496 27884020410
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc43 (x y : ℝ) : 0 ≤ (52679027520 * x ^ 2 + 2 * 25311712320 * x * y + 23874369804 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 52679027520 23874369804 25311712320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc44 (x y : ℝ) : 0 ≤ (4509563160 * x ^ 2 + 2 * 3520992240 * x * y + 2849739891 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4509563160 2849739891 3520992240
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem A_OSC_entry11 (z w : ℝ) : 92160 * A11 (z + w) w 1 =
      17252710400 * ((1 - z - w) ^ 8) +
      158056814080 * (w * (1 - z - w) ^ 7) +
      479164067840 * (w ^ 2 * (1 - z - w) ^ 6) +
      715874263040 * (w ^ 3 * (1 - z - w) ^ 5) +
      621716700160 * (w ^ 4 * (1 - z - w) ^ 4) +
      359540042240 * (w ^ 5 * (1 - z - w) ^ 3) +
      155718743040 * (w ^ 6 * (1 - z - w) ^ 2) +
      46921236480 * (w ^ 7 * (1 - z - w)) +
      6540134400 * (w ^ 8) +
      115729146880 * (z * (1 - z - w) ^ 7) +
      868924433920 * (z * w * (1 - z - w) ^ 6) +
      2199990382080 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      2777259973120 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      2096990801920 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      1065675640320 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      352909432320 * (z * w ^ 6 * (1 - z - w)) +
      53759715840 * (z * w ^ 7) +
      317429568480 * (z ^ 2 * (1 - z - w) ^ 6) +
      2004721901600 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      4293146296480 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      4635392834400 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      2977183602080 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      1143655466560 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      196010735520 * (z ^ 2 * w ^ 6) +
      480178552960 * (z ^ 3 * (1 - z - w) ^ 5) +
      2603039483520 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      4741503929600 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      4260670908800 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      2038681949120 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      410625264960 * (z ^ 3 * w ^ 5) +
      454056140000 * (z ^ 4 * (1 - z - w) ^ 4) +
      2133392931580 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      3203939071020 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      2117912965930 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      534168603450 * (z ^ 4 * w ^ 4) +
      287785218300 * (z ^ 5 * (1 - z - w) ^ 3) +
      1135771302200 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      1246501965850 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      434606482500 * (z ^ 5 * w ^ 3) +
      124979975180 * (z ^ 6 * (1 - z - w) ^ 2) +
      364138717400 * (z ^ 6 * w * (1 - z - w)) +
      210441454290 * (z ^ 6 * w ^ 2) +
      34535039080 * (z ^ 7 * (1 - z - w)) +
      52679027520 * (z ^ 7 * w) +
      4509563160 * (z ^ 8) := by
  simp only [A11, P0, Pk, K1, K2, weight, kappa]
  ring

private theorem A_OSC_entry22 (z w : ℝ) : 92160 * A22 (z + w) w 1 =
      3450542080 * ((1 - z - w) ^ 8) +
      31611362816 * (w * (1 - z - w) ^ 7) +
      108962590720 * (w ^ 2 * (1 - z - w) ^ 6) +
      202056613888 * (w ^ 3 * (1 - z - w) ^ 5) +
      228817943552 * (w ^ 4 * (1 - z - w) ^ 4) +
      163584352768 * (w ^ 5 * (1 - z - w) ^ 3) +
      71196115968 * (w ^ 6 * (1 - z - w) ^ 2) +
      16728219648 * (w ^ 7 * (1 - z - w)) +
      1553356800 * (w ^ 8) +
      23145829376 * (z * (1 - z - w) ^ 7) +
      200044441088 * (z * w * (1 - z - w) ^ 6) +
      618105681408 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      981187455488 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      893889413120 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      469378856448 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      129556729344 * (z * w ^ 6 * (1 - z - w)) +
      14086900224 * (z * w ^ 7) +
      76615690848 * (z ^ 2 * (1 - z - w) ^ 6) +
      580514306464 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      1510341325856 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      1912483495776 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      1280348492704 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      430117149632 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      55809442464 * (z ^ 2 * w ^ 6) +
      156379793024 * (z ^ 3 * (1 - z - w) ^ 5) +
      964724061312 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      1974404593792 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      1830675210112 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      787479157024 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      125658517536 * (z ^ 3 * w ^ 5) +
      204476183392 * (z ^ 4 * (1 - z - w) ^ 4) +
      962254704716 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      1428624843972 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      851201225066 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      174955046445 * (z ^ 4 * w ^ 4) +
      169619374668 * (z ^ 5 * (1 - z - w) ^ 3) +
      565947886312 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      537161025002 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      153232839840 * (z ^ 5 * w ^ 3) +
      85773208228 * (z ^ 6 * (1 - z - w) ^ 2) +
      180175149520 * (z ^ 6 * w * (1 - z - w)) +
      81685041804 * (z ^ 6 * w ^ 2) +
      24024832496 * (z ^ 7 * (1 - z - w)) +
      23874369804 * (z ^ 7 * w) +
      2849739891 * (z ^ 8) := by
  simp only [A22, P0, Pk, Pl, K2, weight, kappa]
  ring

private theorem A_OSC_entry12 (z w : ℝ) : 92160 * A12 (z + w) w 1 =
      16412221440 * (w ^ 2 * (1 - z - w) ^ 6) +
      75585669120 * (w ^ 3 * (1 - z - w) ^ 5) +
      139843399680 * (w ^ 4 * (1 - z - w) ^ 4) +
      131761336320 * (w ^ 5 * (1 - z - w) ^ 3) +
      65896980480 * (w ^ 6 * (1 - z - w) ^ 2) +
      16428533760 * (w ^ 7 * (1 - z - w)) +
      1622937600 * (w ^ 8) +
      32824442880 * (z * w * (1 - z - w) ^ 6) +
      228584908800 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      569280360960 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      678715292160 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      413946155520 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      122889991680 * (z * w ^ 6 * (1 - z - w)) +
      14139233280 * (z * w ^ 7) +
      16412221440 * (z ^ 2 * (1 - z - w) ^ 6) +
      230412810240 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      870472316160 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      1402601150880 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      1087456210560 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      395407510560 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      54080723520 * (z ^ 2 * w ^ 6) +
      77413570560 * (z ^ 3 * (1 - z - w) ^ 5) +
      592477148160 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      1453216430880 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      1528657741440 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      709121944800 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      118617056640 * (z ^ 3 * w ^ 5) +
      151441793280 * (z ^ 4 * (1 - z - w) ^ 4) +
      754683896160 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      1212283815210 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      765276701850 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      163163833200 * (z ^ 4 * w ^ 4) +
      157114660320 * (z ^ 5 * (1 - z - w) ^ 3) +
      514070353620 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      496822876110 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      144110577600 * (z ^ 5 * w ^ 3) +
      91037244330 * (z ^ 6 * (1 - z - w) ^ 2) +
      179606086830 * (z ^ 6 * w * (1 - z - w)) +
      79790093280 * (z ^ 6 * w ^ 2) +
      27884020410 * (z ^ 7 * (1 - z - w)) +
      25311712320 * (z ^ 7 * w) +
      3520992240 * (z ^ 8) := by
  simp only [A12, P0, Pk, Pl, K12, weight]
  ring

private theorem A_OSC_entry11_list (z w : ℝ) :
    92160 * A11 (z + w) w 1 = ((A_OSC_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [A_OSC_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_OSC_entry11 z w

private theorem A_OSC_entry22_list (z w : ℝ) :
    92160 * A22 (z + w) w 1 = ((A_OSC_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [A_OSC_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_OSC_entry22 z w

private theorem A_OSC_entry12_list (z w : ℝ) :
    92160 * A12 (z + w) w 1 = ((A_OSC_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [A_OSC_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_OSC_entry12 z w

private theorem A_OSC {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ A11 (z + w) w 1 * x ^ 2 + 2 * A12 (z + w) w 1 * x * y + A22 (z + w) w 1 * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (A_OSC_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (A_OSC_hc0 x y) (by positivity),
      mul_nonneg (A_OSC_hc1 x y) (by positivity),
      mul_nonneg (A_OSC_hc2 x y) (by positivity),
      mul_nonneg (A_OSC_hc3 x y) (by positivity),
      mul_nonneg (A_OSC_hc4 x y) (by positivity),
      mul_nonneg (A_OSC_hc5 x y) (by positivity),
      mul_nonneg (A_OSC_hc6 x y) (by positivity),
      mul_nonneg (A_OSC_hc7 x y) (by positivity),
      mul_nonneg (A_OSC_hc8 x y) (by positivity),
      mul_nonneg (A_OSC_hc9 x y) (by positivity),
      mul_nonneg (A_OSC_hc10 x y) (by positivity),
      mul_nonneg (A_OSC_hc11 x y) (by positivity),
      mul_nonneg (A_OSC_hc12 x y) (by positivity),
      mul_nonneg (A_OSC_hc13 x y) (by positivity),
      mul_nonneg (A_OSC_hc14 x y) (by positivity),
      mul_nonneg (A_OSC_hc15 x y) (by positivity),
      mul_nonneg (A_OSC_hc16 x y) (by positivity),
      mul_nonneg (A_OSC_hc17 x y) (by positivity),
      mul_nonneg (A_OSC_hc18 x y) (by positivity),
      mul_nonneg (A_OSC_hc19 x y) (by positivity),
      mul_nonneg (A_OSC_hc20 x y) (by positivity),
      mul_nonneg (A_OSC_hc21 x y) (by positivity),
      mul_nonneg (A_OSC_hc22 x y) (by positivity),
      mul_nonneg (A_OSC_hc23 x y) (by positivity),
      mul_nonneg (A_OSC_hc24 x y) (by positivity),
      mul_nonneg (A_OSC_hc25 x y) (by positivity),
      mul_nonneg (A_OSC_hc26 x y) (by positivity),
      mul_nonneg (A_OSC_hc27 x y) (by positivity),
      mul_nonneg (A_OSC_hc28 x y) (by positivity),
      mul_nonneg (A_OSC_hc29 x y) (by positivity),
      mul_nonneg (A_OSC_hc30 x y) (by positivity),
      mul_nonneg (A_OSC_hc31 x y) (by positivity),
      mul_nonneg (A_OSC_hc32 x y) (by positivity),
      mul_nonneg (A_OSC_hc33 x y) (by positivity),
      mul_nonneg (A_OSC_hc34 x y) (by positivity),
      mul_nonneg (A_OSC_hc35 x y) (by positivity),
      mul_nonneg (A_OSC_hc36 x y) (by positivity),
      mul_nonneg (A_OSC_hc37 x y) (by positivity),
      mul_nonneg (A_OSC_hc38 x y) (by positivity),
      mul_nonneg (A_OSC_hc39 x y) (by positivity),
      mul_nonneg (A_OSC_hc40 x y) (by positivity),
      mul_nonneg (A_OSC_hc41 x y) (by positivity),
      mul_nonneg (A_OSC_hc42 x y) (by positivity),
      mul_nonneg (A_OSC_hc43 x y) (by positivity),
      mul_nonneg (A_OSC_hc44 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (A_OSC_data z w) x y hcoeff
  rw [← A_OSC_entry11_list, ← A_OSC_entry12_list, ← A_OSC_entry22_list] at hpos
  nlinarith only [hpos]

private theorem A_OCW_hc0 (x y : ℝ) : 0 ≤ (1078294400 * x ^ 2 + 2 * 0 * x * y + 215658880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1078294400 215658880 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc1 (x y : ℝ) : 0 ≤ (13917313600 * x ^ 2 + 2 * 0 * x * y + 2783462720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 13917313600 2783462720 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc2 (x y : ℝ) : 0 ≤ (49146252600 * x ^ 2 + 2 * 0 * x * y + 9829250520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 49146252600 9829250520 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc3 (x y : ℝ) : 0 ≤ (83212031200 * x ^ 2 + 2 * 0 * x * y + 16642406240 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 83212031200 16642406240 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc4 (x y : ℝ) : 0 ≤ (79111415000 * x ^ 2 + 2 * 0 * x * y + 15822283000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 79111415000 15822283000 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc5 (x y : ℝ) : 0 ≤ (44620627200 * x ^ 2 + 2 * 0 * x * y + 8924125440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 44620627200 8924125440 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc6 (x y : ℝ) : 0 ≤ (15005417000 * x ^ 2 + 2 * 0 * x * y + 3001083400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 15005417000 3001083400 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc7 (x y : ℝ) : 0 ≤ (2617132000 * x ^ 2 + 2 * 0 * x * y + 523426400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2617132000 523426400 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc8 (x y : ℝ) : 0 ≤ (25725000 * x ^ 2 + 2 * 0 * x * y + 5145000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 25725000 5145000 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc9 (x y : ℝ) : 0 ≤ (9878550880 * x ^ 2 + 2 * 0 * x * y + 1975710176 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 9878550880 1975710176 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc10 (x y : ℝ) : 0 ≤ (80325318880 * x ^ 2 + 2 * 0 * x * y + 16065063776 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 80325318880 16065063776 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc11 (x y : ℝ) : 0 ≤ (212593326440 * x ^ 2 + 2 * 0 * x * y + 42518665288 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 212593326440 42518665288 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc12 (x y : ℝ) : 0 ≤ (273006125160 * x ^ 2 + 2 * 0 * x * y + 54601225032 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 273006125160 54601225032 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc13 (x y : ℝ) : 0 ≤ (193148912140 * x ^ 2 + 2 * 0 * x * y + 38629782428 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 193148912140 38629782428 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc14 (x y : ℝ) : 0 ≤ (79438591940 * x ^ 2 + 2 * 0 * x * y + 15887718388 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 79438591940 15887718388 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc15 (x y : ℝ) : 0 ≤ (18951498020 * x ^ 2 + 2 * 0 * x * y + 3790299604 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 18951498020 3790299604 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc16 (x y : ℝ) : 0 ≤ (1802251500 * x ^ 2 + 2 * 0 * x * y + 360450300 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1802251500 360450300 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc17 (x y : ℝ) : 0 ≤ (29947754240 * x ^ 2 + 2 * 1025763840 * x * y + 6810161920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 29947754240 6810161920 1025763840
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc18 (x y : ℝ) : 0 ≤ (173140576320 * x ^ 2 + 2 * 5926095360 * x * y + 39368991552 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 173140576320 39368991552 5926095360
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc19 (x y : ℝ) : 0 ≤ (339403212520 * x ^ 2 + 2 * 14666927040 * x * y + 79614184136 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 339403212520 79614184136 14666927040
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc20 (x y : ℝ) : 0 ≤ (314227263920 * x ^ 2 + 2 * 19876347360 * x * y + 78746530672 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 314227263920 78746530672 19876347360
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc21 (x y : ℝ) : 0 ≤ (152504665740 * x ^ 2 + 2 * 15542982090 * x * y + 42935318820 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 152504665740 42935318820 15542982090
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc22 (x y : ℝ) : 0 ≤ (40732801840 * x ^ 2 + 2 * 6648736500 * x * y + 13465549568 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 40732801840 13465549568 6648736500
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc23 (x y : ℝ) : 0 ≤ (5091974580 * x ^ 2 + 2 * 1215506250 * x * y + 1990799916 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 5091974580 1990799916 1215506250
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc24 (x y : ℝ) : 0 ≤ (44742141440 * x ^ 2 + 2 * 4724104320 * x * y + 12628538368 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 44742141440 12628538368 4724104320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc25 (x y : ℝ) : 0 ≤ (187411560640 * x ^ 2 + 2 * 22382176320 * x * y + 54903231680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 187411560640 54903231680 22382176320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc26 (x y : ℝ) : 0 ≤ (262932340440 * x ^ 2 + 2 * 43625998440 * x * y + 86519885784 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 262932340440 86519885784 43625998440
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc27 (x y : ℝ) : 0 ≤ (164590050440 * x ^ 2 + 2 * 43648558200 * x * y + 66851908744 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 164590050440 66851908744 43648558200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc28 (x y : ℝ) : 0 ≤ (50113080370 * x ^ 2 + 2 * 22390181010 * x * y + 27423589106 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 50113080370 27423589106 22390181010
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc29 (x y : ℝ) : 0 ≤ (7160879370 * x ^ 2 + 2 * 4709549250 * x * y + 5091858474 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7160879370 5091858474 4709549250
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc30 (x y : ℝ) : 0 ≤ (38857293760 * x ^ 2 + 2 * 8740212480 * x * y + 14301121472 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 38857293760 14301121472 8740212480
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc31 (x y : ℝ) : 0 ≤ (118017851200 * x ^ 2 + 2 * 32472273600 * x * y + 47708529728 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 118017851200 47708529728 32472273600
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc32 (x y : ℝ) : 0 ≤ (117056427560 * x ^ 2 + 2 * 46520580960 * x * y + 57667847848 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 117056427560 57667847848 46520580960
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc33 (x y : ℝ) : 0 ≤ (49587064400 * x ^ 2 + 2 * 30367398240 * x * y + 32036261728 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 49587064400 32036261728 30367398240
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc34 (x y : ℝ) : 0 ≤ (9113859330 * x ^ 2 + 2 * 7600748400 * x * y + 7273386021 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 9113859330 7273386021 7600748400
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc35 (x y : ℝ) : 0 ≤ (22471252640 * x ^ 2 + 2 * 8235083520 * x * y + 10224022048 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 22471252640 10224022048 8235083520
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc36 (x y : ℝ) : 0 ≤ (50993360160 * x ^ 2 + 2 * 22384716480 * x * y + 25396796064 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 50993360160 25396796064 22384716480
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc37 (x y : ℝ) : 0 ≤ (37459172080 * x ^ 2 + 2 * 20830874760 * x * y + 21138872528 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 37459172080 21138872528 20830874760
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc38 (x y : ℝ) : 0 ≤ (10303385520 * x ^ 2 + 2 * 6595187400 * x * y + 6146705184 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 10303385520 6146705184 6595187400
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc39 (x y : ℝ) : 0 ≤ (9732421440 * x ^ 2 + 2 * 4118561280 * x * y + 4449757248 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 9732421440 4449757248 4118561280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc40 (x y : ℝ) : 0 ≤ (16407245760 * x ^ 2 + 2 * 7250840640 * x * y + 7342115520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 16407245760 7342115520 7250840640
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc41 (x y : ℝ) : 0 ≤ (7378946280 * x ^ 2 + 2 * 3269365200 * x * y + 3066141096 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7378946280 3066141096 3269365200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc42 (x y : ℝ) : 0 ≤ (2932577280 * x ^ 2 + 2 * 1026783360 * x * y + 1045513728 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2932577280 1045513728 1026783360
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc43 (x y : ℝ) : 0 ≤ (2752747200 * x ^ 2 + 2 * 882316800 * x * y + 838008000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2752747200 838008000 882316800
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc44 (x y : ℝ) : 0 ≤ (408758400 * x ^ 2 + 2 * 101433600 * x * y + 97084800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 408758400 97084800 101433600
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem A_OCW_entry11 (z w : ℝ) : 5760 * A11 z (z + 2 * w) 1 =
      1078294400 * ((1 - z - w) ^ 8) +
      13917313600 * (w * (1 - z - w) ^ 7) +
      49146252600 * (w ^ 2 * (1 - z - w) ^ 6) +
      83212031200 * (w ^ 3 * (1 - z - w) ^ 5) +
      79111415000 * (w ^ 4 * (1 - z - w) ^ 4) +
      44620627200 * (w ^ 5 * (1 - z - w) ^ 3) +
      15005417000 * (w ^ 6 * (1 - z - w) ^ 2) +
      2617132000 * (w ^ 7 * (1 - z - w)) +
      25725000 * (w ^ 8) +
      9878550880 * (z * (1 - z - w) ^ 7) +
      80325318880 * (z * w * (1 - z - w) ^ 6) +
      212593326440 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      273006125160 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      193148912140 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      79438591940 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      18951498020 * (z * w ^ 6 * (1 - z - w)) +
      1802251500 * (z * w ^ 7) +
      29947754240 * (z ^ 2 * (1 - z - w) ^ 6) +
      173140576320 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      339403212520 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      314227263920 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      152504665740 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      40732801840 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      5091974580 * (z ^ 2 * w ^ 6) +
      44742141440 * (z ^ 3 * (1 - z - w) ^ 5) +
      187411560640 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      262932340440 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      164590050440 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      50113080370 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      7160879370 * (z ^ 3 * w ^ 5) +
      38857293760 * (z ^ 4 * (1 - z - w) ^ 4) +
      118017851200 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      117056427560 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      49587064400 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      9113859330 * (z ^ 4 * w ^ 4) +
      22471252640 * (z ^ 5 * (1 - z - w) ^ 3) +
      50993360160 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      37459172080 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      10303385520 * (z ^ 5 * w ^ 3) +
      9732421440 * (z ^ 6 * (1 - z - w) ^ 2) +
      16407245760 * (z ^ 6 * w * (1 - z - w)) +
      7378946280 * (z ^ 6 * w ^ 2) +
      2932577280 * (z ^ 7 * (1 - z - w)) +
      2752747200 * (z ^ 7 * w) +
      408758400 * (z ^ 8) := by
  simp only [A11, P0, Pk, K1, K2, weight, kappa]
  ring

private theorem A_OCW_entry22 (z w : ℝ) : 5760 * A22 z (z + 2 * w) 1 =
      215658880 * ((1 - z - w) ^ 8) +
      2783462720 * (w * (1 - z - w) ^ 7) +
      9829250520 * (w ^ 2 * (1 - z - w) ^ 6) +
      16642406240 * (w ^ 3 * (1 - z - w) ^ 5) +
      15822283000 * (w ^ 4 * (1 - z - w) ^ 4) +
      8924125440 * (w ^ 5 * (1 - z - w) ^ 3) +
      3001083400 * (w ^ 6 * (1 - z - w) ^ 2) +
      523426400 * (w ^ 7 * (1 - z - w)) +
      5145000 * (w ^ 8) +
      1975710176 * (z * (1 - z - w) ^ 7) +
      16065063776 * (z * w * (1 - z - w) ^ 6) +
      42518665288 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      54601225032 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      38629782428 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      15887718388 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      3790299604 * (z * w ^ 6 * (1 - z - w)) +
      360450300 * (z * w ^ 7) +
      6810161920 * (z ^ 2 * (1 - z - w) ^ 6) +
      39368991552 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      79614184136 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      78746530672 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      42935318820 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      13465549568 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      1990799916 * (z ^ 2 * w ^ 6) +
      12628538368 * (z ^ 3 * (1 - z - w) ^ 5) +
      54903231680 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      86519885784 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      66851908744 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      27423589106 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      5091858474 * (z ^ 3 * w ^ 5) +
      14301121472 * (z ^ 4 * (1 - z - w) ^ 4) +
      47708529728 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      57667847848 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      32036261728 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      7273386021 * (z ^ 4 * w ^ 4) +
      10224022048 * (z ^ 5 * (1 - z - w) ^ 3) +
      25396796064 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      21138872528 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      6146705184 * (z ^ 5 * w ^ 3) +
      4449757248 * (z ^ 6 * (1 - z - w) ^ 2) +
      7342115520 * (z ^ 6 * w * (1 - z - w)) +
      3066141096 * (z ^ 6 * w ^ 2) +
      1045513728 * (z ^ 7 * (1 - z - w)) +
      838008000 * (z ^ 7 * w) +
      97084800 * (z ^ 8) := by
  simp only [A22, P0, Pk, Pl, K2, weight, kappa]
  ring

private theorem A_OCW_entry12 (z w : ℝ) : 5760 * A12 z (z + 2 * w) 1 =
      1025763840 * (z ^ 2 * (1 - z - w) ^ 6) +
      5926095360 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      14666927040 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      19876347360 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      15542982090 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      6648736500 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      1215506250 * (z ^ 2 * w ^ 6) +
      4724104320 * (z ^ 3 * (1 - z - w) ^ 5) +
      22382176320 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      43625998440 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      43648558200 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      22390181010 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      4709549250 * (z ^ 3 * w ^ 5) +
      8740212480 * (z ^ 4 * (1 - z - w) ^ 4) +
      32472273600 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      46520580960 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      30367398240 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      7600748400 * (z ^ 4 * w ^ 4) +
      8235083520 * (z ^ 5 * (1 - z - w) ^ 3) +
      22384716480 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      20830874760 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      6595187400 * (z ^ 5 * w ^ 3) +
      4118561280 * (z ^ 6 * (1 - z - w) ^ 2) +
      7250840640 * (z ^ 6 * w * (1 - z - w)) +
      3269365200 * (z ^ 6 * w ^ 2) +
      1026783360 * (z ^ 7 * (1 - z - w)) +
      882316800 * (z ^ 7 * w) +
      101433600 * (z ^ 8) := by
  simp only [A12, P0, Pk, Pl, K12, weight]
  ring

private theorem A_OCW_entry11_list (z w : ℝ) :
    5760 * A11 z (z + 2 * w) 1 = ((A_OCW_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [A_OCW_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_OCW_entry11 z w

private theorem A_OCW_entry22_list (z w : ℝ) :
    5760 * A22 z (z + 2 * w) 1 = ((A_OCW_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [A_OCW_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_OCW_entry22 z w

private theorem A_OCW_entry12_list (z w : ℝ) :
    5760 * A12 z (z + 2 * w) 1 = ((A_OCW_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [A_OCW_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_OCW_entry12 z w

private theorem A_OCW {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ A11 z (z + 2 * w) 1 * x ^ 2 + 2 * A12 z (z + 2 * w) 1 * x * y + A22 z (z + 2 * w) 1 * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (A_OCW_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (A_OCW_hc0 x y) (by positivity),
      mul_nonneg (A_OCW_hc1 x y) (by positivity),
      mul_nonneg (A_OCW_hc2 x y) (by positivity),
      mul_nonneg (A_OCW_hc3 x y) (by positivity),
      mul_nonneg (A_OCW_hc4 x y) (by positivity),
      mul_nonneg (A_OCW_hc5 x y) (by positivity),
      mul_nonneg (A_OCW_hc6 x y) (by positivity),
      mul_nonneg (A_OCW_hc7 x y) (by positivity),
      mul_nonneg (A_OCW_hc8 x y) (by positivity),
      mul_nonneg (A_OCW_hc9 x y) (by positivity),
      mul_nonneg (A_OCW_hc10 x y) (by positivity),
      mul_nonneg (A_OCW_hc11 x y) (by positivity),
      mul_nonneg (A_OCW_hc12 x y) (by positivity),
      mul_nonneg (A_OCW_hc13 x y) (by positivity),
      mul_nonneg (A_OCW_hc14 x y) (by positivity),
      mul_nonneg (A_OCW_hc15 x y) (by positivity),
      mul_nonneg (A_OCW_hc16 x y) (by positivity),
      mul_nonneg (A_OCW_hc17 x y) (by positivity),
      mul_nonneg (A_OCW_hc18 x y) (by positivity),
      mul_nonneg (A_OCW_hc19 x y) (by positivity),
      mul_nonneg (A_OCW_hc20 x y) (by positivity),
      mul_nonneg (A_OCW_hc21 x y) (by positivity),
      mul_nonneg (A_OCW_hc22 x y) (by positivity),
      mul_nonneg (A_OCW_hc23 x y) (by positivity),
      mul_nonneg (A_OCW_hc24 x y) (by positivity),
      mul_nonneg (A_OCW_hc25 x y) (by positivity),
      mul_nonneg (A_OCW_hc26 x y) (by positivity),
      mul_nonneg (A_OCW_hc27 x y) (by positivity),
      mul_nonneg (A_OCW_hc28 x y) (by positivity),
      mul_nonneg (A_OCW_hc29 x y) (by positivity),
      mul_nonneg (A_OCW_hc30 x y) (by positivity),
      mul_nonneg (A_OCW_hc31 x y) (by positivity),
      mul_nonneg (A_OCW_hc32 x y) (by positivity),
      mul_nonneg (A_OCW_hc33 x y) (by positivity),
      mul_nonneg (A_OCW_hc34 x y) (by positivity),
      mul_nonneg (A_OCW_hc35 x y) (by positivity),
      mul_nonneg (A_OCW_hc36 x y) (by positivity),
      mul_nonneg (A_OCW_hc37 x y) (by positivity),
      mul_nonneg (A_OCW_hc38 x y) (by positivity),
      mul_nonneg (A_OCW_hc39 x y) (by positivity),
      mul_nonneg (A_OCW_hc40 x y) (by positivity),
      mul_nonneg (A_OCW_hc41 x y) (by positivity),
      mul_nonneg (A_OCW_hc42 x y) (by positivity),
      mul_nonneg (A_OCW_hc43 x y) (by positivity),
      mul_nonneg (A_OCW_hc44 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (A_OCW_data z w) x y hcoeff
  rw [← A_OCW_entry11_list, ← A_OCW_entry12_list, ← A_OCW_entry22_list] at hpos
  nlinarith only [hpos]

private theorem A_SCU_hc0 (x y : ℝ) : 0 ≤ (4509563160 * x ^ 2 + 2 * 3520992240 * x * y + 2849739891 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4509563160 2849739891 3520992240
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc1 (x y : ℝ) : 0 ≤ (37617971480 * x ^ 2 + 2 * 28451855430 * x * y + 21571005760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 37617971480 21571005760 28451855430
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc2 (x y : ℝ) : 0 ≤ (146560501980 * x ^ 2 + 2 * 95012089470 * x * y + 68596421076 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 146560501980 68596421076 95012089470
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc3 (x y : ℝ) : 0 ≤ (331315496820 * x ^ 2 + 2 * 170479080720 * x * y + 118256665572 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 331315496820 118256665572 170479080720
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc4 (x y : ℝ) : 0 ≤ (455902264600 * x ^ 2 + 2 * 178515443880 * x * y + 119430509432 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 455902264600 119430509432 178515443880
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc5 (x y : ℝ) : 0 ≤ (379173161760 * x ^ 2 + 2 * 110060120160 * x * y + 71195690784 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 379173161760 71195690784 110060120160
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc6 (x y : ℝ) : 0 ≤ (179673110880 * x ^ 2 + 2 * 37856028960 * x * y + 23831782752 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 179673110880 23831782752 37856028960
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc7 (x y : ℝ) : 0 ≤ (41075910080 * x ^ 2 + 2 * 6256419840 * x * y + 3911982784 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 41075910080 3911982784 6256419840
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc8 (x y : ℝ) : 0 ≤ (2537099520 * x ^ 2 + 2 * 342921600 * x * y + 222426624 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2537099520 222426624 342921600
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc9 (x y : ℝ) : 0 ≤ (52679027520 * x ^ 2 + 2 * 25311712320 * x * y + 23874369804 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 52679027520 23874369804 25311712320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc10 (x y : ℝ) : 0 ≤ (373367667880 * x ^ 2 + 2 * 174757885650 * x * y + 154066027736 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 373367667880 154066027736 174757885650
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc11 (x y : ℝ) : 0 ≤ (1191145005080 * x ^ 2 + 2 * 484981146540 * x * y + 409293155608 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1191145005080 409293155608 484981146540
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc12 (x y : ℝ) : 0 ≤ (2126124752020 * x ^ 2 + 2 * 696933879840 * x * y + 571538732324 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2126124752020 571538732324 696933879840
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc13 (x y : ℝ) : 0 ≤ (2204808746080 * x ^ 2 + 2 * 555405130080 * x * y + 446225043104 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2204808746080 446225043104 555405130080
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc14 (x y : ℝ) : 0 ≤ (1280803135040 * x ^ 2 + 2 * 241674700320 * x * y + 191088676672 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1280803135040 191088676672 241674700320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc15 (x y : ℝ) : 0 ≤ (365211583360 * x ^ 2 + 2 * 51921040320 * x * y + 40445269376 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 365211583360 40445269376 51921040320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc16 (x y : ℝ) : 0 ≤ (33652689600 * x ^ 2 + 2 * 4233427200 * x * y + 3179636160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 33652689600 3179636160 4233427200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc17 (x y : ℝ) : 0 ≤ (210441454290 * x ^ 2 + 2 * 79790093280 * x * y + 81685041804 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 210441454290 81685041804 79790093280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc18 (x y : ℝ) : 0 ≤ (1278795485630 * x ^ 2 + 2 * 460658243250 * x * y + 443059476646 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1278795485630 443059476646 460658243250
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc19 (x y : ℝ) : 0 ≤ (3365406669920 * x ^ 2 + 2 * 1031460650910 * x * y + 958117102192 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3365406669920 958117102192 1031460650910
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc20 (x y : ℝ) : 0 ≤ (4700562690960 * x ^ 2 + 2 * 1138553971200 * x * y + 1037759846544 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4700562690960 1037759846544 1138553971200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc21 (x y : ℝ) : 0 ≤ (3524452184960 * x ^ 2 + 2 * 649777594320 * x * y + 582438051232 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3524452184960 582438051232 649777594320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc22 (x y : ℝ) : 0 ≤ (1285199876960 * x ^ 2 + 2 * 181657092960 * x * y + 157045529824 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1285199876960 157045529824 181657092960
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc23 (x y : ℝ) : 0 ≤ (162952356480 * x ^ 2 + 2 * 20175199200 * x * y + 15567159936 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 162952356480 15567159936 20175199200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc24 (x y : ℝ) : 0 ≤ (434606482500 * x ^ 2 + 2 * 144110577600 * x * y + 153232839840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 434606482500 153232839840 144110577600
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc25 (x y : ℝ) : 0 ≤ (2228151859070 * x ^ 2 + 2 * 675829074150 * x * y + 681127173334 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2228151859070 681127173334 675829074150
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc26 (x y : ℝ) : 0 ≤ (4701626481360 * x ^ 2 + 2 * 1170867230640 * x * y + 1150379003184 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4701626481360 1150379003184 1170867230640
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc27 (x y : ℝ) : 0 ≤ (4867240036080 * x ^ 2 + 2 * 931550661360 * x * y + 901365550512 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4867240036080 901365550512 931550661360
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc28 (x y : ℝ) : 0 ≤ (2359043231360 * x ^ 2 + 2 * 342760403520 * x * y + 319543978816 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2359043231360 319543978816 342760403520
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc29 (x y : ℝ) : 0 ≤ (403241601120 * x ^ 2 + 2 * 48943634400 * x * y + 40017268704 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 403241601120 40017268704 48943634400
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc30 (x y : ℝ) : 0 ≤ (534168603450 * x ^ 2 + 2 * 163163833200 * x * y + 174955046445 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 534168603450 174955046445 163163833200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc31 (x y : ℝ) : 0 ≤ (2234666878480 * x ^ 2 + 2 * 596188720800 * x * y + 612161214536 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2234666878480 612161214536 596188720800
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc32 (x y : ℝ) : 0 ≤ (3565138390160 * x ^ 2 + 2 * 748656538560 * x * y + 754394665240 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3565138390160 754394665240 748656538560
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc33 (x y : ℝ) : 0 ≤ (2440955527360 * x ^ 2 + 2 * 382888874880 * x * y + 376316159648 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2440955527360 376316159648 382888874880
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc34 (x y : ℝ) : 0 ≤ (573711566880 * x ^ 2 + 2 * 69883430400 * x * y + 61880575056 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 573711566880 61880575056 69883430400
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc35 (x y : ℝ) : 0 ≤ (410625264960 * x ^ 2 + 2 * 118617056640 * x * y + 125658517536 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 410625264960 125658517536 118617056640
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc36 (x y : ℝ) : 0 ≤ (1320096123200 * x ^ 2 + 2 * 316294829280 * x * y + 323833955584 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1320096123200 323833955584 316294829280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc37 (x y : ℝ) : 0 ≤ (1418556953600 * x ^ 2 + 2 * 255720792960 * x * y + 256812468352 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1418556953600 256812468352 255720792960
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc38 (x y : ℝ) : 0 ≤ (482191491840 * x ^ 2 + 2 * 63437385600 * x * y + 59972901888 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 482191491840 59972901888 63437385600
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc39 (x y : ℝ) : 0 ≤ (196010735520 * x ^ 2 + 2 * 54080723520 * x * y + 55809442464 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 196010735520 55809442464 54080723520
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc40 (x y : ℝ) : 0 ≤ (431133509760 * x ^ 2 + 2 * 93432902400 * x * y + 93681040512 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 431133509760 93681040512 93432902400
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc41 (x y : ℝ) : 0 ≤ (233942820480 * x ^ 2 + 2 * 36439891200 * x * y + 35320427136 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 233942820480 35320427136 36439891200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc42 (x y : ℝ) : 0 ≤ (53759715840 * x ^ 2 + 2 * 14139233280 * x * y + 14086900224 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 53759715840 14086900224 14139233280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc43 (x y : ℝ) : 0 ≤ (60598195200 * x ^ 2 + 2 * 11849932800 * x * y + 11445580800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 60598195200 11445580800 11849932800
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc44 (x y : ℝ) : 0 ≤ (6540134400 * x ^ 2 + 2 * 1622937600 * x * y + 1553356800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6540134400 1553356800 1622937600
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem A_SCU_entry11 (z w : ℝ) : 92160 * A11 (1 + w) z 1 =
      4509563160 * ((1 - z - w) ^ 8) +
      37617971480 * (w * (1 - z - w) ^ 7) +
      146560501980 * (w ^ 2 * (1 - z - w) ^ 6) +
      331315496820 * (w ^ 3 * (1 - z - w) ^ 5) +
      455902264600 * (w ^ 4 * (1 - z - w) ^ 4) +
      379173161760 * (w ^ 5 * (1 - z - w) ^ 3) +
      179673110880 * (w ^ 6 * (1 - z - w) ^ 2) +
      41075910080 * (w ^ 7 * (1 - z - w)) +
      2537099520 * (w ^ 8) +
      52679027520 * (z * (1 - z - w) ^ 7) +
      373367667880 * (z * w * (1 - z - w) ^ 6) +
      1191145005080 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      2126124752020 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      2204808746080 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      1280803135040 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      365211583360 * (z * w ^ 6 * (1 - z - w)) +
      33652689600 * (z * w ^ 7) +
      210441454290 * (z ^ 2 * (1 - z - w) ^ 6) +
      1278795485630 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      3365406669920 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      4700562690960 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      3524452184960 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      1285199876960 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      162952356480 * (z ^ 2 * w ^ 6) +
      434606482500 * (z ^ 3 * (1 - z - w) ^ 5) +
      2228151859070 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      4701626481360 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      4867240036080 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      2359043231360 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      403241601120 * (z ^ 3 * w ^ 5) +
      534168603450 * (z ^ 4 * (1 - z - w) ^ 4) +
      2234666878480 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      3565138390160 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      2440955527360 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      573711566880 * (z ^ 4 * w ^ 4) +
      410625264960 * (z ^ 5 * (1 - z - w) ^ 3) +
      1320096123200 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      1418556953600 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      482191491840 * (z ^ 5 * w ^ 3) +
      196010735520 * (z ^ 6 * (1 - z - w) ^ 2) +
      431133509760 * (z ^ 6 * w * (1 - z - w)) +
      233942820480 * (z ^ 6 * w ^ 2) +
      53759715840 * (z ^ 7 * (1 - z - w)) +
      60598195200 * (z ^ 7 * w) +
      6540134400 * (z ^ 8) := by
  simp only [A11, P0, Pk, K1, K2, weight, kappa]
  ring

private theorem A_SCU_entry22 (z w : ℝ) : 92160 * A22 (1 + w) z 1 =
      2849739891 * ((1 - z - w) ^ 8) +
      21571005760 * (w * (1 - z - w) ^ 7) +
      68596421076 * (w ^ 2 * (1 - z - w) ^ 6) +
      118256665572 * (w ^ 3 * (1 - z - w) ^ 5) +
      119430509432 * (w ^ 4 * (1 - z - w) ^ 4) +
      71195690784 * (w ^ 5 * (1 - z - w) ^ 3) +
      23831782752 * (w ^ 6 * (1 - z - w) ^ 2) +
      3911982784 * (w ^ 7 * (1 - z - w)) +
      222426624 * (w ^ 8) +
      23874369804 * (z * (1 - z - w) ^ 7) +
      154066027736 * (z * w * (1 - z - w) ^ 6) +
      409293155608 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      571538732324 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      446225043104 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      191088676672 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      40445269376 * (z * w ^ 6 * (1 - z - w)) +
      3179636160 * (z * w ^ 7) +
      81685041804 * (z ^ 2 * (1 - z - w) ^ 6) +
      443059476646 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      958117102192 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      1037759846544 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      582438051232 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      157045529824 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      15567159936 * (z ^ 2 * w ^ 6) +
      153232839840 * (z ^ 3 * (1 - z - w) ^ 5) +
      681127173334 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      1150379003184 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      901365550512 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      319543978816 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      40017268704 * (z ^ 3 * w ^ 5) +
      174955046445 * (z ^ 4 * (1 - z - w) ^ 4) +
      612161214536 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      754394665240 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      376316159648 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      61880575056 * (z ^ 4 * w ^ 4) +
      125658517536 * (z ^ 5 * (1 - z - w) ^ 3) +
      323833955584 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      256812468352 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      59972901888 * (z ^ 5 * w ^ 3) +
      55809442464 * (z ^ 6 * (1 - z - w) ^ 2) +
      93681040512 * (z ^ 6 * w * (1 - z - w)) +
      35320427136 * (z ^ 6 * w ^ 2) +
      14086900224 * (z ^ 7 * (1 - z - w)) +
      11445580800 * (z ^ 7 * w) +
      1553356800 * (z ^ 8) := by
  simp only [A22, P0, Pk, Pl, K2, weight, kappa]
  ring

private theorem A_SCU_entry12 (z w : ℝ) : 92160 * A12 (1 + w) z 1 =
      3520992240 * ((1 - z - w) ^ 8) +
      28451855430 * (w * (1 - z - w) ^ 7) +
      95012089470 * (w ^ 2 * (1 - z - w) ^ 6) +
      170479080720 * (w ^ 3 * (1 - z - w) ^ 5) +
      178515443880 * (w ^ 4 * (1 - z - w) ^ 4) +
      110060120160 * (w ^ 5 * (1 - z - w) ^ 3) +
      37856028960 * (w ^ 6 * (1 - z - w) ^ 2) +
      6256419840 * (w ^ 7 * (1 - z - w)) +
      342921600 * (w ^ 8) +
      25311712320 * (z * (1 - z - w) ^ 7) +
      174757885650 * (z * w * (1 - z - w) ^ 6) +
      484981146540 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      696933879840 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      555405130080 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      241674700320 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      51921040320 * (z * w ^ 6 * (1 - z - w)) +
      4233427200 * (z * w ^ 7) +
      79790093280 * (z ^ 2 * (1 - z - w) ^ 6) +
      460658243250 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      1031460650910 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      1138553971200 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      649777594320 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      181657092960 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      20175199200 * (z ^ 2 * w ^ 6) +
      144110577600 * (z ^ 3 * (1 - z - w) ^ 5) +
      675829074150 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      1170867230640 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      931550661360 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      342760403520 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      48943634400 * (z ^ 3 * w ^ 5) +
      163163833200 * (z ^ 4 * (1 - z - w) ^ 4) +
      596188720800 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      748656538560 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      382888874880 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      69883430400 * (z ^ 4 * w ^ 4) +
      118617056640 * (z ^ 5 * (1 - z - w) ^ 3) +
      316294829280 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      255720792960 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      63437385600 * (z ^ 5 * w ^ 3) +
      54080723520 * (z ^ 6 * (1 - z - w) ^ 2) +
      93432902400 * (z ^ 6 * w * (1 - z - w)) +
      36439891200 * (z ^ 6 * w ^ 2) +
      14139233280 * (z ^ 7 * (1 - z - w)) +
      11849932800 * (z ^ 7 * w) +
      1622937600 * (z ^ 8) := by
  simp only [A12, P0, Pk, Pl, K12, weight]
  ring

private theorem A_SCU_entry11_list (z w : ℝ) :
    92160 * A11 (1 + w) z 1 = ((A_SCU_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [A_SCU_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_SCU_entry11 z w

private theorem A_SCU_entry22_list (z w : ℝ) :
    92160 * A22 (1 + w) z 1 = ((A_SCU_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [A_SCU_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_SCU_entry22 z w

private theorem A_SCU_entry12_list (z w : ℝ) :
    92160 * A12 (1 + w) z 1 = ((A_SCU_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [A_SCU_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_SCU_entry12 z w

private theorem A_SCU {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ A11 (1 + w) z 1 * x ^ 2 + 2 * A12 (1 + w) z 1 * x * y + A22 (1 + w) z 1 * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (A_SCU_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (A_SCU_hc0 x y) (by positivity),
      mul_nonneg (A_SCU_hc1 x y) (by positivity),
      mul_nonneg (A_SCU_hc2 x y) (by positivity),
      mul_nonneg (A_SCU_hc3 x y) (by positivity),
      mul_nonneg (A_SCU_hc4 x y) (by positivity),
      mul_nonneg (A_SCU_hc5 x y) (by positivity),
      mul_nonneg (A_SCU_hc6 x y) (by positivity),
      mul_nonneg (A_SCU_hc7 x y) (by positivity),
      mul_nonneg (A_SCU_hc8 x y) (by positivity),
      mul_nonneg (A_SCU_hc9 x y) (by positivity),
      mul_nonneg (A_SCU_hc10 x y) (by positivity),
      mul_nonneg (A_SCU_hc11 x y) (by positivity),
      mul_nonneg (A_SCU_hc12 x y) (by positivity),
      mul_nonneg (A_SCU_hc13 x y) (by positivity),
      mul_nonneg (A_SCU_hc14 x y) (by positivity),
      mul_nonneg (A_SCU_hc15 x y) (by positivity),
      mul_nonneg (A_SCU_hc16 x y) (by positivity),
      mul_nonneg (A_SCU_hc17 x y) (by positivity),
      mul_nonneg (A_SCU_hc18 x y) (by positivity),
      mul_nonneg (A_SCU_hc19 x y) (by positivity),
      mul_nonneg (A_SCU_hc20 x y) (by positivity),
      mul_nonneg (A_SCU_hc21 x y) (by positivity),
      mul_nonneg (A_SCU_hc22 x y) (by positivity),
      mul_nonneg (A_SCU_hc23 x y) (by positivity),
      mul_nonneg (A_SCU_hc24 x y) (by positivity),
      mul_nonneg (A_SCU_hc25 x y) (by positivity),
      mul_nonneg (A_SCU_hc26 x y) (by positivity),
      mul_nonneg (A_SCU_hc27 x y) (by positivity),
      mul_nonneg (A_SCU_hc28 x y) (by positivity),
      mul_nonneg (A_SCU_hc29 x y) (by positivity),
      mul_nonneg (A_SCU_hc30 x y) (by positivity),
      mul_nonneg (A_SCU_hc31 x y) (by positivity),
      mul_nonneg (A_SCU_hc32 x y) (by positivity),
      mul_nonneg (A_SCU_hc33 x y) (by positivity),
      mul_nonneg (A_SCU_hc34 x y) (by positivity),
      mul_nonneg (A_SCU_hc35 x y) (by positivity),
      mul_nonneg (A_SCU_hc36 x y) (by positivity),
      mul_nonneg (A_SCU_hc37 x y) (by positivity),
      mul_nonneg (A_SCU_hc38 x y) (by positivity),
      mul_nonneg (A_SCU_hc39 x y) (by positivity),
      mul_nonneg (A_SCU_hc40 x y) (by positivity),
      mul_nonneg (A_SCU_hc41 x y) (by positivity),
      mul_nonneg (A_SCU_hc42 x y) (by positivity),
      mul_nonneg (A_SCU_hc43 x y) (by positivity),
      mul_nonneg (A_SCU_hc44 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (A_SCU_data z w) x y hcoeff
  rw [← A_SCU_entry11_list, ← A_SCU_entry12_list, ← A_SCU_entry22_list] at hpos
  nlinarith only [hpos]

/-- Equation (21) at the axial spectral value, on the whole closed triangle.
The proof checks the three finite triangle expansions above. -/
theorem axial_matrix_nonneg_oai {v b : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2) (x y : ℝ) :
    0 ≤ A11 v b 1 * x ^ 2 + 2 * A12 v b 1 * x * y + A22 v b 1 * y ^ 2 := by
  by_cases horder : b ≤ v
  · by_cases hv1 : v ≤ 1
    · have h := A_OSC (z := v - b) (w := b) (by linarith) hb (by linarith) x y
      simpa only [sub_add_cancel] using h
    · have h := A_SCU (z := b) (w := v - 1) hb (by linarith) (by linarith) x y
      simpa only [show 1 + (v - 1) = v by ring] using h
  · have h := A_OCW (z := v) (w := (b - v) / 2) hv (by linarith) (by linarith) x y
    simpa only [show v + 2 * ((b - v) / 2) = b by ring] using h

end

end PositiveEinsteinFour.Quadratic
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Quadratic.axial_matrix_nonneg_oai := @OAI.PositiveEinsteinFour.Quadratic.axial_matrix_nonneg_oai
