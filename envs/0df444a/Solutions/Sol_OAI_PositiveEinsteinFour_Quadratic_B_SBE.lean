-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Quadratic.B_SBE
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:24:45.060052+00:00
-- url     : https://prove2.me/submissions/02cb5bfe-7846-40fd-bef8-1a9784299030

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

private theorem B_SBE_hc0 (x y : ℝ) : 0 ≤ (801184320 * x ^ 2 + 2 * (-411481728) * x * y + 268058655 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 801184320 268058655 (-411481728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc1 (x y : ℝ) : 0 ≤ (7761549600 * x ^ 2 + 2 * (-3632190912) * x * y + 2156641245 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7761549600 2156641245 (-3632190912)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc2 (x y : ℝ) : 0 ≤ (33545378390 * x ^ 2 + 2 * (-14568520482) * x * y + 8016883685 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 33545378390 8016883685 (-14568520482)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc3 (x y : ℝ) : 0 ≤ (84189484865 * x ^ 2 + 2 * (-34684787694) * x * y + 18306466615 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 84189484865 18306466615 (-34684787694)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc4 (x y : ℝ) : 0 ≤ (133900348280 * x ^ 2 + 2 * (-53475840324) * x * y + 28360530540 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 133900348280 28360530540 (-53475840324)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc5 (x y : ℝ) : 0 ≤ (138250280160 * x ^ 2 + 2 * (-54534308550) * x * y + 30580181140 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 138250280160 30580181140 (-54534308550)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc6 (x y : ℝ) : 0 ≤ (91017819400 * x ^ 2 + 2 * (-36001603866) * x * y + 22502066300 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 91017819400 22502066300 (-36001603866)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc7 (x y : ℝ) : 0 ≤ (35683155740 * x ^ 2 + 2 * (-14336038872) * x * y + 10652132340 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 35683155740 10652132340 (-14336038872)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc8 (x y : ℝ) : 0 ≤ (7013055760 * x ^ 2 + 2 * (-2908573260) * x * y + 2877353600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7013055760 2877353600 (-2908573260)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc9 (x y : ℝ) : 0 ≤ (393346160 * x ^ 2 + 2 * (-178693632) * x * y + 329471440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 393346160 329471440 (-178693632)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc10 (x y : ℝ) : 0 ≤ (8214628800 * x ^ 2 + 2 * (-4609025856) * x * y + 3173049120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 8214628800 3173049120 (-4609025856)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc11 (x y : ℝ) : 0 ≤ (70787466560 * x ^ 2 + 2 * (-36412750944) * x * y + 23133767660 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 70787466560 23133767660 (-36412750944)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc12 (x y : ℝ) : 0 ≤ (268395571630 * x ^ 2 + 2 * (-127897332726) * x * y + 75410056960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 268395571630 75410056960 (-127897332726)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc13 (x y : ℝ) : 0 ≤ (581299100260 * x ^ 2 + 2 * (-260302314732) * x * y + 144758679180 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 581299100260 144758679180 (-260302314732)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc14 (x y : ℝ) : 0 ≤ (781243281480 * x ^ 2 + 2 * (-333933543096) * x * y + 179786836120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 781243281480 179786836120 (-333933543096)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc15 (x y : ℝ) : 0 ≤ (661942110320 * x ^ 2 + 2 * (-274133203134) * x * y + 147700125920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 661942110320 147700125920 (-274133203134)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc16 (x y : ℝ) : 0 ≤ (341890453720 * x ^ 2 + 2 * (-138950194848) * x * y + 77766239280 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 341890453720 77766239280 (-138950194848)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc17 (x y : ℝ) : 0 ≤ (97008364240 * x ^ 2 + 2 * (-39089889564) * x * y + 23694410480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 97008364240 23694410480 (-39089889564)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc18 (x y : ℝ) : 0 ≤ (11292991360 * x ^ 2 + 2 * (-4548061848) * x * y + 3150801760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 11292991360 3150801760 (-4548061848)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc19 (x y : ℝ) : 0 ≤ (36441336000 * x ^ 2 + 2 * (-22148058240) * x * y + 16173052200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 36441336000 16173052200 (-22148058240)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc20 (x y : ℝ) : 0 ≤ (274755292320 * x ^ 2 + 2 * (-154258269792) * x * y + 104856901120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 274755292320 104856901120 (-154258269792)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc21 (x y : ℝ) : 0 ≤ (893937893840 * x ^ 2 + 2 * (-465812117844) * x * y + 294637724420 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 893937893840 294637724420 (-465812117844)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc22 (x y : ℝ) : 0 ≤ (1619860304900 * x ^ 2 + 2 * (-789800687772) * x * y + 467442094140 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1619860304900 467442094140 (-789800687772)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc23 (x y : ℝ) : 0 ≤ (1757077254160 * x ^ 2 + 2 * (-809723096748) * x * y + 453895088640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1757077254160 453895088640 (-809723096748)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc24 (x y : ℝ) : 0 ≤ (1134990038960 * x ^ 2 + 2 * (-499542625788) * x * y + 270129657680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1134990038960 270129657680 (-499542625788)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc25 (x y : ℝ) : 0 ≤ (401907989120 * x ^ 2 + 2 * (-170556849744) * x * y + 91077082800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 401907989120 91077082800 (-170556849744)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc26 (x y : ℝ) : 0 ≤ (59758896880 * x ^ 2 + 2 * (-24638539224) * x * y + 13354295120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 59758896880 13354295120 (-24638539224)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc27 (x y : ℝ) : 0 ≤ (91489281600 * x ^ 2 + 2 * (-59794467648) * x * y + 46429159680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 91489281600 46429159680 (-59794467648)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc28 (x y : ℝ) : 0 ≤ (590753231360 * x ^ 2 + 2 * (-359615989056) * x * y + 261537060080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 590753231360 261537060080 (-359615989056)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc29 (x y : ℝ) : 0 ≤ (1601710881400 * x ^ 2 + 2 * (-908664717216) * x * y + 616809671920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1601710881400 616809671920 (-908664717216)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc30 (x y : ℝ) : 0 ≤ (2326829525280 * x ^ 2 + 2 * (-1234255129968) * x * y + 781703724000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2326829525280 781703724000 (-1234255129968)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc31 (x y : ℝ) : 0 ≤ (1903824005440 * x ^ 2 + 2 * (-949116116856) * x * y + 562817685920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1903824005440 562817685920 (-949116116856)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc32 (x y : ℝ) : 0 ≤ (829055040000 * x ^ 2 + 2 * (-390748387608) * x * y + 218634934720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 829055040000 218634934720 (-390748387608)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc33 (x y : ℝ) : 0 ≤ (149611463520 * x ^ 2 + 2 * (-67043088624) * x * y + 35818498560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 149611463520 35818498560 (-67043088624)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc34 (x y : ℝ) : 0 ≤ (142481379840 * x ^ 2 + 2 * (-99599797632) * x * y + 82527394560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 142481379840 82527394560 (-99599797632)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc35 (x y : ℝ) : 0 ≤ (765153799040 * x ^ 2 + 2 * (-502531248000) * x * y + 391709609120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 765153799040 391709609120 (-502531248000)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc36 (x y : ℝ) : 0 ≤ (1657603915680 * x ^ 2 + 2 * (-1020165005088) * x * y + 744368024880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1657603915680 744368024880 (-1020165005088)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc37 (x y : ℝ) : 0 ≤ (1807058977840 * x ^ 2 + 2 * (-1041462762624) * x * y + 708879162960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1807058977840 708879162960 (-1041462762624)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc38 (x y : ℝ) : 0 ≤ (989244464320 * x ^ 2 + 2 * (-534292548912) * x * y + 338754810560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 989244464320 338754810560 (-534292548912)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc39 (x y : ℝ) : 0 ≤ (217125931200 * x ^ 2 + 2 * (-110059034832) * x * y + 65061158400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 217125931200 65061158400 (-110059034832)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc40 (x y : ℝ) : 0 ≤ (141421989120 * x ^ 2 + 2 * (-105489283584) * x * y + 93954693120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 141421989120 93954693120 (-105489283584)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc41 (x y : ℝ) : 0 ≤ (605203066880 * x ^ 2 + 2 * (-428159069184) * x * y + 359891370560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 605203066880 359891370560 (-428159069184)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc42 (x y : ℝ) : 0 ≤ (980341467680 * x ^ 2 + 2 * (-654274865184) * x * y + 516206570240 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 980341467680 516206570240 (-654274865184)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc43 (x y : ℝ) : 0 ≤ (711648599360 * x ^ 2 + 2 * (-446122185984) * x * y + 328780724160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 711648599360 328780724160 (-446122185984)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc44 (x y : ℝ) : 0 ≤ (195141229440 * x ^ 2 + 2 * (-114497717472) * x * y + 78505209600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 195141229440 78505209600 (-114497717472)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc45 (x y : ℝ) : 0 ≤ (87917245440 * x ^ 2 + 2 * (-70186266624) * x * y + 68211588480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 87917245440 68211588480 (-70186266624)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc46 (x y : ℝ) : 0 ≤ (280046067200 * x ^ 2 + 2 * (-214467239424) * x * y + 197245667840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 280046067200 197245667840 (-214467239424)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc47 (x y : ℝ) : 0 ≤ (300512864000 * x ^ 2 + 2 * (-218970687936) * x * y + 189580245440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 300512864000 189580245440 (-218970687936)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc48 (x y : ℝ) : 0 ≤ (108641464000 * x ^ 2 + 2 * (-74698292160) * x * y + 60571899200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 108641464000 60571899200 (-74698292160)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc49 (x y : ℝ) : 0 ≤ (31795461120 * x ^ 2 + 2 * (-27574459392) * x * y + 30182983680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 31795461120 30182983680 (-27574459392)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc50 (x y : ℝ) : 0 ≤ (66443857920 * x ^ 2 + 2 * (-56221602816) * x * y + 58431909120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 66443857920 58431909120 (-56221602816)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc51 (x y : ℝ) : 0 ≤ (35152131200 * x ^ 2 + 2 * (-28680253440) * x * y + 28178904320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 35152131200 28178904320 (-28680253440)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc52 (x y : ℝ) : 0 ≤ (5472952320 * x ^ 2 + 2 * (-5447534592) * x * y + 7247950080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 5472952320 7247950080 (-5447534592)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc53 (x y : ℝ) : 0 ≤ (5470914560 * x ^ 2 + 2 * (-5520463872) * x * y + 7024718080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 5470914560 7024718080 (-5520463872)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc54 (x y : ℝ) : 0 ≤ (192737280 * x ^ 2 + 2 * (-325902336) * x * y + 688128000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 192737280 688128000 (-325902336)
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem B_SBE_entry11 (z w : ℝ) : 4423680 * Hdiag (1 + w / 2) ((1 - z) / 2) =
      801184320 * ((1 - z - w) ^ 9) +
      7761549600 * (w * (1 - z - w) ^ 8) +
      33545378390 * (w ^ 2 * (1 - z - w) ^ 7) +
      84189484865 * (w ^ 3 * (1 - z - w) ^ 6) +
      133900348280 * (w ^ 4 * (1 - z - w) ^ 5) +
      138250280160 * (w ^ 5 * (1 - z - w) ^ 4) +
      91017819400 * (w ^ 6 * (1 - z - w) ^ 3) +
      35683155740 * (w ^ 7 * (1 - z - w) ^ 2) +
      7013055760 * (w ^ 8 * (1 - z - w)) +
      393346160 * (w ^ 9) +
      8214628800 * (z * (1 - z - w) ^ 8) +
      70787466560 * (z * w * (1 - z - w) ^ 7) +
      268395571630 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      581299100260 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      781243281480 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      661942110320 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      341890453720 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      97008364240 * (z * w ^ 7 * (1 - z - w)) +
      11292991360 * (z * w ^ 8) +
      36441336000 * (z ^ 2 * (1 - z - w) ^ 7) +
      274755292320 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      893937893840 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      1619860304900 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      1757077254160 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      1134990038960 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      401907989120 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      59758896880 * (z ^ 2 * w ^ 7) +
      91489281600 * (z ^ 3 * (1 - z - w) ^ 6) +
      590753231360 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      1601710881400 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      2326829525280 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      1903824005440 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      829055040000 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      149611463520 * (z ^ 3 * w ^ 6) +
      142481379840 * (z ^ 4 * (1 - z - w) ^ 5) +
      765153799040 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      1657603915680 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      1807058977840 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      989244464320 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      217125931200 * (z ^ 4 * w ^ 5) +
      141421989120 * (z ^ 5 * (1 - z - w) ^ 4) +
      605203066880 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      980341467680 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      711648599360 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      195141229440 * (z ^ 5 * w ^ 4) +
      87917245440 * (z ^ 6 * (1 - z - w) ^ 3) +
      280046067200 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      300512864000 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      108641464000 * (z ^ 6 * w ^ 3) +
      31795461120 * (z ^ 7 * (1 - z - w) ^ 2) +
      66443857920 * (z ^ 7 * w * (1 - z - w)) +
      35152131200 * (z ^ 7 * w ^ 2) +
      5472952320 * (z ^ 8 * (1 - z - w)) +
      5470914560 * (z ^ 8 * w) +
      192737280 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_SBE_entry22 (z w : ℝ) : 4423680 * Hdiag ((1 - z) / 2) (1 + w / 2) =
      268058655 * ((1 - z - w) ^ 9) +
      2156641245 * (w * (1 - z - w) ^ 8) +
      8016883685 * (w ^ 2 * (1 - z - w) ^ 7) +
      18306466615 * (w ^ 3 * (1 - z - w) ^ 6) +
      28360530540 * (w ^ 4 * (1 - z - w) ^ 5) +
      30580181140 * (w ^ 5 * (1 - z - w) ^ 4) +
      22502066300 * (w ^ 6 * (1 - z - w) ^ 3) +
      10652132340 * (w ^ 7 * (1 - z - w) ^ 2) +
      2877353600 * (w ^ 8 * (1 - z - w)) +
      329471440 * (w ^ 9) +
      3173049120 * (z * (1 - z - w) ^ 8) +
      23133767660 * (z * w * (1 - z - w) ^ 7) +
      75410056960 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      144758679180 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      179786836120 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      147700125920 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      77766239280 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      23694410480 * (z * w ^ 7 * (1 - z - w)) +
      3150801760 * (z * w ^ 8) +
      16173052200 * (z ^ 2 * (1 - z - w) ^ 7) +
      104856901120 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      294637724420 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      467442094140 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      453895088640 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      270129657680 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      91077082800 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      13354295120 * (z ^ 2 * w ^ 7) +
      46429159680 * (z ^ 3 * (1 - z - w) ^ 6) +
      261537060080 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      616809671920 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      781703724000 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      562817685920 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      218634934720 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      35818498560 * (z ^ 3 * w ^ 6) +
      82527394560 * (z ^ 4 * (1 - z - w) ^ 5) +
      391709609120 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      744368024880 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      708879162960 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      338754810560 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      65061158400 * (z ^ 4 * w ^ 5) +
      93954693120 * (z ^ 5 * (1 - z - w) ^ 4) +
      359891370560 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      516206570240 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      328780724160 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      78505209600 * (z ^ 5 * w ^ 4) +
      68211588480 * (z ^ 6 * (1 - z - w) ^ 3) +
      197245667840 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      189580245440 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      60571899200 * (z ^ 6 * w ^ 3) +
      30182983680 * (z ^ 7 * (1 - z - w) ^ 2) +
      58431909120 * (z ^ 7 * w * (1 - z - w)) +
      28178904320 * (z ^ 7 * w ^ 2) +
      7247950080 * (z ^ 8 * (1 - z - w)) +
      7024718080 * (z ^ 8 * w) +
      688128000 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_SBE_entry12 (z w : ℝ) : 4423680 * Hmixed (1 + w / 2) ((1 - z) / 2) =
      (-411481728) * ((1 - z - w) ^ 9) +
      (-3632190912) * (w * (1 - z - w) ^ 8) +
      (-14568520482) * (w ^ 2 * (1 - z - w) ^ 7) +
      (-34684787694) * (w ^ 3 * (1 - z - w) ^ 6) +
      (-53475840324) * (w ^ 4 * (1 - z - w) ^ 5) +
      (-54534308550) * (w ^ 5 * (1 - z - w) ^ 4) +
      (-36001603866) * (w ^ 6 * (1 - z - w) ^ 3) +
      (-14336038872) * (w ^ 7 * (1 - z - w) ^ 2) +
      (-2908573260) * (w ^ 8 * (1 - z - w)) +
      (-178693632) * (w ^ 9) +
      (-4609025856) * (z * (1 - z - w) ^ 8) +
      (-36412750944) * (z * w * (1 - z - w) ^ 7) +
      (-127897332726) * (z * w ^ 2 * (1 - z - w) ^ 6) +
      (-260302314732) * (z * w ^ 3 * (1 - z - w) ^ 5) +
      (-333933543096) * (z * w ^ 4 * (1 - z - w) ^ 4) +
      (-274133203134) * (z * w ^ 5 * (1 - z - w) ^ 3) +
      (-138950194848) * (z * w ^ 6 * (1 - z - w) ^ 2) +
      (-39089889564) * (z * w ^ 7 * (1 - z - w)) +
      (-4548061848) * (z * w ^ 8) +
      (-22148058240) * (z ^ 2 * (1 - z - w) ^ 7) +
      (-154258269792) * (z ^ 2 * w * (1 - z - w) ^ 6) +
      (-465812117844) * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      (-789800687772) * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      (-809723096748) * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      (-499542625788) * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      (-170556849744) * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      (-24638539224) * (z ^ 2 * w ^ 7) +
      (-59794467648) * (z ^ 3 * (1 - z - w) ^ 6) +
      (-359615989056) * (z ^ 3 * w * (1 - z - w) ^ 5) +
      (-908664717216) * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      (-1234255129968) * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      (-949116116856) * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      (-390748387608) * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      (-67043088624) * (z ^ 3 * w ^ 6) +
      (-99599797632) * (z ^ 4 * (1 - z - w) ^ 5) +
      (-502531248000) * (z ^ 4 * w * (1 - z - w) ^ 4) +
      (-1020165005088) * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      (-1041462762624) * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      (-534292548912) * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      (-110059034832) * (z ^ 4 * w ^ 5) +
      (-105489283584) * (z ^ 5 * (1 - z - w) ^ 4) +
      (-428159069184) * (z ^ 5 * w * (1 - z - w) ^ 3) +
      (-654274865184) * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      (-446122185984) * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      (-114497717472) * (z ^ 5 * w ^ 4) +
      (-70186266624) * (z ^ 6 * (1 - z - w) ^ 3) +
      (-214467239424) * (z ^ 6 * w * (1 - z - w) ^ 2) +
      (-218970687936) * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      (-74698292160) * (z ^ 6 * w ^ 3) +
      (-27574459392) * (z ^ 7 * (1 - z - w) ^ 2) +
      (-56221602816) * (z ^ 7 * w * (1 - z - w)) +
      (-28680253440) * (z ^ 7 * w ^ 2) +
      (-5447534592) * (z ^ 8 * (1 - z - w)) +
      (-5520463872) * (z ^ 8 * w) +
      (-325902336) * (z ^ 9) := by
  simp only [Hmixed, mixedNumerator, Sbound, denominator, kappaB]
  ring

private theorem B_SBE_entry11_list (z w : ℝ) :
    4423680 * Hdiag (1 + w / 2) ((1 - z) / 2) = ((B_SBE_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [B_SBE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_SBE_entry11 z w

private theorem B_SBE_entry22_list (z w : ℝ) :
    4423680 * Hdiag ((1 - z) / 2) (1 + w / 2) = ((B_SBE_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [B_SBE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_SBE_entry22 z w

private theorem B_SBE_entry12_list (z w : ℝ) :
    4423680 * Hmixed (1 + w / 2) ((1 - z) / 2) = ((B_SBE_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [B_SBE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_SBE_entry12 z w

private theorem B_SBE_oai {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag (1 + w / 2) ((1 - z) / 2) * x ^ 2 + 2 * Hmixed (1 + w / 2) ((1 - z) / 2) * x * y + Hdiag ((1 - z) / 2) (1 + w / 2) * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (B_SBE_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (B_SBE_hc0 x y) (by positivity),
      mul_nonneg (B_SBE_hc1 x y) (by positivity),
      mul_nonneg (B_SBE_hc2 x y) (by positivity),
      mul_nonneg (B_SBE_hc3 x y) (by positivity),
      mul_nonneg (B_SBE_hc4 x y) (by positivity),
      mul_nonneg (B_SBE_hc5 x y) (by positivity),
      mul_nonneg (B_SBE_hc6 x y) (by positivity),
      mul_nonneg (B_SBE_hc7 x y) (by positivity),
      mul_nonneg (B_SBE_hc8 x y) (by positivity),
      mul_nonneg (B_SBE_hc9 x y) (by positivity),
      mul_nonneg (B_SBE_hc10 x y) (by positivity),
      mul_nonneg (B_SBE_hc11 x y) (by positivity),
      mul_nonneg (B_SBE_hc12 x y) (by positivity),
      mul_nonneg (B_SBE_hc13 x y) (by positivity),
      mul_nonneg (B_SBE_hc14 x y) (by positivity),
      mul_nonneg (B_SBE_hc15 x y) (by positivity),
      mul_nonneg (B_SBE_hc16 x y) (by positivity),
      mul_nonneg (B_SBE_hc17 x y) (by positivity),
      mul_nonneg (B_SBE_hc18 x y) (by positivity),
      mul_nonneg (B_SBE_hc19 x y) (by positivity),
      mul_nonneg (B_SBE_hc20 x y) (by positivity),
      mul_nonneg (B_SBE_hc21 x y) (by positivity),
      mul_nonneg (B_SBE_hc22 x y) (by positivity),
      mul_nonneg (B_SBE_hc23 x y) (by positivity),
      mul_nonneg (B_SBE_hc24 x y) (by positivity),
      mul_nonneg (B_SBE_hc25 x y) (by positivity),
      mul_nonneg (B_SBE_hc26 x y) (by positivity),
      mul_nonneg (B_SBE_hc27 x y) (by positivity),
      mul_nonneg (B_SBE_hc28 x y) (by positivity),
      mul_nonneg (B_SBE_hc29 x y) (by positivity),
      mul_nonneg (B_SBE_hc30 x y) (by positivity),
      mul_nonneg (B_SBE_hc31 x y) (by positivity),
      mul_nonneg (B_SBE_hc32 x y) (by positivity),
      mul_nonneg (B_SBE_hc33 x y) (by positivity),
      mul_nonneg (B_SBE_hc34 x y) (by positivity),
      mul_nonneg (B_SBE_hc35 x y) (by positivity),
      mul_nonneg (B_SBE_hc36 x y) (by positivity),
      mul_nonneg (B_SBE_hc37 x y) (by positivity),
      mul_nonneg (B_SBE_hc38 x y) (by positivity),
      mul_nonneg (B_SBE_hc39 x y) (by positivity),
      mul_nonneg (B_SBE_hc40 x y) (by positivity),
      mul_nonneg (B_SBE_hc41 x y) (by positivity),
      mul_nonneg (B_SBE_hc42 x y) (by positivity),
      mul_nonneg (B_SBE_hc43 x y) (by positivity),
      mul_nonneg (B_SBE_hc44 x y) (by positivity),
      mul_nonneg (B_SBE_hc45 x y) (by positivity),
      mul_nonneg (B_SBE_hc46 x y) (by positivity),
      mul_nonneg (B_SBE_hc47 x y) (by positivity),
      mul_nonneg (B_SBE_hc48 x y) (by positivity),
      mul_nonneg (B_SBE_hc49 x y) (by positivity),
      mul_nonneg (B_SBE_hc50 x y) (by positivity),
      mul_nonneg (B_SBE_hc51 x y) (by positivity),
      mul_nonneg (B_SBE_hc52 x y) (by positivity),
      mul_nonneg (B_SBE_hc53 x y) (by positivity),
      mul_nonneg (B_SBE_hc54 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (B_SBE_data z w) x y hcoeff
  rw [← B_SBE_entry11_list, ← B_SBE_entry12_list, ← B_SBE_entry22_list] at hpos
  nlinarith only [hpos]

end

end PositiveEinsteinFour.Quadratic
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Quadratic.B_SBE_oai := @OAI.PositiveEinsteinFour.Quadratic.B_SBE_oai
