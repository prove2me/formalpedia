-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.hilbert_quadratic_bound_closed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:03:13.014624+00:00
-- url     : https://prove2.me/submissions/96568d86-6d65-4f91-9391-fd68ab76548b

import Mathlib
import Definitions.Def_OAIQ091C005
import Definitions.Def_OAIQ091C012
import Theorems.Thm_OAI_PositiveEinsteinFour_Quadratic_B_ACE
import Theorems.Thm_OAI_PositiveEinsteinFour_Quadratic_B_ASE
import Theorems.Thm_OAI_PositiveEinsteinFour_Quadratic_B_CBE
import Theorems.Thm_OAI_PositiveEinsteinFour_Quadratic_B_SBE
import Theorems.Thm_OAI_PositiveEinsteinFour_Quadratic_B_SUB
import Theorems.Thm_OAI_PositiveEinsteinFour_Quadratic_combine_quadratic_nonneg
import Theorems.Thm_OAI_PositiveEinsteinFour_quadratic_form_nonneg_of_det

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Boundary
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact triangle certificates and the full zeroth-order coupling bound. -/

namespace PositiveEinsteinFour.Boundary

open Potential

noncomputable section

theorem theta_swap (v b : ℝ) : theta b v = theta v b := by
  unfold theta
  ring

end

end PositiveEinsteinFour.Boundary

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Matrix
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small positive semidefinite forms and Schur completion

The closed determinant criterion includes vanishing diagonal entries. The
Schur estimate below consequently includes the singular axial endpoint of the
quadratic comparison in Section 6 of the manuscript.
-/

namespace PositiveEinsteinFour

/-- Conversely, nonnegativity of the binary form implies the closed diagonal
and determinant conditions. The singular diagonal case is tested directly. -/
theorem quadratic_form_det_of_nonneg
    (r h s : ℝ)
    (hform : ∀ x y, 0 ≤ r * x ^ 2 + 2 * s * x * y + h * y ^ 2) :
    0 ≤ r ∧ 0 ≤ h ∧ s ^ 2 ≤ r * h := by
  have hr : 0 ≤ r := by simpa using hform 1 0
  have hh : 0 ≤ h := by simpa using hform 0 1
  refine ⟨hr, hh, ?_⟩
  by_cases hrzero : r = 0
  · subst r
    have htest := hform (h + 1) (-s)
    have hhs : 0 ≤ h * s ^ 2 := mul_nonneg hh (sq_nonneg s)
    have hs : s = 0 := by nlinarith [sq_nonneg s]
    simp [hs]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
    have htest := hform (-s) r
    have hproduct : 0 ≤ r * (r * h - s ^ 2) := by nlinarith
    have hdet := nonneg_of_mul_nonneg_right hproduct hrpos
    linarith

end PositiveEinsteinFour

end OAI
end

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

private theorem B_OAS_hc0 (x y : ℝ) : 0 ≤ (65413120 * x ^ 2 + 2 * 0 * x * y + 65413120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 65413120 65413120 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc1 (x y : ℝ) : 0 ≤ (768942080 * x ^ 2 + 2 * (-133423104) * x * y + 752844800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 768942080 752844800 (-133423104)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc2 (x y : ℝ) : 0 ≤ (3102197760 * x ^ 2 + 2 * (-863834112) * x * y + 3415869440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3102197760 3415869440 (-863834112)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc3 (x y : ℝ) : 0 ≤ (6619097600 * x ^ 2 + 2 * (-2481039360) * x * y + 8497295360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6619097600 8497295360 (-2481039360)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc4 (x y : ℝ) : 0 ≤ (8519705600 * x ^ 2 + 2 * (-4130804736) * x * y + 13078190080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 8519705600 13078190080 (-4130804736)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc5 (x y : ℝ) : 0 ≤ (6914861440 * x ^ 2 + 2 * (-4369367040) * x * y + 13062400000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6914861440 13062400000 (-4369367040)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc6 (x y : ℝ) : 0 ≤ (3543654400 * x ^ 2 + 2 * (-3018777600) * x * y + 8517160960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3543654400 8517160960 (-3018777600)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc7 (x y : ℝ) : 0 ≤ (1123260480 * x ^ 2 + 2 * (-1337256960) * x * y + 3508029440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1123260480 3508029440 (-1337256960)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc8 (x y : ℝ) : 0 ≤ (217338880 * x ^ 2 + 2 * (-348407808) * x * y + 829952000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 217338880 829952000 (-348407808)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc9 (x y : ℝ) : 0 ≤ (24092160 * x ^ 2 + 2 * (-40737792) * x * y + 86016000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 24092160 86016000 (-40737792)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc10 (x y : ℝ) : 0 ≤ (760893440 * x ^ 2 + 2 * (-170948352) * x * y + 760893440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 760893440 760893440 (-170948352)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc11 (x y : ℝ) : 0 ≤ (7266693120 * x ^ 2 + 2 * (-2996311680) * x * y + 7580364800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7266693120 7580364800 (-2996311680)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc12 (x y : ℝ) : 0 ≤ (25423996160 * x ^ 2 + 2 * (-13760692032) * x * y + 29375939840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 25423996160 29375939840 (-13760692032)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc13 (x y : ℝ) : 0 ≤ (47330421760 * x ^ 2 + 2 * (-31098090144) * x * y + 61264896000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 47330421760 61264896000 (-31098090144)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc14 (x y : ℝ) : 0 ≤ (53256127040 * x ^ 2 + 2 * (-41155529856) * x * y + 76993188800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 53256127040 76993188800 (-41155529856)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc15 (x y : ℝ) : 0 ≤ (38162003200 * x ^ 2 + 2 * (-33876050304) * x * y + 60410876160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 38162003200 60410876160 (-33876050304)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc16 (x y : ℝ) : 0 ≤ (17632998560 * x ^ 2 + 2 * (-17334445536) * x * y + 29111903200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 17632998560 29111903200 (-17334445536)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc17 (x y : ℝ) : 0 ≤ (5013623360 * x ^ 2 + 2 * (-5122989312) * x * y + 7919686080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 5013623360 7919686080 (-5122989312)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc18 (x y : ℝ) : 0 ≤ (684373760 * x ^ 2 + 2 * (-671825664) * x * y + 933897760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 684373760 933897760 (-671825664)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc19 (x y : ℝ) : 0 ≤ (3711764480 * x ^ 2 + 2 * (-1619632512) * x * y + 3711764480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3711764480 3711764480 (-1619632512)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc20 (x y : ℝ) : 0 ≤ (28774671360 * x ^ 2 + 2 * (-17221631040) * x * y + 30750643200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 28774671360 30750643200 (-17221631040)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc21 (x y : ℝ) : 0 ≤ (84574977280 * x ^ 2 + 2 * (-60810326976) * x * y + 98638961920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 84574977280 98638961920 (-60810326976)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc22 (x y : ℝ) : 0 ≤ (131648405760 * x ^ 2 + 2 * (-108187004544) * x * y + 166572573120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 131648405760 166572573120 (-108187004544)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc23 (x y : ℝ) : 0 ≤ (121899264640 * x ^ 2 + 2 * (-110478091632) * x * y + 163288773760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 121899264640 163288773760 (-110478091632)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc24 (x y : ℝ) : 0 ≤ (69674734240 * x ^ 2 + 2 * (-66707564592) * x * y + 94041361600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 69674734240 94041361600 (-66707564592)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc25 (x y : ℝ) : 0 ≤ (23585061280 * x ^ 2 + 2 * (-22531986528) * x * y + 29730955360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 23585061280 29730955360 (-22531986528)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc26 (x y : ℝ) : 0 ≤ (3680782480 * x ^ 2 + 2 * (-3316860672) * x * y + 4005877600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3680782480 4005877600 (-3316860672)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc27 (x y : ℝ) : 0 ≤ (9920885760 * x ^ 2 + 2 * (-5965350432) * x * y + 9920885760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 9920885760 9920885760 (-5965350432)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc28 (x y : ℝ) : 0 ≤ (62114142720 * x ^ 2 + 2 * (-45728303280) * x * y + 66802137600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 62114142720 66802137600 (-45728303280)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc29 (x y : ℝ) : 0 ≤ (148853092640 * x ^ 2 + 2 * (-124803813792) * x * y + 171908729120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 148853092640 171908729120 (-124803813792)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc30 (x y : ℝ) : 0 ≤ (185333807360 * x ^ 2 + 2 * (-169623069600) * x * y + 224924409600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 185333807360 224924409600 (-169623069600)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc31 (x y : ℝ) : 0 ≤ (131851537360 * x ^ 2 + 2 * (-126020279448) * x * y + 160844009040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 131851537360 160844009040 (-126020279448)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc32 (x y : ℝ) : 0 ≤ (52794631200 * x ^ 2 + 2 * (-49875604560) * x * y + 60413316320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 52794631200 60413316320 (-49875604560)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc33 (x y : ℝ) : 0 ≤ (9442244840 * x ^ 2 + 2 * (-8358032376) * x * y + 9412328520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 9442244840 9412328520 (-8358032376)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc34 (x y : ℝ) : 0 ≤ (16114535040 * x ^ 2 + 2 * (-11694054768) * x * y + 16114535040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 16114535040 16114535040 (-11694054768)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc35 (x y : ℝ) : 0 ≤ (80126106240 * x ^ 2 + 2 * (-66996501024) * x * y + 85890015360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 80126106240 85890015360 (-66996501024)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc36 (x y : ℝ) : 0 ≤ (150582376320 * x ^ 2 + 2 * (-137797344648) * x * y + 169927950720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 150582376320 169927950720 (-137797344648)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc37 (x y : ℝ) : 0 ≤ (140922909840 * x ^ 2 + 2 * (-134975315424) * x * y + 161127648560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 140922909840 161127648560 (-134975315424)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc38 (x y : ℝ) : 0 ≤ (68626882640 * x ^ 2 + 2 * (-65202397092) * x * y + 74660334640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 68626882640 74660334640 (-65202397092)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc39 (x y : ℝ) : 0 ≤ (14292149040 * x ^ 2 + 2 * (-12738598764) * x * y + 13739270960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 14292149040 13739270960 (-12738598764)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc40 (x y : ℝ) : 0 ≤ (16601612160 * x ^ 2 + 2 * (-13598342736) * x * y + 16601612160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 16601612160 16601612160 (-13598342736)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc41 (x y : ℝ) : 0 ≤ (63449174400 * x ^ 2 + 2 * (-57493812240) * x * y + 67318289280 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 63449174400 67318289280 (-57493812240)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc42 (x y : ℝ) : 0 ≤ (88047030880 * x ^ 2 + 2 * (-84254117448) * x * y + 95821003360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 88047030880 95821003360 (-84254117448)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc43 (x y : ℝ) : 0 ≤ (55390166960 * x ^ 2 + 2 * (-53157515286) * x * y + 58452769040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 55390166960 58452769040 (-53157515286)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc44 (x y : ℝ) : 0 ≤ (13862722720 * x ^ 2 + 2 * (-12586076178) * x * y + 13174861240 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 13862722720 13174861240 (-12586076178)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc45 (x y : ℝ) : 0 ≤ (10897288640 * x ^ 2 + 2 * (-9680731728) * x * y + 10897288640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 10897288640 10897288640 (-9680731728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc46 (x y : ℝ) : 0 ≤ (30216649600 * x ^ 2 + 2 * (-28722051948) * x * y + 31512311680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 30216649600 31512311680 (-28722051948)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc47 (x y : ℝ) : 0 ≤ (27711182480 * x ^ 2 + 2 * (-26818681746) * x * y + 28639138320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 27711182480 28639138320 (-26818681746)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc48 (x y : ℝ) : 0 ≤ (8843240540 * x ^ 2 + 2 * (-8217437028) * x * y + 8428078560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 8843240540 8428078560 (-8217437028)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc49 (x y : ℝ) : 0 ≤ (4409211520 * x ^ 2 + 2 * (-4133675514) * x * y + 4409211520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4409211520 4409211520 (-4133675514)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc50 (x y : ℝ) : 0 ≤ (7942967040 * x ^ 2 + 2 * (-7715144847) * x * y + 8075532160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7942967040 8075532160 (-7715144847)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc51 (x y : ℝ) : 0 ≤ (3639372850 * x ^ 2 + 2 * (-3461048223) * x * y + 3510579250 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3639372850 3510579250 (-3461048223)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc52 (x y : ℝ) : 0 ≤ (1001156200 * x ^ 2 + 2 * (-969780831) * x * y + 1001156200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1001156200 1001156200 (-969780831)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc53 (x y : ℝ) : 0 ≤ (886041000 * x ^ 2 + 2 * (-859230990) * x * y + 869941800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 886041000 869941800 (-859230990)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc54 (x y : ℝ) : 0 ≤ (97554600 * x ^ 2 + 2 * (-95882805) * x * y + 97554600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 97554600 97554600 (-95882805)
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem B_OAS_entry11 (z w : ℝ) : 552960 * Hdiag (z / 2 + w) (z / 2) =
      65413120 * ((1 - z - w) ^ 9) +
      768942080 * (w * (1 - z - w) ^ 8) +
      3102197760 * (w ^ 2 * (1 - z - w) ^ 7) +
      6619097600 * (w ^ 3 * (1 - z - w) ^ 6) +
      8519705600 * (w ^ 4 * (1 - z - w) ^ 5) +
      6914861440 * (w ^ 5 * (1 - z - w) ^ 4) +
      3543654400 * (w ^ 6 * (1 - z - w) ^ 3) +
      1123260480 * (w ^ 7 * (1 - z - w) ^ 2) +
      217338880 * (w ^ 8 * (1 - z - w)) +
      24092160 * (w ^ 9) +
      760893440 * (z * (1 - z - w) ^ 8) +
      7266693120 * (z * w * (1 - z - w) ^ 7) +
      25423996160 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      47330421760 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      53256127040 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      38162003200 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      17632998560 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      5013623360 * (z * w ^ 7 * (1 - z - w)) +
      684373760 * (z * w ^ 8) +
      3711764480 * (z ^ 2 * (1 - z - w) ^ 7) +
      28774671360 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      84574977280 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      131648405760 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      121899264640 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      69674734240 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      23585061280 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      3680782480 * (z ^ 2 * w ^ 7) +
      9920885760 * (z ^ 3 * (1 - z - w) ^ 6) +
      62114142720 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      148853092640 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      185333807360 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      131851537360 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      52794631200 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      9442244840 * (z ^ 3 * w ^ 6) +
      16114535040 * (z ^ 4 * (1 - z - w) ^ 5) +
      80126106240 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      150582376320 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      140922909840 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      68626882640 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      14292149040 * (z ^ 4 * w ^ 5) +
      16601612160 * (z ^ 5 * (1 - z - w) ^ 4) +
      63449174400 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      88047030880 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      55390166960 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      13862722720 * (z ^ 5 * w ^ 4) +
      10897288640 * (z ^ 6 * (1 - z - w) ^ 3) +
      30216649600 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      27711182480 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      8843240540 * (z ^ 6 * w ^ 3) +
      4409211520 * (z ^ 7 * (1 - z - w) ^ 2) +
      7942967040 * (z ^ 7 * w * (1 - z - w)) +
      3639372850 * (z ^ 7 * w ^ 2) +
      1001156200 * (z ^ 8 * (1 - z - w)) +
      886041000 * (z ^ 8 * w) +
      97554600 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_OAS_entry22 (z w : ℝ) : 552960 * Hdiag (z / 2) (z / 2 + w) =
      65413120 * ((1 - z - w) ^ 9) +
      752844800 * (w * (1 - z - w) ^ 8) +
      3415869440 * (w ^ 2 * (1 - z - w) ^ 7) +
      8497295360 * (w ^ 3 * (1 - z - w) ^ 6) +
      13078190080 * (w ^ 4 * (1 - z - w) ^ 5) +
      13062400000 * (w ^ 5 * (1 - z - w) ^ 4) +
      8517160960 * (w ^ 6 * (1 - z - w) ^ 3) +
      3508029440 * (w ^ 7 * (1 - z - w) ^ 2) +
      829952000 * (w ^ 8 * (1 - z - w)) +
      86016000 * (w ^ 9) +
      760893440 * (z * (1 - z - w) ^ 8) +
      7580364800 * (z * w * (1 - z - w) ^ 7) +
      29375939840 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      61264896000 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      76993188800 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      60410876160 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      29111903200 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      7919686080 * (z * w ^ 7 * (1 - z - w)) +
      933897760 * (z * w ^ 8) +
      3711764480 * (z ^ 2 * (1 - z - w) ^ 7) +
      30750643200 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      98638961920 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      166572573120 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      163288773760 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      94041361600 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      29730955360 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      4005877600 * (z ^ 2 * w ^ 7) +
      9920885760 * (z ^ 3 * (1 - z - w) ^ 6) +
      66802137600 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      171908729120 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      224924409600 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      160844009040 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      60413316320 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      9412328520 * (z ^ 3 * w ^ 6) +
      16114535040 * (z ^ 4 * (1 - z - w) ^ 5) +
      85890015360 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      169927950720 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      161127648560 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      74660334640 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      13739270960 * (z ^ 4 * w ^ 5) +
      16601612160 * (z ^ 5 * (1 - z - w) ^ 4) +
      67318289280 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      95821003360 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      58452769040 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      13174861240 * (z ^ 5 * w ^ 4) +
      10897288640 * (z ^ 6 * (1 - z - w) ^ 3) +
      31512311680 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      28639138320 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      8428078560 * (z ^ 6 * w ^ 3) +
      4409211520 * (z ^ 7 * (1 - z - w) ^ 2) +
      8075532160 * (z ^ 7 * w * (1 - z - w)) +
      3510579250 * (z ^ 7 * w ^ 2) +
      1001156200 * (z ^ 8 * (1 - z - w)) +
      869941800 * (z ^ 8 * w) +
      97554600 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_OAS_entry12 (z w : ℝ) : 552960 * Hmixed (z / 2 + w) (z / 2) =
      (-133423104) * (w * (1 - z - w) ^ 8) +
      (-863834112) * (w ^ 2 * (1 - z - w) ^ 7) +
      (-2481039360) * (w ^ 3 * (1 - z - w) ^ 6) +
      (-4130804736) * (w ^ 4 * (1 - z - w) ^ 5) +
      (-4369367040) * (w ^ 5 * (1 - z - w) ^ 4) +
      (-3018777600) * (w ^ 6 * (1 - z - w) ^ 3) +
      (-1337256960) * (w ^ 7 * (1 - z - w) ^ 2) +
      (-348407808) * (w ^ 8 * (1 - z - w)) +
      (-40737792) * (w ^ 9) +
      (-170948352) * (z * (1 - z - w) ^ 8) +
      (-2996311680) * (z * w * (1 - z - w) ^ 7) +
      (-13760692032) * (z * w ^ 2 * (1 - z - w) ^ 6) +
      (-31098090144) * (z * w ^ 3 * (1 - z - w) ^ 5) +
      (-41155529856) * (z * w ^ 4 * (1 - z - w) ^ 4) +
      (-33876050304) * (z * w ^ 5 * (1 - z - w) ^ 3) +
      (-17334445536) * (z * w ^ 6 * (1 - z - w) ^ 2) +
      (-5122989312) * (z * w ^ 7 * (1 - z - w)) +
      (-671825664) * (z * w ^ 8) +
      (-1619632512) * (z ^ 2 * (1 - z - w) ^ 7) +
      (-17221631040) * (z ^ 2 * w * (1 - z - w) ^ 6) +
      (-60810326976) * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      (-108187004544) * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      (-110478091632) * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      (-66707564592) * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      (-22531986528) * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      (-3316860672) * (z ^ 2 * w ^ 7) +
      (-5965350432) * (z ^ 3 * (1 - z - w) ^ 6) +
      (-45728303280) * (z ^ 3 * w * (1 - z - w) ^ 5) +
      (-124803813792) * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      (-169623069600) * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      (-126020279448) * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      (-49875604560) * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      (-8358032376) * (z ^ 3 * w ^ 6) +
      (-11694054768) * (z ^ 4 * (1 - z - w) ^ 5) +
      (-66996501024) * (z ^ 4 * w * (1 - z - w) ^ 4) +
      (-137797344648) * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      (-134975315424) * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      (-65202397092) * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      (-12738598764) * (z ^ 4 * w ^ 5) +
      (-13598342736) * (z ^ 5 * (1 - z - w) ^ 4) +
      (-57493812240) * (z ^ 5 * w * (1 - z - w) ^ 3) +
      (-84254117448) * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      (-53157515286) * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      (-12586076178) * (z ^ 5 * w ^ 4) +
      (-9680731728) * (z ^ 6 * (1 - z - w) ^ 3) +
      (-28722051948) * (z ^ 6 * w * (1 - z - w) ^ 2) +
      (-26818681746) * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      (-8217437028) * (z ^ 6 * w ^ 3) +
      (-4133675514) * (z ^ 7 * (1 - z - w) ^ 2) +
      (-7715144847) * (z ^ 7 * w * (1 - z - w)) +
      (-3461048223) * (z ^ 7 * w ^ 2) +
      (-969780831) * (z ^ 8 * (1 - z - w)) +
      (-859230990) * (z ^ 8 * w) +
      (-95882805) * (z ^ 9) := by
  simp only [Hmixed, mixedNumerator, Sbound, denominator, kappaB]
  ring

private theorem B_OAS_entry11_list (z w : ℝ) :
    552960 * Hdiag (z / 2 + w) (z / 2) = ((B_OAS_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [B_OAS_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_OAS_entry11 z w

private theorem B_OAS_entry22_list (z w : ℝ) :
    552960 * Hdiag (z / 2) (z / 2 + w) = ((B_OAS_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [B_OAS_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_OAS_entry22 z w

private theorem B_OAS_entry12_list (z w : ℝ) :
    552960 * Hmixed (z / 2 + w) (z / 2) = ((B_OAS_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [B_OAS_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_OAS_entry12 z w

private theorem B_OAS {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag (z / 2 + w) (z / 2) * x ^ 2 + 2 * Hmixed (z / 2 + w) (z / 2) * x * y + Hdiag (z / 2) (z / 2 + w) * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (B_OAS_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (B_OAS_hc0 x y) (by positivity),
      mul_nonneg (B_OAS_hc1 x y) (by positivity),
      mul_nonneg (B_OAS_hc2 x y) (by positivity),
      mul_nonneg (B_OAS_hc3 x y) (by positivity),
      mul_nonneg (B_OAS_hc4 x y) (by positivity),
      mul_nonneg (B_OAS_hc5 x y) (by positivity),
      mul_nonneg (B_OAS_hc6 x y) (by positivity),
      mul_nonneg (B_OAS_hc7 x y) (by positivity),
      mul_nonneg (B_OAS_hc8 x y) (by positivity),
      mul_nonneg (B_OAS_hc9 x y) (by positivity),
      mul_nonneg (B_OAS_hc10 x y) (by positivity),
      mul_nonneg (B_OAS_hc11 x y) (by positivity),
      mul_nonneg (B_OAS_hc12 x y) (by positivity),
      mul_nonneg (B_OAS_hc13 x y) (by positivity),
      mul_nonneg (B_OAS_hc14 x y) (by positivity),
      mul_nonneg (B_OAS_hc15 x y) (by positivity),
      mul_nonneg (B_OAS_hc16 x y) (by positivity),
      mul_nonneg (B_OAS_hc17 x y) (by positivity),
      mul_nonneg (B_OAS_hc18 x y) (by positivity),
      mul_nonneg (B_OAS_hc19 x y) (by positivity),
      mul_nonneg (B_OAS_hc20 x y) (by positivity),
      mul_nonneg (B_OAS_hc21 x y) (by positivity),
      mul_nonneg (B_OAS_hc22 x y) (by positivity),
      mul_nonneg (B_OAS_hc23 x y) (by positivity),
      mul_nonneg (B_OAS_hc24 x y) (by positivity),
      mul_nonneg (B_OAS_hc25 x y) (by positivity),
      mul_nonneg (B_OAS_hc26 x y) (by positivity),
      mul_nonneg (B_OAS_hc27 x y) (by positivity),
      mul_nonneg (B_OAS_hc28 x y) (by positivity),
      mul_nonneg (B_OAS_hc29 x y) (by positivity),
      mul_nonneg (B_OAS_hc30 x y) (by positivity),
      mul_nonneg (B_OAS_hc31 x y) (by positivity),
      mul_nonneg (B_OAS_hc32 x y) (by positivity),
      mul_nonneg (B_OAS_hc33 x y) (by positivity),
      mul_nonneg (B_OAS_hc34 x y) (by positivity),
      mul_nonneg (B_OAS_hc35 x y) (by positivity),
      mul_nonneg (B_OAS_hc36 x y) (by positivity),
      mul_nonneg (B_OAS_hc37 x y) (by positivity),
      mul_nonneg (B_OAS_hc38 x y) (by positivity),
      mul_nonneg (B_OAS_hc39 x y) (by positivity),
      mul_nonneg (B_OAS_hc40 x y) (by positivity),
      mul_nonneg (B_OAS_hc41 x y) (by positivity),
      mul_nonneg (B_OAS_hc42 x y) (by positivity),
      mul_nonneg (B_OAS_hc43 x y) (by positivity),
      mul_nonneg (B_OAS_hc44 x y) (by positivity),
      mul_nonneg (B_OAS_hc45 x y) (by positivity),
      mul_nonneg (B_OAS_hc46 x y) (by positivity),
      mul_nonneg (B_OAS_hc47 x y) (by positivity),
      mul_nonneg (B_OAS_hc48 x y) (by positivity),
      mul_nonneg (B_OAS_hc49 x y) (by positivity),
      mul_nonneg (B_OAS_hc50 x y) (by positivity),
      mul_nonneg (B_OAS_hc51 x y) (by positivity),
      mul_nonneg (B_OAS_hc52 x y) (by positivity),
      mul_nonneg (B_OAS_hc53 x y) (by positivity),
      mul_nonneg (B_OAS_hc54 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (B_OAS_data z w) x y hcoeff
  rw [← B_OAS_entry11_list, ← B_OAS_entry12_list, ← B_OAS_entry22_list] at hpos
  nlinarith only [hpos]

/-- The second matrix certificate, on the ordered half of the closed spectral
triangle. The six Bernstein triangles retain their boundary zero matrices. -/
theorem coupling_matrix_nonneg {v b : ℝ}
    (hb : 0 ≤ b) (horder : b ≤ v) (hsum : v + b ≤ 2) (x y : ℝ) :
    0 ≤ Hdiag v b * x ^ 2 + 2 * Hmixed v b * x * y + Hdiag b v * y ^ 2 := by
  by_cases hsmall : v + b ≤ 1
  · have h := B_OAS (z := 2 * b) (w := v - b) (by linarith) (by linarith)
      (by linarith) x y
    have hvrep : (2 * b) / 2 + (v - b) = v := by ring
    have hbrep : (2 * b) / 2 = b := by ring
    simpa only [hvrep, hbrep, show b + (v - b) = v by ring] using h
  · by_cases hv1 : v ≤ 1
    · by_cases hbhalf : b ≤ 1 / 2
      · have h := B_ASE (z := 2 * (1 - v)) (w := 1 - 2 * b) (by linarith) (by linarith)
          (by linarith) x y
        have hvrep : 1 - (2 * (1 - v)) / 2 = v := by ring
        have hbrep : (1 - (1 - 2 * b)) / 2 = b := by ring
        simpa only [hvrep, hbrep] using h
      · have h := B_ACE (z := 2 * (1 - v)) (w := 2 * b - 1) (by linarith) (by linarith)
          (by linarith) x y
        have hvrep : 1 - (2 * (1 - v)) / 2 = v := by ring
        have hbrep : (1 + (2 * b - 1)) / 2 = b := by ring
        simpa only [hvrep, hbrep] using h
    · by_cases hbhalf : b ≤ 1 / 2
      · by_cases hdiag : v - b ≤ 1
        · have h := B_SBE (z := 1 - 2 * b) (w := 2 * (v - 1)) (by linarith) (by linarith)
            (by linarith) x y
          have hvrep : 1 + (2 * (v - 1)) / 2 = v := by ring
          have hbrep : (1 - (1 - 2 * b)) / 2 = b := by ring
          simpa only [hvrep, hbrep] using h
        · have h := B_SUB (z := 2 - v - b) (w := v - b - 1) (by linarith) (by linarith)
            (by linarith) x y
          have hvrep : (3 - (2 - v - b) + (v - b - 1)) / 2 = v := by ring
          have hbrep : (1 - (2 - v - b) - (v - b - 1)) / 2 = b := by ring
          simpa only [hvrep, hbrep] using h
      · have h := B_CBE (z := 2 * b - 1) (w := 2 * (v - 1)) (by linarith) (by linarith)
          (by linarith) x y
        have hvrep : 1 + (2 * (v - 1)) / 2 = v := by ring
        have hbrep : (1 + (2 * b - 1)) / 2 = b := by ring
        simpa only [hvrep, hbrep] using h

end

end PositiveEinsteinFour.Quadratic
end


section

/-! The quadratic coupling bound (22), derived from the finite matrix certificate. -/

namespace PositiveEinsteinFour.Quadratic

open Potential

noncomputable section

private theorem denominator_pos (v b : ℝ) : 0 < denominator v b := by
  unfold denominator
  positivity

private theorem radialDenominator_pos {v : ℝ} (hv : 0 ≤ v) :
    0 < radialDenominator v := by
  unfold radialDenominator
  positivity

private theorem denominator_swap (v b : ℝ) : denominator b v = denominator v b := by
  unfold denominator
  ring

private theorem diagonalDifference_eq {v b : ℝ} (hv : 0 < v) :
    diagonalDifference v b = Hdiag v b / (v * denominator v b * radialDenominator v) := by
  have hK := denominator_pos v b
  have hr := radialDenominator_pos hv.le
  unfold diagonalDifference quadraticCoefficient normWeight Hdiag
  unfold denominator radialDenominator at *
  field_simp
  ring

private theorem mixedCoefficient_eq (v b : ℝ) :
    mixedCoefficient v b = mixedNumerator v b / denominator v b := by
  have hK := denominator_pos v b
  unfold mixedCoefficient mixedNumerator
  field_simp

private theorem Sbound_sq (v b : ℝ) :
    v * b * radialDenominator v * radialDenominator b ≤ Sbound v b ^ 2 := by
  have hid : Sbound v b ^ 2 - v * b * radialDenominator v * radialDenominator b =
      ((5 / 4) * b * radialDenominator v - (4 / 5) * v * radialDenominator b) ^ 2 / 4 := by
    unfold Sbound radialDenominator
    ring
  have hnonneg : 0 ≤
      ((5 / 4) * b * radialDenominator v - (4 / 5) * v * radialDenominator b) ^ 2 / 4 := by
    positivity
  linarith

private theorem quotient_matrix_nonneg {v b : ℝ}
    (hv : 0 < v) (hb : 0 < b) (horder : b ≤ v) (hsum : v + b ≤ 2) (x y : ℝ) :
    0 ≤ (Hdiag v b / (v * denominator v b * radialDenominator v)) * x ^ 2 -
      2 * (mixedNumerator v b / denominator v b) * x * y +
      (Hdiag b v / (b * denominator v b * radialDenominator b)) * y ^ 2 := by
  obtain ⟨hH1, hH2, hdet⟩ := quadratic_form_det_of_nonneg
    (Hdiag v b) (Hdiag b v) (Hmixed v b)
    (coupling_matrix_nonneg hb.le horder hsum)
  have hK := denominator_pos v b
  have hrv := radialDenominator_pos hv.le
  have hrb := radialDenominator_pos hb.le
  have hd1 : 0 < v * denominator v b * radialDenominator v := by positivity
  have hd2 : 0 < b * denominator v b * radialDenominator b := by positivity
  have hcore : (v * b * radialDenominator v * radialDenominator b) *
      mixedNumerator v b ^ 2 ≤ Hdiag v b * Hdiag b v := by
    calc
      _ ≤ Sbound v b ^ 2 * mixedNumerator v b ^ 2 :=
        mul_le_mul_of_nonneg_right (Sbound_sq v b) (sq_nonneg _)
      _ = Hmixed v b ^ 2 := by unfold Hmixed; ring
      _ ≤ _ := hdet
  have hdet' : (mixedNumerator v b / denominator v b) ^ 2 ≤
      (Hdiag v b / (v * denominator v b * radialDenominator v)) *
      (Hdiag b v / (b * denominator v b * radialDenominator b)) := by
    rw [div_mul_div_comm]
    apply (le_div_iff₀ (mul_pos hd1 hd2)).2
    have hid : (mixedNumerator v b / denominator v b) ^ 2 *
        ((v * denominator v b * radialDenominator v) *
          (b * denominator v b * radialDenominator b)) =
        (v * b * radialDenominator v * radialDenominator b) * mixedNumerator v b ^ 2 := by
      field_simp
    rwa [hid]
  have h := quadratic_form_nonneg_of_det
    (Hdiag v b / (v * denominator v b * radialDenominator v))
    (Hdiag b v / (b * denominator v b * radialDenominator b))
    (-(mixedNumerator v b / denominator v b))
    (div_nonneg hH1 hd1.le) (div_nonneg hH2 hd2.le)
    (by simpa only [neg_sq] using hdet') x y
  nlinarith only [h]

private theorem ordered_quadratic_bound {v b : ℝ}
    (hv : 0 < v) (hb : 0 < b) (horder : b ≤ v) (hsum : v + b ≤ 2) (x y : ℝ) :
    quadraticCoefficient v b * x ^ 2 + 2 * mixedCoefficient v b * x * y +
      quadraticCoefficient b v * y ^ 2 ≤
      2 * theta v b * (normWeight v * x ^ 2 + normWeight b * y ^ 2) := by
  have h := quotient_matrix_nonneg hv hb horder hsum x y
  rw [← diagonalDifference_eq hv] at h
  rw [← denominator_swap v b, ← diagonalDifference_eq hb, denominator_swap v b,
    ← mixedCoefficient_eq] at h
  unfold diagonalDifference at h
  rw [Boundary.theta_swap v b] at h
  nlinarith only [h]

/-- The scalar quadratic-form inequality (22) on the positive part of the
spectral triangle. The result is symmetric, although its finite certificate
was verified on the half with the first block larger. -/
theorem quadratic_bound {v b : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hsum : v + b ≤ 2) (x y : ℝ) :
    quadraticCoefficient v b * x ^ 2 + 2 * mixedCoefficient v b * x * y +
      quadraticCoefficient b v * y ^ 2 ≤
      2 * theta v b * (normWeight v * x ^ 2 + normWeight b * y ^ 2) := by
  rcases le_total b v with horder | horder
  · exact ordered_quadratic_bound hv hb horder hsum x y
  · have h := ordered_quadratic_bound hb hv horder (by linarith) y x
    rw [Boundary.theta_swap v b] at h
    have hmid : mixedCoefficient b v = mixedCoefficient v b := by
      unfold mixedCoefficient
      rw [denominator_swap]
      ring
    rw [hmid] at h
    nlinarith only [h]

private theorem zero_second_diagonal_bound {v : ℝ} (hv : 0 < v) (hv2 : v ≤ 2) (x : ℝ) :
    quadraticCoefficient v 0 * x ^ 2 ≤ 2 * theta v 0 * normWeight v * x ^ 2 := by
  have h := coupling_matrix_nonneg (v := v) (b := 0) (by norm_num) hv.le (by simpa) 1 0
  have hH : 0 ≤ Hdiag v 0 := by simpa using h
  have hd : 0 ≤ diagonalDifference v 0 := by
    rw [diagonalDifference_eq hv]
    exact div_nonneg hH (by
      exact le_of_lt (mul_pos (mul_pos hv (denominator_pos v 0))
        (radialDenominator_pos hv.le)))
  have hm := mul_nonneg hd (sq_nonneg x)
  unfold diagonalDifference at hm
  nlinarith only [hm]

/-- Equation (22) on the closed spectral triangle, using the zero-set
convention that derivative entries vanish with their Weyl norm. No continuity
of a coefficient containing `1/v` or `1/b` is asserted. -/
theorem quadratic_bound_closed {v b : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2) (x y : ℝ)
    (hx : v = 0 → x = 0) (hy : b = 0 → y = 0) :
    quadraticCoefficient v b * x ^ 2 + 2 * mixedCoefficient v b * x * y +
      quadraticCoefficient b v * y ^ 2 ≤
      2 * theta v b * (normWeight v * x ^ 2 + normWeight b * y ^ 2) := by
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · have hvzero : v = 0 := hv0.symm
    subst v
    have hxzero := hx rfl
    subst x
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · have hbzero : b = 0 := hb0.symm
      subst b
      have hyzero := hy rfl
      subst y
      simp
    · have h := zero_second_diagonal_bound hbpos (by simpa using hsum) y
      rw [Boundary.theta_swap 0 b] at h
      simpa [mul_assoc] using h
  · rcases eq_or_lt_of_le hb with hb0 | hbpos
    · have hbzero : b = 0 := hb0.symm
      subst b
      have hyzero := hy rfl
      subst y
      have h := zero_second_diagonal_bound hvpos (by simpa using hsum) x
      simpa [mul_assoc] using h
    · exact quadratic_bound hvpos hbpos hsum x y

end

end PositiveEinsteinFour.Quadratic
end


section

/-!
# Assembly of the scalar integrand bounds

The quartic, quadratic, and potential estimates bound the scalar integrand.
The tangent pairing is the real inner product.
-/

namespace PositiveEinsteinFour

open Energy QuarticEnergy QuarticClosed Quadratic Boundary Potential

noncomputable section

/-- The scalar quadratic estimate also holds for tangent vectors, with their
actual pairing. The proof chooses the sign of a scalar test vector according
to the sign of the mixed coefficient. -/
theorem hilbert_quadratic_bound_closed_oai
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v b : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
    (p q : E) (hp : v = 0 → p = 0) (hq : b = 0 → q = 0) :
    quadraticCoefficient v b * ‖p‖ ^ 2 + 2 * mixedCoefficient v b * inner ℝ p q +
      quadraticCoefficient b v * ‖q‖ ^ 2 ≤
      2 * theta v b * (normWeight v * ‖p‖ ^ 2 + normWeight b * ‖q‖ ^ 2) := by
  have habs := abs_real_inner_le_norm p q
  have hlo := (abs_le.mp habs).1
  have hhi := (abs_le.mp habs).2
  by_cases hJ : 0 ≤ mixedCoefficient v b
  · have hscalar := quadratic_bound_closed hv hb hsum ‖p‖ ‖q‖
      (by intro h; simp [hp h]) (by intro h; simp [hq h])
    have hcross := mul_le_mul_of_nonneg_left hhi
      (show 0 ≤ 2 * mixedCoefficient v b by positivity)
    nlinarith only [hscalar, hcross]
  · have hscalar := quadratic_bound_closed hv hb hsum ‖p‖ (-‖q‖)
      (by intro h; simp [hp h]) (by intro h; simp [hq h])
    have hcross := mul_le_mul_of_nonpos_left hlo
      (show 2 * mixedCoefficient v b ≤ 0 by linarith)
    nlinarith only [hscalar, hcross]

end
end PositiveEinsteinFour
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.hilbert_quadratic_bound_closed_oai.{u_1} := @OAI.PositiveEinsteinFour.hilbert_quadratic_bound_closed_oai.{u_1}
