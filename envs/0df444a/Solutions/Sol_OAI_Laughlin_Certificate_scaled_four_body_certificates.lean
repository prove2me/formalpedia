-- Prove2me | solution 1 for OAI.Laughlin.Certificate.scaled_four_body_certificates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:54:36.562165+00:00
-- url     : https://prove2.me/submissions/f3d8a9e2-edec-499a-bbb5-bd48daafc896

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_10_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_11_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_12_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_13_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_14_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_15_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_16_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_17_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_18_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_19_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_20_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_21_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_22_positive
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_9_positive
import Theorems.Thm_OAI_Laughlin_Certificate_ldl_23
import Theorems.Thm_OAI_Laughlin_Certificate_ldl_7
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_1_0
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_1_1
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_1_2
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_1_3
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_1_4
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_1_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_1_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_3_0
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_3_1
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_3_2
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_3_3
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_3_4
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_3_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_3_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_1_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_3_1_0
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_3_1_2
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_3_1_4
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_3_1_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_3_3_1
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_3_3_2
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_3_3_4
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_3_3_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_3_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_3_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_3_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_5_1_0
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_5_1_2
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_5_1_4
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_5_1_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_5_3_0
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_5_3_2
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_5_3_4
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_5_3_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_5_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_5_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_5_5_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_1_0
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_1_1
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_1_3
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_1_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_3_0
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_3_2
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_3_4
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_3_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_5_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_1_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_3_3_0
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_3_3_2
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_3_3_4
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_3_3_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_3_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_3_5_2
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_3_5_4
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_3_5_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_3_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_3_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_3_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_5_5_0
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_5_5_2
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_5_5_4
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_5_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_5_7_0
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_5_7_2
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_5_7_4
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_5_7_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_7_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_7_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_8_7_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_eq_integral

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators Matrix

theorem Y_expand (D r s : ℕ) : Y D r s =
    -(yRow D r s (rows[0]!) + (yRow D r s (rows[1]!) +
      (yRow D r s (rows[2]!) + (yRow D r s (rows[3]!) +
        (yRow D r s (rows[4]!) + (yRow D r s (rows[5]!) +
          (yRow D r s (rows[6]!) + 0))))))) / (10^14 : ℚ) := by rfl


theorem gram_five : gramRational 5 =
    !![48, -24, 60; -24, 12, -30; 60, -30, 75] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_5_1_5_0 : yRow 5 1 5 (rows[0]!) = (517229739078330765 / 4096 : ℚ) := by
  decide +kernel

theorem yRow_5_1_5_2 : yRow 5 1 5 (rows[2]!) = (-39698825671225989422295 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_1_5_4 : yRow 5 1 5 (rows[4]!) = (-18686933965106262007505 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_1_5_6 : yRow 5 1 5 (rows[6]!) = (122766324303368643735 / 67108864 : ℚ) := by
  decide +kernel

theorem yRow_5_3_1_1 : yRow 5 3 1 (rows[1]!) = (-40217208208139155215 / 469762048 : ℚ) := by
  decide +kernel

theorem yRow_5_3_1_3 : yRow 5 3 1 (rows[3]!) = (15972179718835785494373 / 469762048 : ℚ) := by
  decide +kernel

theorem yRow_5_3_1_5 : yRow 5 3 1 (rows[5]!) = (8556207819014717270965 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_3_3_0 : yRow 5 3 3 (rows[0]!) = (828106156763491761 / 16384 : ℚ) := by
  decide +kernel

theorem yRow_5_3_3_3 : yRow 5 3 3 (rows[3]!) = (885506700796361417871 / 234881024 : ℚ) := by
  decide +kernel

theorem yRow_5_3_3_5 : yRow 5 3 3 (rows[5]!) = (10662554367612487256863 / 268435456 : ℚ) := by
  decide +kernel

theorem yRow_5_3_5_0 : yRow 5 3 5 (rows[0]!) = (2088880360412782875 / 8192 : ℚ) := by
  decide +kernel

theorem yRow_5_3_5_2 : yRow 5 3 5 (rows[2]!) = (4154519314999427044985 / 469762048 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row052
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_5_3_5_4 : yRow 5 3 5 (rows[4]!) = (1122516649266680657945 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_3_5_6 : yRow 5 3 5 (rows[6]!) = (-125595578390684976075 / 67108864 : ℚ) := by
  decide +kernel

theorem yRow_5_5_1_1 : yRow 5 5 1 (rows[1]!) = (33354143675585625297 / 234881024 : ℚ) := by
  decide +kernel

theorem yRow_5_5_1_3 : yRow 5 5 1 (rows[3]!) = (-24352127547028721893585 / 234881024 : ℚ) := by
  decide +kernel

theorem yRow_5_5_1_6 : yRow 5 5 1 (rows[6]!) = (122766324303368643735 / 67108864 : ℚ) := by
  decide +kernel

theorem yRow_5_5_3_1 : yRow 5 5 3 (rows[1]!) = (9078017688703880489 / 117440512 : ℚ) := by
  decide +kernel

theorem yRow_5_5_3_3 : yRow 5 5 3 (rows[3]!) = (-1676596742006268315615 / 117440512 : ℚ) := by
  decide +kernel

theorem yRow_5_5_3_5 : yRow 5 5 3 (rows[5]!) = (11113921888615690197695 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_5_5_0 : yRow 5 5 5 (rows[0]!) = (2127370824716077635 / 2048 : ℚ) := by
  decide +kernel

theorem yRow_5_5_5_2 : yRow 5 5 5 (rows[2]!) = (79674709640186975436905 / 234881024 : ℚ) := by
  decide +kernel

theorem yRow_5_5_5_4 : yRow 5 5 5 (rows[4]!) = (35865503886652808531045 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_5_5_6 : yRow 5 5 5 (rows[6]!) = (-465607554421578820545 / 67108864 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Error05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem error_five_11 : Y 5 1 1 = (-131383098735399323103/3355443200000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_1_1_0, yRow_5_1_1_1, yRow_5_1_1_2, yRow_5_1_1_3, yRow_5_1_1_4, yRow_5_1_1_5, yRow_5_1_1_6]
  norm_num

theorem error_five_13 : Y 5 1 3 = (-150940901726840366220441/187904819200000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_1_3_0, yRow_5_1_3_1, yRow_5_1_3_2, yRow_5_1_3_3, yRow_5_1_3_4, yRow_5_1_3_5, yRow_5_1_3_6]
  norm_num

theorem error_five_15 : Y 5 1 5 = (-68371964800993572891617/375809638400000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_1_5_0, yRow_5_1_5_1, yRow_5_1_5_2, yRow_5_1_5_3, yRow_5_1_5_4, yRow_5_1_5_5, yRow_5_1_5_6]
  norm_num

theorem error_five_31 : Y 5 3 1 = (-150940901726840366220441/187904819200000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_3_1_0, yRow_5_3_1_1, yRow_5_3_1_2, yRow_5_3_1_3, yRow_5_3_1_4, yRow_5_3_1_5, yRow_5_3_1_6]
  norm_num

theorem error_five_33 : Y 5 3 3 = (-157876378364069020620837/187904819200000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_3_3_0, yRow_5_3_3_1, yRow_5_3_3_2, yRow_5_3_3_3, yRow_5_3_3_4, yRow_5_3_3_5, yRow_5_3_3_6]
  norm_num

theorem error_five_35 : Y 5 3 5 = (-957095703323798289717/367001600000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_3_5_0, yRow_5_3_5_1, yRow_5_3_5_2, yRow_5_3_5_3, yRow_5_3_5_4, yRow_5_3_5_5, yRow_5_3_5_6]
  norm_num

theorem error_five_51 : Y 5 5 1 = (-68371964800993572891617/375809638400000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_5_1_0, yRow_5_5_1_1, yRow_5_5_1_2, yRow_5_5_1_3, yRow_5_5_1_4, yRow_5_5_1_5, yRow_5_5_1_6]
  norm_num

theorem error_five_53 : Y 5 5 3 = (-957095703323798289717/367001600000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_5_3_0, yRow_5_5_3_1, yRow_5_5_3_2, yRow_5_5_3_3, yRow_5_5_3_4, yRow_5_5_3_5, yRow_5_5_3_6]
  norm_num

theorem error_five_55 : Y 5 5 5 = (-6732043280507644550567857/375809638400000000000000 : ℚ) := by
  rw [Y_expand, yRow_5_5_5_0, yRow_5_5_5_1, yRow_5_5_5_2, yRow_5_5_5_3, yRow_5_5_5_4, yRow_5_5_5_5, yRow_5_5_5_6]
  norm_num
theorem error_five : errorRational 5 =
    !![-131383098735399323103/3355443200000000000000, -150940901726840366220441/187904819200000000000000, -68371964800993572891617/375809638400000000000000;
      -150940901726840366220441/187904819200000000000000, -157876378364069020620837/187904819200000000000000, -957095703323798289717/367001600000000000000;
      -68371964800993572891617/375809638400000000000000, -957095703323798289717/367001600000000000000, -6732043280507644550567857/375809638400000000000000] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact error_five_11
  · exact error_five_13
  · exact error_five_15
  · exact error_five_31
  · exact error_five_33
  · exact error_five_35
  · exact error_five_51
  · exact error_five_53
  · exact error_five_55

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Integral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem rows_integral_bounds : ∀ row ∈ rows, row.1 ≤ 16 ∧
    ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      e.1 + e.2.1 + (f.1 + f.2.1 - row.1) ≤ 24 := by
  decide +kernel

theorem source_yRow_eq_integral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegral D r s (rows[n]!) : ℚ) / arithmeticScale := by
  have hm : rows[n]! ∈ rows := by
    interval_cases n <;> decide +kernel
  exact yRow_eq_integral D r s _ (rows_integral_bounds _ hm).1 (rows_integral_bounds _ hm).2

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_8_1_1_2 : yRow 8 1 1 (rows[2]!) = (-9136760184633772519965/33554432 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 1 2 (by decide)]
  have h : yRowIntegral 8 1 1 (rows[2]!) = (-3116504275684753840824333987016605727399506032669491200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_1_4 : yRow 8 1 1 (rows[4]!) = (14597567158110194070375/16777216 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 1 4 (by decide)]
  have h : yRowIntegral 8 1 1 (rows[4]!) = (9958317728281114061683907653004378575256490564648960000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_1_6 : yRow 8 1 1 (rows[6]!) = (-8205115144686782088375/16777216 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 1 6 (by decide)]
  have h : yRowIntegral 8 1 1 (rows[6]!) = (-5597449405295309043794642493309726317975774366269440000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_3_1 : yRow 8 1 3 (rows[1]!) = (197119650262423977/524288 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 3 1 (by decide)]
  have h : yRowIntegral 8 1 3 (rows[1]!) = (4303139199104731278274793995541665105689055372247040000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_3_3 : yRow 8 1 3 (rows[3]!) = (15064379418747419024745/33554432 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 3 3 (by decide)]
  have h : yRowIntegral 8 1 3 (rows[3]!) = (5138386246365681146408405211272447483086217886144921600000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_3_5 : yRow 8 1 3 (rows[5]!) = (-6630239381949782627055/16777216 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 3 5 (by decide)]
  have h : yRowIntegral 8 1 3 (rows[5]!) = (-4523084543120943521189449142964840775985106302848204800000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_5_0 : yRow 8 1 5 (rows[0]!) = (-14645438327407983795/2048 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 5 0 (by decide)]
  have h : yRowIntegral 8 1 5 (rows[0]!) = (-81846066973714198535257051527707951684592003606537830400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_5_2 : yRow 8 1 5 (rows[2]!) = (-35901747833688299761245/8388608 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 5 2 (by decide)]
  have h : yRowIntegral 8 1 5 (rows[2]!) = (-48983643377843663525738690465967873761696349774308966400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_5_4 : yRow 8 1 5 (rows[4]!) = (-102541802088869818905/2097152 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 5 4 (by decide)]
  have h : yRowIntegral 8 1 5 (rows[4]!) = (-559624126169080528107859221332441491696940415870566400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_7_0 : yRow 8 1 7 (rows[0]!) = (-29482763785841653245/2048 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 7 0 (by decide)]
  have h : yRowIntegral 8 1 7 (rows[0]!) = (-164764495636182421456560607435114239038750987318093414400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_7_2 : yRow 8 1 7 (rows[2]!) = (-825991533879872150445/4194304 : ℚ) := by
  rw [source_yRow_eq_integral 8 1 7 2 (by decide)]
  have h : yRowIntegral 8 1 7 (rows[2]!) = (-2253933424975156060465058265096229214598307691416780800000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_FastChoose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem U_eq_fast (c z T p : ℕ) : U c z T p = UFast c z T p := by
  simp only [U, UFast, Nat.choose_eq_fast_choose]

theorem V_eq_fast (r D T p j k : ℕ) : V r D T p j k = VFast r D T p j k := by
  simp only [V, VFast, U_eq_fast]

theorem yEntryIntegral_eq_fast (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    yEntryIntegral D r s t e f = yEntryIntegralFast D r s t e f := by
  simp only [yEntryIntegral, yEntryIntegralFast, V_eq_fast]

theorem yRowIntegral_eq_fast (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    yRowIntegral D r s row = yRowIntegralFast D r s row := by
  simp only [yRowIntegral, yRowIntegralFast, yEntryIntegral_eq_fast]

theorem source_yRow_eq_fastIntegral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegralFast D r s (rows[n]!) : ℚ) / arithmeticScale := by
  rw [source_yRow_eq_integral D r s n hn, yRowIntegral_eq_fast]

theorem L_eq_fast (D r : ℕ) (A : ℕ × ℕ × ℕ × ℕ) : L D r A = LFast D r A := by
  simp only [L, LFast, V_eq_fast]

theorem Z_eq_fast (D r s : ℕ) : Z D r s = ZFast D r s := by
  simp only [Z, ZFast, L_eq_fast]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row082
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_8_1_7_4 : yRow 8 1 7 (rows[4]!) = (898662178057610818425/8388608 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 1 7 4 (by decide)]
  have h : yRowIntegralFast 8 1 7 (rows[4]!) = (1226117119730434135579945337146359789819184929570816000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_1_7_6 : yRow 8 1 7 (rows[6]!) = (139637915427504113235/1048576 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 1 7 6 (by decide)]
  have h : yRowIntegralFast 8 1 7 (rows[6]!) = (1524153951058190208281381424542084824467012314569113600000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_3_1 : yRow 8 3 3 (rows[1]!) = (3142036540605854661/2097152 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 3 1 (by decide)]
  have h : yRowIntegralFast 8 3 3 (rows[1]!) = (17147733096244555833634088409268874847094058967367680000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_3_3 : yRow 8 3 3 (rows[3]!) = (-18744793144766932510845/16777216 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 3 3 (by decide)]
  have h : yRowIntegralFast 8 3 3 (rows[3]!) = (-12787514786858549425344796377195048608240794860729139200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_3_5 : yRow 8 3 3 (rows[5]!) = (32391427003169138594775/234881024 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 3 5 (by decide)]
  have h : yRowIntegralFast 8 3 3 (rows[5]!) = (1578365364761537085254234510698954482866065816682496000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_5_0 : yRow 8 3 5 (rows[0]!) = (76640875416000675/1024 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 5 0 (by decide)]
  have h : yRowIntegralFast 8 3 5 (rows[0]!) = (856615429595306325025256914923187604516818661670912000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_5_3 : yRow 8 3 5 (rows[3]!) = (702428309218164239085/8388608 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 5 3 (by decide)]
  have h : yRowIntegralFast 8 3 5 (rows[3]!) = (958379462655522227776546507336903612321559804588851200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_5_5 : yRow 8 3 5 (rows[5]!) = (20424443618431088962035/58720256 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 5 5 (by decide)]
  have h : yRowIntegralFast 8 3 5 (rows[5]!) = (3980958838115082923031199520266531892326567020960153600000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_7_0 : yRow 8 3 7 (rows[0]!) = (1990312643635120665/2048 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 7 0 (by decide)]
  have h : yRowIntegralFast 8 3 7 (rows[0]!) = (11122866949276273240494885445024757470322608040627404800000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_7_2 : yRow 8 3 7 (rows[2]!) = (11311749600528369600555/2097152 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 7 2 (by decide)]
  have h : yRowIntegralFast 8 3 7 (rows[2]!) = (61734120687218218053787138616255934133213958544713318400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_7_4 : yRow 8 3 7 (rows[4]!) = (3519874183592373572895/16777216 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 7 4 (by decide)]
  have h : yRowIntegralFast 8 3 7 (rows[4]!) = (2401223786411049713220922466624398209967081271800627200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_3_7_6 : yRow 8 3 7 (rows[6]!) = (672523966016989221555/4194304 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 3 7 6 (by decide)]
  have h : yRowIntegralFast 8 3 7 (rows[6]!) = (1835157121989341670710322442697238660354473731502899200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_5_5_1 : yRow 8 5 5 (rows[1]!) = (2321948566914231201/524288 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 5 5 1 (by decide)]
  have h : yRowIntegralFast 8 5 5 (rows[1]!) = (50688340220225875834055464782591602111445800079851520000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_5_5_3 : yRow 8 5 5 (rows[3]!) = (2894465599178455021275/4194304 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 5 5 3 (by decide)]
  have h : yRowIntegralFast 8 5 5 (rows[3]!) = (7898304636107648937531058100797533823195362870951936000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row083
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_8_5_5_6 : yRow 8 5 5 (rows[6]!) = (14119266506282124255/2097152 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 5 5 6 (by decide)]
  have h : yRowIntegralFast 8 5 5 (rows[6]!) = (77056205564619678704021234047790246774509031286374400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_5_7_1 : yRow 8 5 7 (rows[1]!) = (265856006788524411/16384 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 5 7 1 (by decide)]
  have h : yRowIntegralFast 8 5 7 (rows[1]!) = (185717115890761117907991264301533337132741044511703040000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_5_7_3 : yRow 8 5 7 (rows[3]!) = (-6216612413350207898295/2097152 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 5 7 3 (by decide)]
  have h : yRowIntegralFast 8 5 7 (rows[3]!) = (-33927298123138660043769111171450955625046914576783769600000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_5_7_5 : yRow 8 5 7 (rows[5]!) = (-26878866420346632296175/33554432 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 5 7 5 (by decide)]
  have h : yRowIntegralFast 8 5 7 (rows[5]!) = (-9168250061487993259349020436235780108988519047757824000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_7_7_0 : yRow 8 7 7 (rows[0]!) = (42321625347011687775/512 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 7 7 0 (by decide)]
  have h : yRowIntegralFast 8 7 7 (rows[0]!) = (946058016196230415752027336404918886222132921218629632000000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_7_7_2 : yRow 8 7 7 (rows[2]!) = (20829685222835364120795/524288 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 7 7 2 (by decide)]
  have h : yRowIntegralFast 8 7 7 (rows[2]!) = (454713849522701608096165768651365279143842787883378278400000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_7_7_4 : yRow 8 7 7 (rows[4]!) = (-1243929398768283753645/4194304 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 7 7 4 (by decide)]
  have h : yRowIntegralFast 8 7 7 (rows[4]!) = (-3394385941249665107509736601572607530416212886211788800000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

theorem yRow_8_7_7_6 : yRow 8 7 7 (rows[6]!) = (-466714964291950350585/524288 : ℚ) := by
  rw [source_yRow_eq_fastIntegral 8 7 7 6 (by decide)]
  have h : yRowIntegralFast 8 7 7 (rows[6]!) = (-10188428474684124940652669537868107900326856055010099200000 : ℤ) := by
    decide +kernel
  rw [h]
  norm_num [arithmeticScale, Nat.factorial]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Symmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yEntry_swap (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (he : t ≤ e.1 + e.2.1) (hf : t ≤ f.1 + f.2.1) :
    yEntry D r s t e f = yEntry D s r t f e := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp at he hf
  have hT : q+l+(p+j-t) = p+j+(q+l-t) := by omega
  simp only [yEntry, hT, Nat.add_comm s r]
  split_ifs <;> ring_nf

private theorem sum_add {Element : Type*} (xs : List Element) (f g : Element → ℚ) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem sum_swap {Element : Type*} (xs ys : List Element)
    (f : Element → Element → ℚ) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, sum_add]

theorem yRow_swap (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (h : ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1) :
    yRow D r s row = yRow D s r row := by
  unfold yRow
  rw [sum_swap]
  congr 1
  apply List.map_congr_left
  intro f hf
  congr 1
  apply List.map_congr_left
  intro e he
  exact yEntry_swap D r s row.1 e f (h e he) (h f hf)

theorem rows_valid : ∀ row ∈ rows, ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1 := by
  decide +kernel

theorem Y_symm (D r s : ℕ) : Y D r s = Y D s r := by
  unfold Y
  congr 3
  apply List.map_congr_left
  intro row hr
  exact yRow_swap D r s row (rows_valid row hr)

theorem Z_symm (D r s : ℕ) : Z D r s = Z D s r := by
  unfold Z
  congr 1
  apply List.map_congr_left
  intro A hA
  dsimp
  ring

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Error08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem error_8_1_1 : Y 8 1 1 = (-67460768130800149252179/3355443200000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_1_1_0, yRow_8_1_1_1, yRow_8_1_1_2, yRow_8_1_1_3, yRow_8_1_1_4, yRow_8_1_1_5, yRow_8_1_1_6]
  norm_num

theorem error_8_1_3 : Y 8 1 3 = (-12646981826519267475639/1677721600000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_1_3_0, yRow_8_1_3_1, yRow_8_1_3_2, yRow_8_1_3_3, yRow_8_1_3_4, yRow_8_1_3_5, yRow_8_1_3_6]
  norm_num

theorem error_8_1_5 : Y 8 1 5 = (862312946559627131048937/6710886400000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_1_5_0, yRow_8_1_5_1, yRow_8_1_5_2, yRow_8_1_5_3, yRow_8_1_5_4, yRow_8_1_5_5, yRow_8_1_5_6]
  norm_num

theorem error_8_1_7 : Y 8 1 7 = (145152021796677708235047/3355443200000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_1_7_0, yRow_8_1_7_1, yRow_8_1_7_2, yRow_8_1_7_3, yRow_8_1_7_4, yRow_8_1_7_5, yRow_8_1_7_6]
  norm_num

theorem error_8_3_3 : Y 8 3 3 = (-227609666383850988434007/23488102400000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_3_3_0, yRow_8_3_3_1, yRow_8_3_3_2, yRow_8_3_3_3, yRow_8_3_3_4, yRow_8_3_3_5, yRow_8_3_3_6]
  norm_num

theorem error_8_3_5 : Y 8 3 5 = (-285716550006646092887421/23488102400000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_3_5_0, yRow_8_3_5_1, yRow_8_3_5_2, yRow_8_3_5_3, yRow_8_3_5_4, yRow_8_3_5_5, yRow_8_3_5_6]
  norm_num

theorem error_8_3_7 : Y 8 3 7 = (-140429284546716888797613/1677721600000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_3_7_0, yRow_8_3_7_1, yRow_8_3_7_2, yRow_8_3_7_3, yRow_8_3_7_4, yRow_8_3_7_5, yRow_8_3_7_6]
  norm_num

theorem error_8_5_5 : Y 8 5 5 = (1048952949137524188240279/46976204800000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_5_5_0, yRow_8_5_5_1, yRow_8_5_5_2, yRow_8_5_5_3, yRow_8_5_5_4, yRow_8_5_5_5, yRow_8_5_5_6]
  norm_num

theorem error_8_5_7 : Y 8 5 7 = (707573349496458024998847/3355443200000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_5_7_0, yRow_8_5_7_1, yRow_8_5_7_2, yRow_8_5_7_3, yRow_8_5_7_4, yRow_8_5_7_5, yRow_8_5_7_6]
  norm_num

theorem error_8_7_7 : Y 8 7 7 = (-2475302483264003426615343/1677721600000000000000 : ℚ) := by
  rw [Y_expand, yRow_8_7_7_0, yRow_8_7_7_1, yRow_8_7_7_2, yRow_8_7_7_3, yRow_8_7_7_4, yRow_8_7_7_5, yRow_8_7_7_6]
  norm_num

theorem error_8_3_1 : Y 8 3 1 = (-12646981826519267475639/1677721600000000000000 : ℚ) := by
  rw [Y_symm]
  exact error_8_1_3

theorem error_8_5_1 : Y 8 5 1 = (862312946559627131048937/6710886400000000000000 : ℚ) := by
  rw [Y_symm]
  exact error_8_1_5

theorem error_8_5_3 : Y 8 5 3 = (-285716550006646092887421/23488102400000000000000 : ℚ) := by
  rw [Y_symm]
  exact error_8_3_5

theorem error_8_7_1 : Y 8 7 1 = (145152021796677708235047/3355443200000000000000 : ℚ) := by
  rw [Y_symm]
  exact error_8_1_7

theorem error_8_7_3 : Y 8 7 3 = (-140429284546716888797613/1677721600000000000000 : ℚ) := by
  rw [Y_symm]
  exact error_8_3_7

theorem error_8_7_5 : Y 8 7 5 = (707573349496458024998847/3355443200000000000000 : ℚ) := by
  rw [Y_symm]
  exact error_8_5_7
theorem error_8 : errorRational 8 =
    !![-67460768130800149252179/3355443200000000000000, -12646981826519267475639/1677721600000000000000, 862312946559627131048937/6710886400000000000000, 145152021796677708235047/3355443200000000000000;
      -12646981826519267475639/1677721600000000000000, -227609666383850988434007/23488102400000000000000, -285716550006646092887421/23488102400000000000000, -140429284546716888797613/1677721600000000000000;
      862312946559627131048937/6710886400000000000000, -285716550006646092887421/23488102400000000000000, 1048952949137524188240279/46976204800000000000000, 707573349496458024998847/3355443200000000000000;
      145152021796677708235047/3355443200000000000000, -140429284546716888797613/1677721600000000000000, 707573349496458024998847/3355443200000000000000, -2475302483264003426615343/1677721600000000000000] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact error_8_1_1
  · exact error_8_1_3
  · exact error_8_1_5
  · exact error_8_1_7
  · exact error_8_3_1
  · exact error_8_3_3
  · exact error_8_3_5
  · exact error_8_3_7
  · exact error_8_5_1
  · exact error_8_5_3
  · exact error_8_5_5
  · exact error_8_5_7
  · exact error_8_7_1
  · exact error_8_7_3
  · exact error_8_7_5
  · exact error_8_7_7

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Quadruples08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem quadruples_8 : quadruples 8 = [(0,1,2,6), (0,1,3,5), (0,2,3,4)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Gram082
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem gram_8_1_1 : Z 8 1 1 = (0 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_1_3 : Z 8 1 3 = (0 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_1_5 : Z 8 1 5 = (0 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_1_7 : Z 8 1 7 = (0 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_3_3 : Z 8 3 3 = (720 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_3_5 : Z 8 3 5 = (-720 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_3_7 : Z 8 3 7 = (1260 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_5_5 : Z 8 5 5 = (720 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_5_7 : Z 8 5 7 = (-1260 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_7_7 : Z 8 7 7 = (2205 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Gram08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem gram_8 : gramRational 8 =
  !![0, 0, 0, 0;
    0, 720, -720, 1260;
    0, -720, 720, -1260;
    0, 1260, -1260, 2205] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact gram_8_1_1
  · exact gram_8_1_3
  · exact gram_8_1_5
  · exact gram_8_1_7
  · exact (Z_symm 8 3 1).trans gram_8_1_3
  · exact gram_8_3_3
  · exact gram_8_3_5
  · exact gram_8_3_7
  · exact (Z_symm 8 5 1).trans gram_8_1_5
  · exact (Z_symm 8 5 3).trans gram_8_3_5
  · exact gram_8_5_5
  · exact gram_8_5_7
  · exact (Z_symm 8 7 1).trans gram_8_1_7
  · exact (Z_symm 8 7 3).trans gram_8_3_7
  · exact (Z_symm 8 7 5).trans gram_8_5_7
  · exact gram_8_7_7

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_RationalPSD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem rational_ldl_positive {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℚ)
    (d : Fin n → ℚ) (h : A = L * Matrix.diagonal d * L.transpose)
    (hd : ∀ i, 0 ≤ d i) : (A.map (Rat.castHom ℝ)).PosSemidef := by
  rw [h, Matrix.map_mul, Matrix.map_mul]
  have hdiag : (Matrix.diagonal d).map (Rat.castHom ℝ) =
      Matrix.diagonal (fun i => (d i : ℝ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have htrans : L.transpose.map (Rat.castHom ℝ) =
      (L.map (Rat.castHom ℝ)).conjTranspose := by
    ext i j
    simp
  rw [hdiag, htrans]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℝ) ≤ (d i : ℝ)
  exact_mod_cast hd i

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem compressed_positive_of_gram_zero (D : ℕ) (h : gramRational D = 0) :
    ((compressedRational D).map (Rat.castHom ℝ)).PosSemidef := by
  have he : compressedRational D = 0 := by simp [compressedRational, h]
  rw [he]
  simpa using (Matrix.PosSemidef.zero :
    (0 : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ).PosSemidef)


theorem gram_one_zero : gramRational 1 = 0 := by decide +kernel
theorem gram_two_zero : gramRational 2 = 0 := by decide +kernel
theorem gram_three_zero : gramRational 3 = 0 := by decide +kernel
theorem gram_four_zero : gramRational 4 = 0 := by decide +kernel
theorem gram_six_zero : gramRational 6 = 0 := by decide +kernel

theorem zero_blocks_positive (D : ℕ) (hD : D ∈ [1,2,3,4,6]) :
    ((compressedRational D).map (Rat.castHom ℝ)).PosSemidef := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl
  · exact compressed_positive_of_gram_zero 1 gram_one_zero
  · exact compressed_positive_of_gram_zero 2 gram_two_zero
  · exact compressed_positive_of_gram_zero 3 gram_three_zero
  · exact compressed_positive_of_gram_zero 4 gram_four_zero
  · exact compressed_positive_of_gram_zero 6 gram_six_zero

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_MatrixCompute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate.MatrixCompute

open scoped BigOperators

theorem middle_apply (D : ℕ) (Y : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ)
    (i j : Fin ((D+1)/2)) :
    middle D Y i j =
      (if i = j then ((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ)) * copyWeight D i else 0) -
        copyWeight D i * Y i j * copyWeight D j := by
  simp only [middle, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_apply]

theorem compressed_apply (D : ℕ) (Y Z : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ)
    (i j : Fin ((D+1)/2)) :
    compressed D Y Z i j =
      ∑ k, (∑ l, Z i l *
        ((if l = k then ((if copyLabel l = 1 then 2 else 0) + (3/10^6 : ℚ)) * copyWeight D l else 0) -
          copyWeight D l * Y l k * copyWeight D k)) * Z k j := by
  simp only [compressed, Matrix.mul_apply, middle_apply]

theorem ldl_apply {n : ℕ} (L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (i j : Fin n) :
    (L * Matrix.diagonal d * L.transpose) i j = ∑ k, L i k * d k * L j k := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

end Laughlin.Certificate.MatrixCompute

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_NumericBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem compressedRational_eq_compute (D : ℕ) :
    compressedRational D = MatrixCompute.compressed D (errorRational D) (gramRational D) := by
  rfl

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_LDL08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem ldl_8_0_0 : compressedRational 8 0 0 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 0 0 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_0_1 : compressedRational 8 0 1 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 0 1 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_0_2 : compressedRational 8 0 2 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 0 2 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_0_3 : compressedRational 8 0 3 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 0 3 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_1_0 : compressedRational 8 1 0 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 1 0 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_1_1 : compressedRational 8 1 1 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 1 1 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_1_2 : compressedRational 8 1 2 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 1 2 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_1_3 : compressedRational 8 1 3 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 1 3 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_2_0 : compressedRational 8 2 0 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 2 0 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_2_1 : compressedRational 8 2 1 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 2 1 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_2_2 : compressedRational 8 2 2 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 2 2 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_2_3 : compressedRational 8 2 3 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 2 3 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_3_0 : compressedRational 8 3 0 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 3 0 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_3_1 : compressedRational 8 3 1 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 3 1 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_3_2 : compressedRational 8 3 2 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 3 2 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_3_3 : compressedRational 8 3 3 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 3 3 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix


theorem ldl_five : compressedRational 5 =
    lowerFive * Matrix.diagonal pivotsFive * lowerFive.transpose := by
  unfold compressedRational middleRational
  rw [gram_five, error_five]
  decide +kernel

theorem four_body_five_positive :
    ((compressedRational 5).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lowerFive pivotsFive ldl_five
  intro i
  fin_cases i <;> norm_num [pivotsFive]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem four_body_7_positive :
    ((compressedRational 7).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_7 pivots_7 ldl_7
  intro i
  fin_cases i <;> norm_num [pivots_7]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem ldl_8 : compressedRational 8 =
    lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact ldl_8_0_0
  · exact ldl_8_0_1
  · exact ldl_8_0_2
  · exact ldl_8_0_3
  · exact ldl_8_1_0
  · exact ldl_8_1_1
  · exact ldl_8_1_2
  · exact ldl_8_1_3
  · exact ldl_8_2_0
  · exact ldl_8_2_1
  · exact ldl_8_2_2
  · exact ldl_8_2_3
  · exact ldl_8_3_0
  · exact ldl_8_3_1
  · exact ldl_8_3_2
  · exact ldl_8_3_3
theorem four_body_8_positive :
    ((compressedRational 8).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_8 pivots_8 ldl_8
  intro i
  fin_cases i <;> norm_num [pivots_8]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem four_body_23_positive :
    ((compressedRational 23).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_23 pivots_23 ldl_23
  intro i
  fin_cases i <;> norm_num [pivots_23]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_All
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem four_body_certificates (D : ℕ) (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    ((compressedRational D).map (Rat.castHom ℝ)).PosSemidef := by
  interval_cases D
  · exact zero_blocks_positive 1 (by decide)
  · exact zero_blocks_positive 2 (by decide)
  · exact zero_blocks_positive 3 (by decide)
  · exact zero_blocks_positive 4 (by decide)
  · exact four_body_five_positive
  · exact zero_blocks_positive 6 (by decide)
  · exact four_body_7_positive
  · exact four_body_8_positive
  · exact four_body_9_positive
  · exact four_body_10_positive
  · exact four_body_11_positive
  · exact four_body_12_positive
  · exact four_body_13_positive
  · exact four_body_14_positive
  · exact four_body_15_positive
  · exact four_body_16_positive
  · exact four_body_17_positive
  · exact four_body_18_positive
  · exact four_body_19_positive
  · exact four_body_20_positive
  · exact four_body_21_positive
  · exact four_body_22_positive
  · exact four_body_23_positive

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_MatrixCongruence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem compressed_congruence_identity {n : ℕ}
    (D Z Y K : Matrix (Fin n) (Fin n) ℝ) :
    (D*Z*D) * (K-D*Y*D) * (D*Z*D) =
      D * (Z * (D*K*D-(D*D)*Y*(D*D)) * Z) * D := by
  noncomm_ring

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Scaled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem cast_rat_diagonal {n : ℕ} (v : Fin n → ℚ) :
    (Matrix.diagonal v).map (Rat.castHom ℝ) = Matrix.diagonal (fun i => (v i : ℝ)) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.map_apply,h]

theorem cast_rat_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    (A-B).map (Rat.castHom ℝ) = A.map (Rat.castHom ℝ)-B.map (Rat.castHom ℝ) := by
  ext i j
  simp [Matrix.map_apply,Matrix.sub_apply]

theorem copyWeight_nonneg (D : ℕ) (i : Fin ((D+1)/2)) : 0 ≤ (copyWeight D i : ℝ) := by
  unfold copyWeight
  positivity

theorem weightSqrtDiagonal_sq (D : ℕ) :
    weightSqrtDiagonal D * weightSqrtDiagonal D =
      (Matrix.diagonal (copyWeight D)).map (Rat.castHom ℝ) := by
  rw [weightSqrtDiagonal,Matrix.diagonal_mul_diagonal,cast_rat_diagonal]
  congr 1
  funext i
  simpa [pow_two] using Real.sq_sqrt (copyWeight_nonneg D i)

theorem weightSqrtDiagonal_middle_diagonal (D : ℕ) :
    weightSqrtDiagonal D * certificateDiagonal D * weightSqrtDiagonal D =
      (Matrix.diagonal (fun i => ((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ))*copyWeight D i)).map
        (Rat.castHom ℝ) := by
  simp only [weightSqrtDiagonal,certificateDiagonal,cast_rat_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  change Real.sqrt (copyWeight D i : ℝ) *
    (((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ) : ℚ) : ℝ) * Real.sqrt (copyWeight D i : ℝ) = _
  rw [Rat.cast_mul]
  calc
    _ = (((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ) : ℚ) : ℝ) *
        (Real.sqrt (copyWeight D i : ℝ))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (copyWeight_nonneg D i)]

theorem scaled_compression_identity (D : ℕ) :
    scaledGram D * (certificateDiagonal D-scaledError D) * scaledGram D =
      weightSqrtDiagonal D * (compressedRational D).map (Rat.castHom ℝ) * weightSqrtDiagonal D := by
  rw [scaledGram,scaledError,compressed_congruence_identity,
    weightSqrtDiagonal_middle_diagonal,weightSqrtDiagonal_sq]
  simp only [compressedRational,middleRational,Matrix.map_mul,cast_rat_sub]

theorem scaled_compression_positive (D : ℕ)
    (hM : ((compressedRational D).map (Rat.castHom ℝ)).PosSemidef) :
    (scaledGram D * (certificateDiagonal D-scaledError D) * scaledGram D).PosSemidef := by
  rw [scaled_compression_identity]
  have hd : (weightSqrtDiagonal D).IsHermitian := by
    simp [weightSqrtDiagonal,Matrix.IsHermitian]
  simpa only [hd.eq] using hM.mul_mul_conjTranspose_same (weightSqrtDiagonal D)

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_ScaledAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem scaled_four_body_certificates_oai (D : ℕ) (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (scaledGram D * (certificateDiagonal D-scaledError D) * scaledGram D).PosSemidef :=
  scaled_compression_positive D (four_body_certificates D hD₁ hD₂)

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.scaled_four_body_certificates_oai := @OAI.Laughlin.Certificate.scaled_four_body_certificates_oai
