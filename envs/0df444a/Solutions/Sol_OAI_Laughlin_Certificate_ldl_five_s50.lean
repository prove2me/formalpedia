-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_five_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:37:21.004202+00:00
-- url     : https://prove2.me/submissions/cb7cfc84-f9e1-40bf-b99c-3161bd00abfd

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Basic
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Row05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_5_1_1_0 : yRow 5 1 1 (rows[0]!) = (288217185514048371 / 32768 : ℚ) := by
  decide +kernel

theorem yRow_5_1_1_1 : yRow 5 1 1 (rows[1]!) = (117686364357605208465 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_1_1_2 : yRow 5 1 1 (rows[2]!) = (45543850761592353716265 / 3758096384 : ℚ) := by
  decide +kernel

theorem yRow_5_1_1_3 : yRow 5 1 1 (rows[3]!) = (-33527805633645391850149 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_1_1_4 : yRow 5 1 1 (rows[4]!) = (307361222967220883631 / 67108864 : ℚ) := by
  decide +kernel

theorem yRow_5_1_1_5 : yRow 5 1 1 (rows[5]!) = (10589763940221275062345 / 536870912 : ℚ) := by
  decide +kernel

theorem yRow_5_1_1_6 : yRow 5 1 1 (rows[6]!) = (-192715136303794262991 / 33554432 : ℚ) := by
  decide +kernel

theorem yRow_5_1_3_0 : yRow 5 1 3 (rows[0]!) = (1227892611554313699 / 32768 : ℚ) := by
  decide +kernel

theorem yRow_5_1_3_1 : yRow 5 1 3 (rows[1]!) = (-40217208208139155215 / 469762048 : ℚ) := by
  decide +kernel

theorem yRow_5_1_3_2 : yRow 5 1 3 (rows[2]!) = (3609794378028611869977 / 1879048192 : ℚ) := by
  decide +kernel

theorem yRow_5_1_3_3 : yRow 5 1 3 (rows[3]!) = (15972179718835785494373 / 469762048 : ℚ) := by
  decide +kernel

theorem yRow_5_1_3_4 : yRow 5 1 3 (rows[4]!) = (973139460225276068975 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_1_3_5 : yRow 5 1 3 (rows[5]!) = (8556207819014717270965 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_1_3_6 : yRow 5 1 3 (rows[6]!) = (-26195139147988314471 / 8388608 : ℚ) := by
  decide +kernel

theorem yRow_5_1_5_0 : yRow 5 1 5 (rows[0]!) = (517229739078330765 / 4096 : ℚ) := by
  decide +kernel

theorem yRow_5_1_5_1 : yRow 5 1 5 (rows[1]!) = (33354143675585625297 / 234881024 : ℚ) := by
  decide +kernel

theorem yRow_5_1_5_2 : yRow 5 1 5 (rows[2]!) = (-39698825671225989422295 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_1_5_3 : yRow 5 1 5 (rows[3]!) = (-24352127547028721893585 / 234881024 : ℚ) := by
  decide +kernel

theorem yRow_5_1_5_4 : yRow 5 1 5 (rows[4]!) = (-18686933965106262007505 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_1_5_5 : yRow 5 1 5 (rows[5]!) = (209580109115659324643705 / 3758096384 : ℚ) := by
  decide +kernel

theorem yRow_5_1_5_6 : yRow 5 1 5 (rows[6]!) = (122766324303368643735 / 67108864 : ℚ) := by
  decide +kernel

theorem yRow_5_3_1_0 : yRow 5 3 1 (rows[0]!) = (1227892611554313699 / 32768 : ℚ) := by
  decide +kernel

theorem yRow_5_3_1_1 : yRow 5 3 1 (rows[1]!) = (-40217208208139155215 / 469762048 : ℚ) := by
  decide +kernel

theorem yRow_5_3_1_2 : yRow 5 3 1 (rows[2]!) = (3609794378028611869977 / 1879048192 : ℚ) := by
  decide +kernel

theorem yRow_5_3_1_3 : yRow 5 3 1 (rows[3]!) = (15972179718835785494373 / 469762048 : ℚ) := by
  decide +kernel

theorem yRow_5_3_1_4 : yRow 5 3 1 (rows[4]!) = (973139460225276068975 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_3_1_5 : yRow 5 3 1 (rows[5]!) = (8556207819014717270965 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_3_1_6 : yRow 5 3 1 (rows[6]!) = (-26195139147988314471 / 8388608 : ℚ) := by
  decide +kernel

theorem yRow_5_3_3_0 : yRow 5 3 3 (rows[0]!) = (828106156763491761 / 16384 : ℚ) := by
  decide +kernel

theorem yRow_5_3_3_1 : yRow 5 3 3 (rows[1]!) = (12057655206433421045 / 234881024 : ℚ) := by
  decide +kernel

theorem yRow_5_3_3_2 : yRow 5 3 3 (rows[2]!) = (-6457052018534822018791 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_3_3_3 : yRow 5 3 3 (rows[3]!) = (885506700796361417871 / 234881024 : ℚ) := by
  decide +kernel

theorem yRow_5_3_3_4 : yRow 5 3 3 (rows[4]!) = (-543574257899971267101 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_3_3_5 : yRow 5 3 3 (rows[5]!) = (10662554367612487256863 / 268435456 : ℚ) := by
  decide +kernel

theorem yRow_5_3_3_6 : yRow 5 3 3 (rows[6]!) = (-175521550402232335797 / 67108864 : ℚ) := by
  decide +kernel

theorem yRow_5_3_5_0 : yRow 5 3 5 (rows[0]!) = (2088880360412782875 / 8192 : ℚ) := by
  decide +kernel

theorem yRow_5_3_5_1 : yRow 5 3 5 (rows[1]!) = (9078017688703880489 / 117440512 : ℚ) := by
  decide +kernel

theorem yRow_5_3_5_2 : yRow 5 3 5 (rows[2]!) = (4154519314999427044985 / 469762048 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Row052
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_5_3_5_3 : yRow 5 3 5 (rows[3]!) = (-1676596742006268315615 / 117440512 : ℚ) := by
  decide +kernel

theorem yRow_5_3_5_4 : yRow 5 3 5 (rows[4]!) = (1122516649266680657945 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_3_5_5 : yRow 5 3 5 (rows[5]!) = (11113921888615690197695 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_3_5_6 : yRow 5 3 5 (rows[6]!) = (-125595578390684976075 / 67108864 : ℚ) := by
  decide +kernel

theorem yRow_5_5_1_0 : yRow 5 5 1 (rows[0]!) = (517229739078330765 / 4096 : ℚ) := by
  decide +kernel

theorem yRow_5_5_1_1 : yRow 5 5 1 (rows[1]!) = (33354143675585625297 / 234881024 : ℚ) := by
  decide +kernel

theorem yRow_5_5_1_2 : yRow 5 5 1 (rows[2]!) = (-39698825671225989422295 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_5_1_3 : yRow 5 5 1 (rows[3]!) = (-24352127547028721893585 / 234881024 : ℚ) := by
  decide +kernel

theorem yRow_5_5_1_4 : yRow 5 5 1 (rows[4]!) = (-18686933965106262007505 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_5_1_5 : yRow 5 5 1 (rows[5]!) = (209580109115659324643705 / 3758096384 : ℚ) := by
  decide +kernel

theorem yRow_5_5_1_6 : yRow 5 5 1 (rows[6]!) = (122766324303368643735 / 67108864 : ℚ) := by
  decide +kernel

theorem yRow_5_5_3_0 : yRow 5 5 3 (rows[0]!) = (2088880360412782875 / 8192 : ℚ) := by
  decide +kernel

theorem yRow_5_5_3_1 : yRow 5 5 3 (rows[1]!) = (9078017688703880489 / 117440512 : ℚ) := by
  decide +kernel

theorem yRow_5_5_3_2 : yRow 5 5 3 (rows[2]!) = (4154519314999427044985 / 469762048 : ℚ) := by
  decide +kernel

theorem yRow_5_5_3_3 : yRow 5 5 3 (rows[3]!) = (-1676596742006268315615 / 117440512 : ℚ) := by
  decide +kernel

theorem yRow_5_5_3_4 : yRow 5 5 3 (rows[4]!) = (1122516649266680657945 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_5_3_5 : yRow 5 5 3 (rows[5]!) = (11113921888615690197695 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_5_3_6 : yRow 5 5 3 (rows[6]!) = (-125595578390684976075 / 67108864 : ℚ) := by
  decide +kernel

theorem yRow_5_5_5_0 : yRow 5 5 5 (rows[0]!) = (2127370824716077635 / 2048 : ℚ) := by
  decide +kernel

theorem yRow_5_5_5_1 : yRow 5 5 5 (rows[1]!) = (105906315909713386913 / 58720256 : ℚ) := by
  decide +kernel

theorem yRow_5_5_5_2 : yRow 5 5 5 (rows[2]!) = (79674709640186975436905 / 234881024 : ℚ) := by
  decide +kernel

theorem yRow_5_5_5_3 : yRow 5 5 5 (rows[3]!) = (16556987918363989467635 / 58720256 : ℚ) := by
  decide +kernel

theorem yRow_5_5_5_4 : yRow 5 5 5 (rows[4]!) = (35865503886652808531045 / 939524096 : ℚ) := by
  decide +kernel

theorem yRow_5_5_5_5 : yRow 5 5 5 (rows[5]!) = (52813174350218993123795 / 536870912 : ℚ) := by
  decide +kernel

theorem yRow_5_5_5_6 : yRow 5 5 5 (rows[6]!) = (-465607554421578820545 / 67108864 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Error05
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix


theorem ldl_five_s50_oai : compressedRational 5 =
    lowerFive * Matrix.diagonal pivotsFive * lowerFive.transpose := by
  unfold compressedRational middleRational
  rw [gram_five, error_five]
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_five_s50_oai := @OAI.Laughlin.Certificate.ldl_five_s50_oai
