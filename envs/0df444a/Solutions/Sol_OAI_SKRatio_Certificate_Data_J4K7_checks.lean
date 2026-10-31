-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K7.checks
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:41:37.597257+00:00
-- url     : https://prove2.me/submissions/b2ea260d-17de-426a-ac37-83b4e73e7698

import Mathlib
import Definitions.Def_OAIQ024S013
import Definitions.Def_OAIQ024S016
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_26
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_27
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_28
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_29
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_30
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_31
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_32
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_33
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_34
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_35
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_36
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_37
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_38
import Theorems.Thm_OAI_SKRatio_Certificate_Data_J4K7_check_39

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K7

lemma check_0 : expression.check (-10+(0:ℚ)*(5*(1/10))) (1/10) 5 (blocks 0) = true := by decide +kernel
lemma check_1 : expression.check (-10+(1:ℚ)*(5*(1/10))) (1/10) 5 (blocks 1) = true := by decide +kernel
lemma check_2 : expression.check (-10+(2:ℚ)*(5*(1/10))) (1/10) 5 (blocks 2) = true := by decide +kernel
lemma check_3 : expression.check (-10+(3:ℚ)*(5*(1/10))) (1/10) 5 (blocks 3) = true := by decide +kernel
lemma check_4 : expression.check (-10+(4:ℚ)*(5*(1/10))) (1/10) 5 (blocks 4) = true := by decide +kernel
lemma check_5 : expression.check (-10+(5:ℚ)*(5*(1/10))) (1/10) 5 (blocks 5) = true := by decide +kernel
lemma check_6 : expression.check (-10+(6:ℚ)*(5*(1/10))) (1/10) 5 (blocks 6) = true := by decide +kernel
lemma check_7 : expression.check (-10+(7:ℚ)*(5*(1/10))) (1/10) 5 (blocks 7) = true := by decide +kernel
lemma check_8 : expression.check (-10+(8:ℚ)*(5*(1/10))) (1/10) 5 (blocks 8) = true := by decide +kernel
lemma check_9 : expression.check (-10+(9:ℚ)*(5*(1/10))) (1/10) 5 (blocks 9) = true := by decide +kernel
lemma check_10 : expression.check (-10+(10:ℚ)*(5*(1/10))) (1/10) 5 (blocks 10) = true := by decide +kernel
lemma check_11 : expression.check (-10+(11:ℚ)*(5*(1/10))) (1/10) 5 (blocks 11) = true := by decide +kernel
lemma check_12 : expression.check (-10+(12:ℚ)*(5*(1/10))) (1/10) 5 (blocks 12) = true := by decide +kernel
lemma check_13 : expression.check (-10+(13:ℚ)*(5*(1/10))) (1/10) 5 (blocks 13) = true := by decide +kernel
lemma check_14 : expression.check (-10+(14:ℚ)*(5*(1/10))) (1/10) 5 (blocks 14) = true := by decide +kernel
lemma check_15 : expression.check (-10+(15:ℚ)*(5*(1/10))) (1/10) 5 (blocks 15) = true := by decide +kernel
lemma check_16 : expression.check (-10+(16:ℚ)*(5*(1/10))) (1/10) 5 (blocks 16) = true := by decide +kernel
lemma check_17 : expression.check (-10+(17:ℚ)*(5*(1/10))) (1/10) 5 (blocks 17) = true := by decide +kernel
lemma check_18 : expression.check (-10+(18:ℚ)*(5*(1/10))) (1/10) 5 (blocks 18) = true := by decide +kernel
lemma check_19 : expression.check (-10+(19:ℚ)*(5*(1/10))) (1/10) 5 (blocks 19) = true := by decide +kernel
lemma check_20 : expression.check (-10+(20:ℚ)*(5*(1/10))) (1/10) 5 (blocks 20) = true := by decide +kernel
lemma check_21 : expression.check (-10+(21:ℚ)*(5*(1/10))) (1/10) 5 (blocks 21) = true := by decide +kernel
lemma check_22 : expression.check (-10+(22:ℚ)*(5*(1/10))) (1/10) 5 (blocks 22) = true := by decide +kernel
lemma check_23 : expression.check (-10+(23:ℚ)*(5*(1/10))) (1/10) 5 (blocks 23) = true := by decide +kernel
lemma check_24 : expression.check (-10+(24:ℚ)*(5*(1/10))) (1/10) 5 (blocks 24) = true := by decide +kernel
lemma check_25 : expression.check (-10+(25:ℚ)*(5*(1/10))) (1/10) 5 (blocks 25) = true := by decide +kernel

lemma checks_oai (i : ℕ) (hi : i < 40) :
    expression.check (-10+(i:ℚ)*(5*(1/10))) (1/10) 5 (blocks i) = true := by
  interval_cases i
  · exact check_0
  · exact check_1
  · exact check_2
  · exact check_3
  · exact check_4
  · exact check_5
  · exact check_6
  · exact check_7
  · exact check_8
  · exact check_9
  · exact check_10
  · exact check_11
  · exact check_12
  · exact check_13
  · exact check_14
  · exact check_15
  · exact check_16
  · exact check_17
  · exact check_18
  · exact check_19
  · exact check_20
  · exact check_21
  · exact check_22
  · exact check_23
  · exact check_24
  · exact check_25
  · exact check_26
  · exact check_27
  · exact check_28
  · exact check_29
  · exact check_30
  · exact check_31
  · exact check_32
  · exact check_33
  · exact check_34
  · exact check_35
  · exact check_36
  · exact check_37
  · exact check_38
  · exact check_39

end SKRatio.Certificate.Data.J4K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K7.checks_oai := @OAI.SKRatio.Certificate.Data.J4K7.checks_oai
