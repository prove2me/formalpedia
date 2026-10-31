-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J3K1.checks
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:28:38.231131+00:00
-- url     : https://prove2.me/submissions/bfa09e99-4937-4dee-8132-7e4e5bf4f957

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K1

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
lemma check_26 : expression.check (-10+(26:ℚ)*(5*(1/10))) (1/10) 5 (blocks 26) = true := by decide +kernel
lemma check_27 : expression.check (-10+(27:ℚ)*(5*(1/10))) (1/10) 5 (blocks 27) = true := by decide +kernel
lemma check_28 : expression.check (-10+(28:ℚ)*(5*(1/10))) (1/10) 5 (blocks 28) = true := by decide +kernel
lemma check_29 : expression.check (-10+(29:ℚ)*(5*(1/10))) (1/10) 5 (blocks 29) = true := by decide +kernel
lemma check_30 : expression.check (-10+(30:ℚ)*(5*(1/10))) (1/10) 5 (blocks 30) = true := by decide +kernel
lemma check_31 : expression.check (-10+(31:ℚ)*(5*(1/10))) (1/10) 5 (blocks 31) = true := by decide +kernel
lemma check_32 : expression.check (-10+(32:ℚ)*(5*(1/10))) (1/10) 5 (blocks 32) = true := by decide +kernel
lemma check_33 : expression.check (-10+(33:ℚ)*(5*(1/10))) (1/10) 5 (blocks 33) = true := by decide +kernel
lemma check_34 : expression.check (-10+(34:ℚ)*(5*(1/10))) (1/10) 5 (blocks 34) = true := by decide +kernel
lemma check_35 : expression.check (-10+(35:ℚ)*(5*(1/10))) (1/10) 5 (blocks 35) = true := by decide +kernel
lemma check_36 : expression.check (-10+(36:ℚ)*(5*(1/10))) (1/10) 5 (blocks 36) = true := by decide +kernel
lemma check_37 : expression.check (-10+(37:ℚ)*(5*(1/10))) (1/10) 5 (blocks 37) = true := by decide +kernel
lemma check_38 : expression.check (-10+(38:ℚ)*(5*(1/10))) (1/10) 5 (blocks 38) = true := by decide +kernel
lemma check_39 : expression.check (-10+(39:ℚ)*(5*(1/10))) (1/10) 5 (blocks 39) = true := by decide +kernel

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

end SKRatio.Certificate.Data.J3K1

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J3K1.checks_oai := @OAI.SKRatio.Certificate.Data.J3K1.checks_oai
