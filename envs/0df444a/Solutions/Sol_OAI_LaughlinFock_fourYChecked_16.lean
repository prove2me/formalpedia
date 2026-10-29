-- Prove2me | solution 1 for OAI.LaughlinFock.fourYChecked_16
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:33:33.226777+00:00
-- url     : https://prove2.me/submissions/ef08d61b-edf9-4a19-abf1-8beff39f2d5d

import Mathlib
import Definitions.Def_OAIQ084L035
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_integerRowsFourTrace_collected

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RowTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



theorem rowFourLevel_symm {t : ℕ} (b c : RowEntry t) :
    rowFourLevel b c = rowFourLevel c b := by
  have hb := (rowEntry_bounds b).2.2.2
  have hc := (rowEntry_bounds c).2.2.2
  dsimp [rowFourLevel]
  omega

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1605
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1605. -/
namespace LaughlinFock

theorem collectedFourChecked_16 : collectedFourTerms 16 = collectedFourData_16 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate16Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate16 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_16_1_1 :
    (collectedFourTrace 16 1 1 collectedFourData_16 : ℚ) / fourCommonDenominator = (-3023300183640213893190968391086889/167772160000000000000000) := by
  decide +kernel

theorem fourYNumber_16_3_1 :
    (collectedFourTrace 16 3 1 collectedFourData_16 : ℚ) / fourCommonDenominator = (-1842284299727598695958363192819/4194304000000000000000) := by
  decide +kernel

theorem fourYNumber_16_3_3 :
    (collectedFourTrace 16 3 3 collectedFourData_16 : ℚ) / fourCommonDenominator = (-23811117256265722049574939091203/1677721600000000000000000) := by
  decide +kernel

theorem fourYNumber_16_5_1 :
    (collectedFourTrace 16 5 1 collectedFourData_16 : ℚ) / fourCommonDenominator = (4978857332568431590081678121247/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_16_5_3 :
    (collectedFourTrace 16 5 3 collectedFourData_16 : ℚ) / fourCommonDenominator = (451840005330447003265547996301/167772160000000000000000) := by
  decide +kernel

theorem fourYNumber_16_5_5 :
    (collectedFourTrace 16 5 5 collectedFourData_16 : ℚ) / fourCommonDenominator = (-83970211150334552496385437351/67108864000000000000000) := by
  decide +kernel

theorem fourYNumber_16_7_1 :
    (collectedFourTrace 16 7 1 collectedFourData_16 : ℚ) / fourCommonDenominator = (-495035435219731541754508880991/134217728000000000000000) := by
  decide +kernel

theorem fourYNumber_16_7_3 :
    (collectedFourTrace 16 7 3 collectedFourData_16 : ℚ) / fourCommonDenominator = (765033524894004427226426290029/1342177280000000000000000) := by
  decide +kernel

theorem fourYNumber_16_7_5 :
    (collectedFourTrace 16 7 5 collectedFourData_16 : ℚ) / fourCommonDenominator = (48488780217799936547817299631/335544320000000000000000) := by
  decide +kernel

theorem fourYNumber_16_7_7 :
    (collectedFourTrace 16 7 7 collectedFourData_16 : ℚ) / fourCommonDenominator = (-3262158077323107028703896377657/26843545600000000000000000) := by
  decide +kernel

theorem fourYNumber_16_9_1 :
    (collectedFourTrace 16 9 1 collectedFourData_16 : ℚ) / fourCommonDenominator = (-379088797146560907753377563533/83886080000000000000000) := by
  decide +kernel

theorem fourYNumber_16_9_3 :
    (collectedFourTrace 16 9 3 collectedFourData_16 : ℚ) / fourCommonDenominator = (-299360130730835687934042178557/1677721600000000000000000) := by
  decide +kernel

theorem fourYNumber_16_9_5 :
    (collectedFourTrace 16 9 5 collectedFourData_16 : ℚ) / fourCommonDenominator = (-142712675539696745387515611/10485760000000000000000) := by
  decide +kernel

theorem fourYNumber_16_9_7 :
    (collectedFourTrace 16 9 7 collectedFourData_16 : ℚ) / fourCommonDenominator = (52643089387008932592230169867/1342177280000000000000000) := by
  decide +kernel

theorem fourYNumber_16_9_9 :
    (collectedFourTrace 16 9 9 collectedFourData_16 : ℚ) / fourCommonDenominator = (-35077411519799463622935034803/1677721600000000000000000) := by
  decide +kernel

theorem fourYNumber_16_11_1 :
    (collectedFourTrace 16 11 1 collectedFourData_16 : ℚ) / fourCommonDenominator = (-1950638107811679763870313499579/335544320000000000000000) := by
  decide +kernel

theorem fourYNumber_16_11_3 :
    (collectedFourTrace 16 11 3 collectedFourData_16 : ℚ) / fourCommonDenominator = (-54641732479826306851381037121/134217728000000000000000) := by
  decide +kernel

theorem fourYNumber_16_11_5 :
    (collectedFourTrace 16 11 5 collectedFourData_16 : ℚ) / fourCommonDenominator = (55761689248689962568566349/2097152000000000000000) := by
  decide +kernel

theorem fourYNumber_16_11_7 :
    (collectedFourTrace 16 11 7 collectedFourData_16 : ℚ) / fourCommonDenominator = (53630278770653547050750239809/2684354560000000000000000) := by
  decide +kernel

theorem fourYNumber_16_11_9 :
    (collectedFourTrace 16 11 9 collectedFourData_16 : ℚ) / fourCommonDenominator = (1492590838618072536119968653/671088640000000000000000) := by
  decide +kernel

theorem fourYNumber_16_11_11 :
    (collectedFourTrace 16 11 11 collectedFourData_16 : ℚ) / fourCommonDenominator = (-18951724542978071115384073653/1342177280000000000000000) := by
  decide +kernel

theorem fourYNumber_16_13_1 :
    (collectedFourTrace 16 13 1 collectedFourData_16 : ℚ) / fourCommonDenominator = (830433036679330373158862049057/83886080000000000000000) := by
  decide +kernel

theorem fourYNumber_16_13_3 :
    (collectedFourTrace 16 13 3 collectedFourData_16 : ℚ) / fourCommonDenominator = (1596360042122635609616004677469/1677721600000000000000000) := by
  decide +kernel

theorem fourYNumber_16_13_5 :
    (collectedFourTrace 16 13 5 collectedFourData_16 : ℚ) / fourCommonDenominator = (-14386490313579701778931067169/335544320000000000000000) := by
  decide +kernel

theorem fourYNumber_16_13_7 :
    (collectedFourTrace 16 13 7 collectedFourData_16 : ℚ) / fourCommonDenominator = (-501723637603154001058680647991/6710886400000000000000000) := by
  decide +kernel

theorem fourYNumber_16_13_9 :
    (collectedFourTrace 16 13 9 collectedFourData_16 : ℚ) / fourCommonDenominator = (40370172661050112192774463001/1677721600000000000000000) := by
  decide +kernel

theorem fourYNumber_16_13_11 :
    (collectedFourTrace 16 13 11 collectedFourData_16 : ℚ) / fourCommonDenominator = (3060950838759256839852570543/134217728000000000000000) := by
  decide +kernel

theorem fourYNumber_16_13_13 :
    (collectedFourTrace 16 13 13 collectedFourData_16 : ℚ) / fourCommonDenominator = (-184942013999244668370911421/4194304000000000000000) := by
  decide +kernel

theorem fourYNumber_16_15_1 :
    (collectedFourTrace 16 15 1 collectedFourData_16 : ℚ) / fourCommonDenominator = (-780293120878982200971277577781/134217728000000000000000) := by
  decide +kernel

theorem fourYNumber_16_15_3 :
    (collectedFourTrace 16 15 3 collectedFourData_16 : ℚ) / fourCommonDenominator = (-1867439584107586370782878530553/1342177280000000000000000) := by
  decide +kernel

theorem fourYNumber_16_15_5 :
    (collectedFourTrace 16 15 5 collectedFourData_16 : ℚ) / fourCommonDenominator = (-26878148679024614358884359863/67108864000000000000000) := by
  decide +kernel

theorem fourYNumber_16_15_7 :
    (collectedFourTrace 16 15 7 collectedFourData_16 : ℚ) / fourCommonDenominator = (1593230986748752248427033240737/5368709120000000000000000) := by
  decide +kernel

theorem fourYNumber_16_15_9 :
    (collectedFourTrace 16 15 9 collectedFourData_16 : ℚ) / fourCommonDenominator = (-86392805913427500216351869247/1342177280000000000000000) := by
  decide +kernel

theorem fourYNumber_16_15_11 :
    (collectedFourTrace 16 15 11 collectedFourData_16 : ℚ) / fourCommonDenominator = (-8106039764158833303443597961/536870912000000000000000) := by
  decide +kernel

theorem fourYNumber_16_15_13 :
    (collectedFourTrace 16 15 13 collectedFourData_16 : ℚ) / fourCommonDenominator = (18946767647015678576766350691/268435456000000000000000) := by
  decide +kernel

theorem fourYNumber_16_15_15 :
    (collectedFourTrace 16 15 15 collectedFourData_16 : ℚ) / fourCommonDenominator = (-28303565196748876363274618673/42949672960000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_TraceSymmetry
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Symmetry. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem rationalFourFactor_symm {t : ℕ} (D : ℕ) (b c : RowEntry t) :
    rationalFourFactor D b c = rationalFourFactor D c b := by
  unfold rationalFourFactor
  rw [rowFourLevel_symm b c]
  ring

theorem integerFourTrace_symm (D t : ℕ) (a : RowEntry t → ℚ) (r s : CopyLabel D) :
    integerFourTrace D t a r s = integerFourTrace D t a s r := by
  unfold integerFourTrace
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [rowFourLevel_symm c b, rationalFourFactor_symm D c b]
  split_ifs <;> ring

theorem integerRowsFourTrace_symm (D : ℕ) (r s : CopyLabel D) :
    integerRowsFourTrace D r s = integerRowsFourTrace D s r := by
  unfold integerRowsFourTrace
  simp only [Matrix.sum_apply]
  exact Finset.sum_congr rfl (fun t _ => integerFourTrace_symm D t.val (certificateAlpha t) r s)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate16
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate16. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_16 (r s : CopyLabel 16) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 16 r s = fourYData_16 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_16 collectedFourChecked_16]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_16_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · have h : (7:ℕ) ≤ 1 := hrs
    omega
  · have h : (9:ℕ) ≤ 1 := hrs
    omega
  · have h : (11:ℕ) ≤ 1 := hrs
    omega
  · have h : (13:ℕ) ≤ 1 := hrs
    omega
  · have h : (15:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_16_3_1
  · exact fourYNumber_16_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · have h : (9:ℕ) ≤ 3 := hrs
    omega
  · have h : (11:ℕ) ≤ 3 := hrs
    omega
  · have h : (13:ℕ) ≤ 3 := hrs
    omega
  · have h : (15:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_16_5_1
  · exact fourYNumber_16_5_3
  · exact fourYNumber_16_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · have h : (11:ℕ) ≤ 5 := hrs
    omega
  · have h : (13:ℕ) ≤ 5 := hrs
    omega
  · have h : (15:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_16_7_1
  · exact fourYNumber_16_7_3
  · exact fourYNumber_16_7_5
  · exact fourYNumber_16_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · have h : (13:ℕ) ≤ 7 := hrs
    omega
  · have h : (15:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_16_9_1
  · exact fourYNumber_16_9_3
  · exact fourYNumber_16_9_5
  · exact fourYNumber_16_9_7
  · exact fourYNumber_16_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · have h : (15:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_16_11_1
  · exact fourYNumber_16_11_3
  · exact fourYNumber_16_11_5
  · exact fourYNumber_16_11_7
  · exact fourYNumber_16_11_9
  · exact fourYNumber_16_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_16_13_1
  · exact fourYNumber_16_13_3
  · exact fourYNumber_16_13_5
  · exact fourYNumber_16_13_7
  · exact fourYNumber_16_13_9
  · exact fourYNumber_16_13_11
  · exact fourYNumber_16_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_16_15_1
  · exact fourYNumber_16_15_3
  · exact fourYNumber_16_15_5
  · exact fourYNumber_16_15_7
  · exact fourYNumber_16_15_9
  · exact fourYNumber_16_15_11
  · exact fourYNumber_16_15_13
  · exact fourYNumber_16_15_15

theorem fourYChecked_16_oai (r s : CopyLabel 16) :
    integerRowsFourTrace 16 r s = fourYData_16 r s := by
  have hh : ∀ r s : CopyLabel 16, fourYData_16 r s = fourYData_16 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_16 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_16 s r (by omega), hh]

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYChecked_16_oai := @OAI.LaughlinFock.fourYChecked_16_oai
