-- Prove2me | solution 1 for OAI.LaughlinFock.fourYChecked_17
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:38:15.963554+00:00
-- url     : https://prove2.me/submissions/5c48a9cc-b057-41cc-b3d4-12b2c0f1a011

import Mathlib
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1703
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1703. -/
namespace LaughlinFock

theorem collectedFourChecked_17 : collectedFourTerms 17 = collectedFourData_17 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate17Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate17 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_17_1_1 :
    (collectedFourTrace 17 1 1 collectedFourData_17 : ℚ) / fourCommonDenominator = (-80532574708892899999366914086133/3355443200000000000000) := by
  decide +kernel

theorem fourYNumber_17_3_1 :
    (collectedFourTrace 17 3 1 collectedFourData_17 : ℚ) / fourCommonDenominator = (52168314199581417516891452106867/167772160000000000000000) := by
  decide +kernel

theorem fourYNumber_17_3_3 :
    (collectedFourTrace 17 3 3 collectedFourData_17 : ℚ) / fourCommonDenominator = (-1936359965196807219209198649591/335544320000000000000000) := by
  decide +kernel

theorem fourYNumber_17_5_1 :
    (collectedFourTrace 17 5 1 collectedFourData_17 : ℚ) / fourCommonDenominator = (3416941451122696842894790053813/16777216000000000000000) := by
  decide +kernel

theorem fourYNumber_17_5_3 :
    (collectedFourTrace 17 5 3 collectedFourData_17 : ℚ) / fourCommonDenominator = (-42279505429943443249978853463/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_17_5_5 :
    (collectedFourTrace 17 5 5 collectedFourData_17 : ℚ) / fourCommonDenominator = (-6128074571331463431937198371/2684354560000000000000) := by
  decide +kernel

theorem fourYNumber_17_7_1 :
    (collectedFourTrace 17 7 1 collectedFourData_17 : ℚ) / fourCommonDenominator = (-1780399758192138186776437952187/26843545600000000000000) := by
  decide +kernel

theorem fourYNumber_17_7_3 :
    (collectedFourTrace 17 7 3 collectedFourData_17 : ℚ) / fourCommonDenominator = (80383774372540182022310744913/268435456000000000000000) := by
  decide +kernel

theorem fourYNumber_17_7_5 :
    (collectedFourTrace 17 7 5 collectedFourData_17 : ℚ) / fourCommonDenominator = (10281592378696087538598060783/13421772800000000000000) := by
  decide +kernel

theorem fourYNumber_17_7_7 :
    (collectedFourTrace 17 7 7 collectedFourData_17 : ℚ) / fourCommonDenominator = (-56338902649996905268880020737/214748364800000000000000) := by
  decide +kernel

theorem fourYNumber_17_9_1 :
    (collectedFourTrace 17 9 1 collectedFourData_17 : ℚ) / fourCommonDenominator = (-147580447016100579129054473067/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_17_9_3 :
    (collectedFourTrace 17 9 3 collectedFourData_17 : ℚ) / fourCommonDenominator = (7501433511302274776260777749/67108864000000000000000) := by
  decide +kernel

theorem fourYNumber_17_9_5 :
    (collectedFourTrace 17 9 5 collectedFourData_17 : ℚ) / fourCommonDenominator = (-251301453661421637165143991/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_17_9_7 :
    (collectedFourTrace 17 9 7 collectedFourData_17 : ℚ) / fourCommonDenominator = (3801942718922194741310789331/268435456000000000000000) := by
  decide +kernel

theorem fourYNumber_17_9_9 :
    (collectedFourTrace 17 9 9 collectedFourData_17 : ℚ) / fourCommonDenominator = (-880826387722113202317841761/67108864000000000000000) := by
  decide +kernel

theorem fourYNumber_17_11_1 :
    (collectedFourTrace 17 11 1 collectedFourData_17 : ℚ) / fourCommonDenominator = (484754681413657976207114779551/13421772800000000000000) := by
  decide +kernel

theorem fourYNumber_17_11_3 :
    (collectedFourTrace 17 11 3 collectedFourData_17 : ℚ) / fourCommonDenominator = (-213828608195027061344135968941/671088640000000000000000) := by
  decide +kernel

theorem fourYNumber_17_11_5 :
    (collectedFourTrace 17 11 5 collectedFourData_17 : ℚ) / fourCommonDenominator = (-2988845641835365468393449333/8388608000000000000000) := by
  decide +kernel

theorem fourYNumber_17_11_7 :
    (collectedFourTrace 17 11 7 collectedFourData_17 : ℚ) / fourCommonDenominator = (12371464740075924792908192517/107374182400000000000000) := by
  decide +kernel

theorem fourYNumber_17_11_9 :
    (collectedFourTrace 17 11 9 collectedFourData_17 : ℚ) / fourCommonDenominator = (778359374321012227957500441/134217728000000000000000) := by
  decide +kernel

theorem fourYNumber_17_11_11 :
    (collectedFourTrace 17 11 11 collectedFourData_17 : ℚ) / fourCommonDenominator = (-3469951889789090759165765169/53687091200000000000000) := by
  decide +kernel

theorem fourYNumber_17_13_1 :
    (collectedFourTrace 17 13 1 collectedFourData_17 : ℚ) / fourCommonDenominator = (-8998787136844095341470376163507/167772160000000000000000) := by
  decide +kernel

theorem fourYNumber_17_13_3 :
    (collectedFourTrace 17 13 3 collectedFourData_17 : ℚ) / fourCommonDenominator = (277309144397718714739016580021/335544320000000000000000) := by
  decide +kernel

theorem fourYNumber_17_13_5 :
    (collectedFourTrace 17 13 5 collectedFourData_17 : ℚ) / fourCommonDenominator = (1478457672704508300479559027/2684354560000000000000) := by
  decide +kernel

theorem fourYNumber_17_13_7 :
    (collectedFourTrace 17 13 7 collectedFourData_17 : ℚ) / fourCommonDenominator = (-57128772289770289745633735739/268435456000000000000000) := by
  decide +kernel

theorem fourYNumber_17_13_9 :
    (collectedFourTrace 17 13 9 collectedFourData_17 : ℚ) / fourCommonDenominator = (1542736257700531168437068907/335544320000000000000000) := by
  decide +kernel

theorem fourYNumber_17_13_11 :
    (collectedFourTrace 17 13 11 collectedFourData_17 : ℚ) / fourCommonDenominator = (67600551228997897843877987271/671088640000000000000000) := by
  decide +kernel

theorem fourYNumber_17_13_13 :
    (collectedFourTrace 17 13 13 collectedFourData_17 : ℚ) / fourCommonDenominator = (-5335051448812934030171092389/41943040000000000000000) := by
  decide +kernel

theorem fourYNumber_17_15_1 :
    (collectedFourTrace 17 15 1 collectedFourData_17 : ℚ) / fourCommonDenominator = (13585035090756473170103083369563/134217728000000000000000) := by
  decide +kernel

theorem fourYNumber_17_15_3 :
    (collectedFourTrace 17 15 3 collectedFourData_17 : ℚ) / fourCommonDenominator = (-255854381753090751185768626413/268435456000000000000000) := by
  decide +kernel

theorem fourYNumber_17_15_5 :
    (collectedFourTrace 17 15 5 collectedFourData_17 : ℚ) / fourCommonDenominator = (-9486946401639002079898757643/13421772800000000000000) := by
  decide +kernel

theorem fourYNumber_17_15_7 :
    (collectedFourTrace 17 15 7 collectedFourData_17 : ℚ) / fourCommonDenominator = (34846908517875080159788075821/214748364800000000000000) := by
  decide +kernel

theorem fourYNumber_17_15_9 :
    (collectedFourTrace 17 15 9 collectedFourData_17 : ℚ) / fourCommonDenominator = (11878850604017989335381270633/268435456000000000000000) := by
  decide +kernel

theorem fourYNumber_17_15_11 :
    (collectedFourTrace 17 15 11 collectedFourData_17 : ℚ) / fourCommonDenominator = (-55816204555305340589721547269/536870912000000000000000) := by
  decide +kernel

theorem fourYNumber_17_15_13 :
    (collectedFourTrace 17 15 13 collectedFourData_17 : ℚ) / fourCommonDenominator = (49207289089932048557142307647/268435456000000000000000) := by
  decide +kernel

theorem fourYNumber_17_15_15 :
    (collectedFourTrace 17 15 15 collectedFourData_17 : ℚ) / fourCommonDenominator = (-25213653324476267050918226709/42949672960000000000000) := by
  decide +kernel

theorem fourYNumber_17_17_1 :
    (collectedFourTrace 17 17 1 collectedFourData_17 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_17_17_3 :
    (collectedFourTrace 17 17 3 collectedFourData_17 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_17_17_5 :
    (collectedFourTrace 17 17 5 collectedFourData_17 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_17_17_7 :
    (collectedFourTrace 17 17 7 collectedFourData_17 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_17_17_9 :
    (collectedFourTrace 17 17 9 collectedFourData_17 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_17_17_11 :
    (collectedFourTrace 17 17 11 collectedFourData_17 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_17_17_13 :
    (collectedFourTrace 17 17 13 collectedFourData_17 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_17_17_15 :
    (collectedFourTrace 17 17 15 collectedFourData_17 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_17_17_17 :
    (collectedFourTrace 17 17 17 collectedFourData_17 : ℚ) / fourCommonDenominator = 0 := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate17
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate17. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_17 (r s : CopyLabel 17) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 17 r s = fourYData_17 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_17 collectedFourChecked_17]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_17_1_1
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
  · have h : (17:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_17_3_1
  · exact fourYNumber_17_3_3
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
  · have h : (17:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_17_5_1
  · exact fourYNumber_17_5_3
  · exact fourYNumber_17_5_5
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
  · have h : (17:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_17_7_1
  · exact fourYNumber_17_7_3
  · exact fourYNumber_17_7_5
  · exact fourYNumber_17_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · have h : (13:ℕ) ≤ 7 := hrs
    omega
  · have h : (15:ℕ) ≤ 7 := hrs
    omega
  · have h : (17:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_17_9_1
  · exact fourYNumber_17_9_3
  · exact fourYNumber_17_9_5
  · exact fourYNumber_17_9_7
  · exact fourYNumber_17_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · have h : (15:ℕ) ≤ 9 := hrs
    omega
  · have h : (17:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_17_11_1
  · exact fourYNumber_17_11_3
  · exact fourYNumber_17_11_5
  · exact fourYNumber_17_11_7
  · exact fourYNumber_17_11_9
  · exact fourYNumber_17_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · have h : (17:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_17_13_1
  · exact fourYNumber_17_13_3
  · exact fourYNumber_17_13_5
  · exact fourYNumber_17_13_7
  · exact fourYNumber_17_13_9
  · exact fourYNumber_17_13_11
  · exact fourYNumber_17_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · have h : (17:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_17_15_1
  · exact fourYNumber_17_15_3
  · exact fourYNumber_17_15_5
  · exact fourYNumber_17_15_7
  · exact fourYNumber_17_15_9
  · exact fourYNumber_17_15_11
  · exact fourYNumber_17_15_13
  · exact fourYNumber_17_15_15
  · have h : (17:ℕ) ≤ 15 := hrs
    omega
  · exact fourYNumber_17_17_1
  · exact fourYNumber_17_17_3
  · exact fourYNumber_17_17_5
  · exact fourYNumber_17_17_7
  · exact fourYNumber_17_17_9
  · exact fourYNumber_17_17_11
  · exact fourYNumber_17_17_13
  · exact fourYNumber_17_17_15
  · exact fourYNumber_17_17_17

theorem fourYChecked_17_oai (r s : CopyLabel 17) :
    integerRowsFourTrace 17 r s = fourYData_17 r s := by
  have hh : ∀ r s : CopyLabel 17, fourYData_17 r s = fourYData_17 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_17 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_17 s r (by omega), hh]

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYChecked_17_oai := @OAI.LaughlinFock.fourYChecked_17_oai
