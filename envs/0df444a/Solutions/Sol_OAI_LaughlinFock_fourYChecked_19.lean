-- Prove2me | solution 1 for OAI.LaughlinFock.fourYChecked_19
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:44:45.721163+00:00
-- url     : https://prove2.me/submissions/badc35bd-24cc-41b6-b6f2-8509a780dfa6

import Mathlib
import Definitions.Def_OAIQ084L029
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse19. -/
namespace LaughlinFock

theorem collectedFourChecked_19 : collectedFourTerms 19 = collectedFourData_19 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate19Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate19 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_19_1_1 :
    (collectedFourTrace 19 1 1 collectedFourData_19 : ℚ) / fourCommonDenominator = (-5179636017239466145793848200719937/20971520000000000000000) := by
  decide +kernel

theorem fourYNumber_19_3_1 :
    (collectedFourTrace 19 3 1 collectedFourData_19 : ℚ) / fourCommonDenominator = (187434720909027305797300194104127/8388608000000000000000) := by
  decide +kernel

theorem fourYNumber_19_3_3 :
    (collectedFourTrace 19 3 3 collectedFourData_19 : ℚ) / fourCommonDenominator = (-178409637091064952160509455064531/83886080000000000000000) := by
  decide +kernel

theorem fourYNumber_19_5_1 :
    (collectedFourTrace 19 5 1 collectedFourData_19 : ℚ) / fourCommonDenominator = (-2655089774899248756771754225173/838860800000000000000) := by
  decide +kernel

theorem fourYNumber_19_5_3 :
    (collectedFourTrace 19 5 3 collectedFourData_19 : ℚ) / fourCommonDenominator = (5621260360207772838458389165677/16777216000000000000000) := by
  decide +kernel

theorem fourYNumber_19_5_5 :
    (collectedFourTrace 19 5 5 collectedFourData_19 : ℚ) / fourCommonDenominator = (-426035399881728630302625737421/6710886400000000000000) := by
  decide +kernel

theorem fourYNumber_19_7_1 :
    (collectedFourTrace 19 7 1 collectedFourData_19 : ℚ) / fourCommonDenominator = (16881332854132320143988817820421/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_19_7_3 :
    (collectedFourTrace 19 7 3 collectedFourData_19 : ℚ) / fourCommonDenominator = (-4717729566947090956657038913269/67108864000000000000000) := by
  decide +kernel

theorem fourYNumber_19_7_5 :
    (collectedFourTrace 19 7 5 collectedFourData_19 : ℚ) / fourCommonDenominator = (245031192885525934544085492063/13421772800000000000000) := by
  decide +kernel

theorem fourYNumber_19_7_7 :
    (collectedFourTrace 19 7 7 collectedFourData_19 : ℚ) / fourCommonDenominator = (-384466433084035638058510508259/53687091200000000000000) := by
  decide +kernel

theorem fourYNumber_19_9_1 :
    (collectedFourTrace 19 9 1 collectedFourData_19 : ℚ) / fourCommonDenominator = (-194634222784906412908126173447/8388608000000000000000) := by
  decide +kernel

theorem fourYNumber_19_9_3 :
    (collectedFourTrace 19 9 3 collectedFourData_19 : ℚ) / fourCommonDenominator = (284747204857559498276849187561/16777216000000000000000) := by
  decide +kernel

theorem fourYNumber_19_9_5 :
    (collectedFourTrace 19 9 5 collectedFourData_19 : ℚ) / fourCommonDenominator = (-1557730163651995099526246487/209715200000000000000) := by
  decide +kernel

theorem fourYNumber_19_9_7 :
    (collectedFourTrace 19 9 7 collectedFourData_19 : ℚ) / fourCommonDenominator = (10123087280082182882087994459/2684354560000000000000) := by
  decide +kernel

theorem fourYNumber_19_9_9 :
    (collectedFourTrace 19 9 9 collectedFourData_19 : ℚ) / fourCommonDenominator = (-7622943311608357206631060953/3355443200000000000000) := by
  decide +kernel

theorem fourYNumber_19_11_1 :
    (collectedFourTrace 19 11 1 collectedFourData_19 : ℚ) / fourCommonDenominator = (-4278863868672885847019994838509/83886080000000000000000) := by
  decide +kernel

theorem fourYNumber_19_11_3 :
    (collectedFourTrace 19 11 3 collectedFourData_19 : ℚ) / fourCommonDenominator = (-36590419351896827609695794291/6710886400000000000000) := by
  decide +kernel

theorem fourYNumber_19_11_5 :
    (collectedFourTrace 19 11 5 collectedFourData_19 : ℚ) / fourCommonDenominator = (27876208643370085842832469481/6710886400000000000000) := by
  decide +kernel

theorem fourYNumber_19_11_7 :
    (collectedFourTrace 19 11 7 collectedFourData_19 : ℚ) / fourCommonDenominator = (-322902858771556364114391557133/134217728000000000000000) := by
  decide +kernel

theorem fourYNumber_19_11_9 :
    (collectedFourTrace 19 11 9 collectedFourData_19 : ℚ) / fourCommonDenominator = (51386596016276650248544081041/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_19_11_11 :
    (collectedFourTrace 19 11 11 collectedFourData_19 : ℚ) / fourCommonDenominator = (-357286302839183067236886747363/335544320000000000000000) := by
  decide +kernel

theorem fourYNumber_19_13_1 :
    (collectedFourTrace 19 13 1 collectedFourData_19 : ℚ) / fourCommonDenominator = (-92711834507674027889855562951/8388608000000000000000) := by
  decide +kernel

theorem fourYNumber_19_13_3 :
    (collectedFourTrace 19 13 3 collectedFourData_19 : ℚ) / fourCommonDenominator = (78521760071585338639486774419/10485760000000000000000) := by
  decide +kernel

theorem fourYNumber_19_13_5 :
    (collectedFourTrace 19 13 5 collectedFourData_19 : ℚ) / fourCommonDenominator = (-105195415768801818681315887793/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_19_13_7 :
    (collectedFourTrace 19 13 7 collectedFourData_19 : ℚ) / fourCommonDenominator = (26165622301296628386942262557/16777216000000000000000) := by
  decide +kernel

theorem fourYNumber_19_13_9 :
    (collectedFourTrace 19 13 9 collectedFourData_19 : ℚ) / fourCommonDenominator = (-15903873537826236008064465447/16777216000000000000000) := by
  decide +kernel

theorem fourYNumber_19_13_11 :
    (collectedFourTrace 19 13 11 collectedFourData_19 : ℚ) / fourCommonDenominator = (1423697597371070492775004701/2097152000000000000000) := by
  decide +kernel

theorem fourYNumber_19_13_13 :
    (collectedFourTrace 19 13 13 collectedFourData_19 : ℚ) / fourCommonDenominator = (-86861544457766197928712646743/167772160000000000000000) := by
  decide +kernel

theorem fourYNumber_19_15_1 :
    (collectedFourTrace 19 15 1 collectedFourData_19 : ℚ) / fourCommonDenominator = (6869519969496381960085415099007/33554432000000000000000) := by
  decide +kernel

theorem fourYNumber_19_15_3 :
    (collectedFourTrace 19 15 3 collectedFourData_19 : ℚ) / fourCommonDenominator = (-1321637020094633023479152437983/67108864000000000000000) := by
  decide +kernel

theorem fourYNumber_19_15_5 :
    (collectedFourTrace 19 15 5 collectedFourData_19 : ℚ) / fourCommonDenominator = (38229925041583923398630108229/13421772800000000000000) := by
  decide +kernel

theorem fourYNumber_19_15_7 :
    (collectedFourTrace 19 15 7 collectedFourData_19 : ℚ) / fourCommonDenominator = (-23973293068487386195658999913/53687091200000000000000) := by
  decide +kernel

theorem fourYNumber_19_15_9 :
    (collectedFourTrace 19 15 9 collectedFourData_19 : ℚ) / fourCommonDenominator = (125491751932979281769752833/2684354560000000000000) := by
  decide +kernel

theorem fourYNumber_19_15_11 :
    (collectedFourTrace 19 15 11 collectedFourData_19 : ℚ) / fourCommonDenominator = (-8162389557098350440321766311/134217728000000000000000) := by
  decide +kernel

theorem fourYNumber_19_15_13 :
    (collectedFourTrace 19 15 13 collectedFourData_19 : ℚ) / fourCommonDenominator = (4888844510450527600329505149/16777216000000000000000) := by
  decide +kernel

theorem fourYNumber_19_15_15 :
    (collectedFourTrace 19 15 15 collectedFourData_19 : ℚ) / fourCommonDenominator = (-42318688162572652589522350587/53687091200000000000000) := by
  decide +kernel

theorem fourYNumber_19_17_1 :
    (collectedFourTrace 19 17 1 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_17_3 :
    (collectedFourTrace 19 17 3 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_17_5 :
    (collectedFourTrace 19 17 5 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_17_7 :
    (collectedFourTrace 19 17 7 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_17_9 :
    (collectedFourTrace 19 17 9 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_17_11 :
    (collectedFourTrace 19 17 11 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_17_13 :
    (collectedFourTrace 19 17 13 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_17_15 :
    (collectedFourTrace 19 17 15 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_17_17 :
    (collectedFourTrace 19 17 17 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_19_1 :
    (collectedFourTrace 19 19 1 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_19_3 :
    (collectedFourTrace 19 19 3 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_19_5 :
    (collectedFourTrace 19 19 5 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_19_7 :
    (collectedFourTrace 19 19 7 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_19_9 :
    (collectedFourTrace 19 19 9 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_19_11 :
    (collectedFourTrace 19 19 11 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_19_13 :
    (collectedFourTrace 19 19 13 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_19_15 :
    (collectedFourTrace 19 19 15 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_19_17 :
    (collectedFourTrace 19 19 17 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_19_19_19 :
    (collectedFourTrace 19 19 19 collectedFourData_19 : ℚ) / fourCommonDenominator = 0 := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate19
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate19. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_19 (r s : CopyLabel 19) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 19 r s = fourYData_19 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_19 collectedFourChecked_19]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_19_1_1
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
  · have h : (19:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_19_3_1
  · exact fourYNumber_19_3_3
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
  · have h : (19:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_19_5_1
  · exact fourYNumber_19_5_3
  · exact fourYNumber_19_5_5
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
  · have h : (19:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_19_7_1
  · exact fourYNumber_19_7_3
  · exact fourYNumber_19_7_5
  · exact fourYNumber_19_7_7
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
  · have h : (19:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_19_9_1
  · exact fourYNumber_19_9_3
  · exact fourYNumber_19_9_5
  · exact fourYNumber_19_9_7
  · exact fourYNumber_19_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · have h : (15:ℕ) ≤ 9 := hrs
    omega
  · have h : (17:ℕ) ≤ 9 := hrs
    omega
  · have h : (19:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_19_11_1
  · exact fourYNumber_19_11_3
  · exact fourYNumber_19_11_5
  · exact fourYNumber_19_11_7
  · exact fourYNumber_19_11_9
  · exact fourYNumber_19_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · have h : (17:ℕ) ≤ 11 := hrs
    omega
  · have h : (19:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_19_13_1
  · exact fourYNumber_19_13_3
  · exact fourYNumber_19_13_5
  · exact fourYNumber_19_13_7
  · exact fourYNumber_19_13_9
  · exact fourYNumber_19_13_11
  · exact fourYNumber_19_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · have h : (17:ℕ) ≤ 13 := hrs
    omega
  · have h : (19:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_19_15_1
  · exact fourYNumber_19_15_3
  · exact fourYNumber_19_15_5
  · exact fourYNumber_19_15_7
  · exact fourYNumber_19_15_9
  · exact fourYNumber_19_15_11
  · exact fourYNumber_19_15_13
  · exact fourYNumber_19_15_15
  · have h : (17:ℕ) ≤ 15 := hrs
    omega
  · have h : (19:ℕ) ≤ 15 := hrs
    omega
  · exact fourYNumber_19_17_1
  · exact fourYNumber_19_17_3
  · exact fourYNumber_19_17_5
  · exact fourYNumber_19_17_7
  · exact fourYNumber_19_17_9
  · exact fourYNumber_19_17_11
  · exact fourYNumber_19_17_13
  · exact fourYNumber_19_17_15
  · exact fourYNumber_19_17_17
  · have h : (19:ℕ) ≤ 17 := hrs
    omega
  · exact fourYNumber_19_19_1
  · exact fourYNumber_19_19_3
  · exact fourYNumber_19_19_5
  · exact fourYNumber_19_19_7
  · exact fourYNumber_19_19_9
  · exact fourYNumber_19_19_11
  · exact fourYNumber_19_19_13
  · exact fourYNumber_19_19_15
  · exact fourYNumber_19_19_17
  · exact fourYNumber_19_19_19

theorem fourYChecked_19_oai (r s : CopyLabel 19) :
    integerRowsFourTrace 19 r s = fourYData_19 r s := by
  have hh : ∀ r s : CopyLabel 19, fourYData_19 r s = fourYData_19 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_19 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_19 s r (by omega), hh]

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYChecked_19_oai := @OAI.LaughlinFock.fourYChecked_19_oai
