-- Prove2me | solution 1 for OAI.LaughlinFock.fourYChecked_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T23:00:38.921082+00:00
-- url     : https://prove2.me/submissions/317e066f-ffd0-4a41-8e2e-03f5f8f903db

import Mathlib
import Definitions.Def_OAIQ084L033
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_collectedFourChecked_13
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_11_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_11_11
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_11_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_11_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_11_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_11_9
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_13_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_13_11
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_13_13
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_13_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_13_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_13_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_13_9
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_1_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_3_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_3_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_5_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_5_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_5_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_7_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_7_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_7_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_7_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_9_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_9_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_9_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_9_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_13_9_9
import Theorems.Thm_OAI_LaughlinFock_integerRowsFourTrace_parts

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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate13
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate13. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_13 (r s : CopyLabel 13) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 13 r s = fourYData_13 r s := by
  rw [integerRowsFourTrace_parts (by decide) collectedFourData_13 collectedFourChecked_13]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_13_1_1
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
  · exact fourYNumber_13_3_1
  · exact fourYNumber_13_3_3
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
  · exact fourYNumber_13_5_1
  · exact fourYNumber_13_5_3
  · exact fourYNumber_13_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · have h : (11:ℕ) ≤ 5 := hrs
    omega
  · have h : (13:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_13_7_1
  · exact fourYNumber_13_7_3
  · exact fourYNumber_13_7_5
  · exact fourYNumber_13_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · have h : (13:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_13_9_1
  · exact fourYNumber_13_9_3
  · exact fourYNumber_13_9_5
  · exact fourYNumber_13_9_7
  · exact fourYNumber_13_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_13_11_1
  · exact fourYNumber_13_11_3
  · exact fourYNumber_13_11_5
  · exact fourYNumber_13_11_7
  · exact fourYNumber_13_11_9
  · exact fourYNumber_13_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_13_13_1
  · exact fourYNumber_13_13_3
  · exact fourYNumber_13_13_5
  · exact fourYNumber_13_13_7
  · exact fourYNumber_13_13_9
  · exact fourYNumber_13_13_11
  · exact fourYNumber_13_13_13

theorem fourYChecked_13_oai (r s : CopyLabel 13) :
    integerRowsFourTrace 13 r s = fourYData_13 r s := by
  have hh : ∀ r s : CopyLabel 13, fourYData_13 r s = fourYData_13 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_13 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_13 s r (by omega), hh]

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYChecked_13_oai := @OAI.LaughlinFock.fourYChecked_13_oai
