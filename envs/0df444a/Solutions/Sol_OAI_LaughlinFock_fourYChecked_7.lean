-- Prove2me | solution 1 for OAI.LaughlinFock.fourYChecked_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T23:00:40.298397+00:00
-- url     : https://prove2.me/submissions/bf7843e6-1dc5-4857-8ef9-0f9f09ea9a39

import Mathlib
import Definitions.Def_OAIQ084L029
import Definitions.Def_OAIQ084L037
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_7_1_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_7_3_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_7_3_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_7_5_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_7_5_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_7_5_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_7_7_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_7_7_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_7_7_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_7_7_7
import Theorems.Thm_OAI_LaughlinFock_numericRowDataChecked_0
import Theorems.Thm_OAI_LaughlinFock_numericRowDataChecked_1
import Theorems.Thm_OAI_LaughlinFock_numericRowDataChecked_2
import Theorems.Thm_OAI_LaughlinFock_numericRowDataChecked_3
import Theorems.Thm_OAI_LaughlinFock_numericRowDataChecked_4
import Theorems.Thm_OAI_LaughlinFock_numericRowDataChecked_5
import Theorems.Thm_OAI_LaughlinFock_numericRowDataChecked_6
import Theorems.Thm_OAI_LaughlinFock_numericRowDataChecked_7
import Theorems.Thm_OAI_LaughlinFock_rowEntryChecked_0
import Theorems.Thm_OAI_LaughlinFock_rowEntryChecked_1
import Theorems.Thm_OAI_LaughlinFock_rowEntryChecked_2
import Theorems.Thm_OAI_LaughlinFock_rowEntryChecked_3
import Theorems.Thm_OAI_LaughlinFock_rowEntryChecked_4
import Theorems.Thm_OAI_LaughlinFock_rowEntryChecked_5
import Theorems.Thm_OAI_LaughlinFock_rowEntryChecked_6
import Theorems.Thm_OAI_LaughlinFock_rowEntryChecked_7

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

theorem rowFourLevel_le {t : ℕ} (b c : RowEntry t) : rowFourLevel b c ≤ 23 := by
  have hb := rowEntry_bounds b
  have hc := rowEntry_bounds c
  dsimp [rowFourLevel]
  omega


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FastCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem integerCoupling_fast (c : ℤ) (z k p : ℕ) :
    integerCoupling c z k p = fastIntegerCoupling c z k p := by
  simp only [integerCoupling, fastIntegerCoupling, Nat.choose_eq_fast_choose]

theorem integerCopyPolynomial_fast (D T r p j k : ℕ) :
    integerCopyPolynomial D T r p j k = fastIntegerCopyPolynomial D T r p j k := by
  simp only [integerCopyPolynomial, fastIntegerCopyPolynomial, integerCoupling_fast]
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CouplingTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coupling Tables. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem unitCouplingChecked_0 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 0 k.val p.val = memoUnitCoupling 0 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_1 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 1 k.val p.val = memoUnitCoupling 1 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_2 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 2 k.val p.val = memoUnitCoupling 2 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_3 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 3 k.val p.val = memoUnitCoupling 3 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_4 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 4 k.val p.val = memoUnitCoupling 4 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_5 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 5 k.val p.val = memoUnitCoupling 5 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_6 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 6 k.val p.val = memoUnitCoupling 6 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_7 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 7 k.val p.val = memoUnitCoupling 7 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_8 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 8 k.val p.val = memoUnitCoupling 8 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_9 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 9 k.val p.val = memoUnitCoupling 9 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_10 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 10 k.val p.val = memoUnitCoupling 10 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_11 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 11 k.val p.val = memoUnitCoupling 11 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_12 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 12 k.val p.val = memoUnitCoupling 12 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_13 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 13 k.val p.val = memoUnitCoupling 13 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_14 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 14 k.val p.val = memoUnitCoupling 14 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_15 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 15 k.val p.val = memoUnitCoupling 15 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_16 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 16 k.val p.val = memoUnitCoupling 16 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_17 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 17 k.val p.val = memoUnitCoupling 17 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_18 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 18 k.val p.val = memoUnitCoupling 18 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_19 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 19 k.val p.val = memoUnitCoupling 19 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_20 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 20 k.val p.val = memoUnitCoupling 20 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_21 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 21 k.val p.val = memoUnitCoupling 21 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_22 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 22 k.val p.val = memoUnitCoupling 22 k.val p.val := by
  decide +kernel

theorem unitCouplingChecked_23 : ∀ (k : Fin 24) (p : Fin 9),
    fastIntegerCoupling 1 23 k.val p.val = memoUnitCoupling 23 k.val p.val := by
  decide +kernel

theorem memoUnitCoupling_spec (z k p : ℕ) (hz : z < 24) (hk : k < 24) (hp : p < 9) :
    fastIntegerCoupling 1 z k p = memoUnitCoupling z k p := by
  interval_cases z
  · exact unitCouplingChecked_0 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_1 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_2 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_3 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_4 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_5 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_6 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_7 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_8 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_9 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_10 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_11 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_12 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_13 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_14 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_15 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_16 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_17 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_18 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_19 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_20 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_21 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_22 ⟨k, hk⟩ ⟨p, hp⟩
  · exact unitCouplingChecked_23 ⟨k, hk⟩ ⟨p, hp⟩
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FastTrace
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem scaledFourFactor_spec (D : ℕ) (t : Fin 8) (b c : RowEntry t.val) :
    (scaledFourFactor D t b c : ℚ) / (2^53 * (23).factorial) = rationalFourFactor D b c := by
  have hT := rowFourLevel_le b c
  have ht := t.isLt
  have hdvd : (rowFourLevel b c-D).factorial ∣ (23).factorial :=
    Nat.factorial_dvd_factorial (by omega)
  have hpow : (2:ℚ)^(53+rowP b+rowP c-(t.val+2*rowFourLevel b c)) *
      2^(t.val+2*rowFourLevel b c) = 2^(53+rowP b+rowP c) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  unfold scaledFourFactor rationalFourFactor
  push_cast
  rw [Nat.cast_div hdvd (by positivity : ((rowFourLevel b c-D).factorial : ℚ) ≠ 0)]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  have hfac : ((rowFourLevel b c-D).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  simp only [← pow_mul, ← pow_add] at *
  ring_nf at *
  exact hpow

theorem integerFourTrace_scaled (D : ℕ) (t : Fin 8) (r s : CopyLabel D) :
    integerFourTrace D t.val (certificateAlpha t) r s =
      (scaledFourTrace D t r s : ℚ) / fourCommonDenominator := by
  unfold integerFourTrace scaledFourTrace
  simp only [integerCopyPolynomial_fast]
  simp only [Int.cast_neg, Int.cast_sum, neg_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with hh
  · simp only [Int.cast_mul, Int.cast_natCast]
    rw [← scaledFourFactor_spec D t b c]
    unfold certificateAlpha fourCommonDenominator
    push_cast
    ring
  · simp

theorem integerRowsFourTrace_scaled (D : ℕ) (r s : CopyLabel D) :
    integerRowsFourTrace D r s = (scaledRowsFourTrace D r s : ℚ) / fourCommonDenominator := by
  simp only [integerRowsFourTrace, Matrix.sum_apply, integerFourTrace_scaled,
    scaledRowsFourTrace, Int.cast_sum, Finset.sum_div]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_TableTrace
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Table Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem memoIntegerCopyPolynomial_spec {D T : ℕ} (hD : D ≤ 23) (hT : T ≤ 23)
    (r : CopyLabel D) (p j k : ℕ) (hp : p ≤ 8) (hj : j ≤ 8) (hk : k ≤ 8) :
    fastIntegerCopyPolynomial D T r.val.val p j k =
      memoIntegerCopyPolynomial D T r.val.val p j k := by
  have hr := r.val.isLt
  unfold fastIntegerCopyPolynomial memoIntegerCopyPolynomial
  split_ifs with hh
  · rw [memoUnitCoupling_spec _ _ _ (by omega) (by omega) (by omega),
      memoUnitCoupling_spec _ _ _ (by omega) (by omega) (by omega)]
  · rfl

theorem memoScaledFourTrace_spec {D : ℕ} (hD : D ≤ 23) (t : Fin 8) (r s : CopyLabel D) :
    scaledFourTrace D t r s = memoScaledFourTrace D t r s := by
  unfold scaledFourTrace memoScaledFourTrace
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  have hb := rowEntry_bounds b
  have hc := rowEntry_bounds c
  rw [memoIntegerCopyPolynomial_spec hD (rowFourLevel_le b c) r _ _ _ (by omega) hb.2.1 hc.2.2.1,
    memoIntegerCopyPolynomial_spec hD (rowFourLevel_le b c) s _ _ _ (by omega) hc.2.1 hb.2.2.1]

theorem integerRowsFourTrace_memo {D : ℕ} (hD : D ≤ 23) (r s : CopyLabel D) :
    integerRowsFourTrace D r s = (memoScaledRowsFourTrace D r s : ℚ) / fourCommonDenominator := by
  rw [integerRowsFourTrace_scaled]
  unfold scaledRowsFourTrace memoScaledRowsFourTrace
  simp only [memoScaledFourTrace_spec hD]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NumericTrace
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem sum_table {α β : Type*} [Fintype α] (ls : List α) (hn : ls.Nodup)
    (tabs : List β) (g : α → β) (hu : (Finset.univ : Finset α) = ⟨(ls : Multiset α), Multiset.coe_nodup.mpr hn⟩)
    (hg : ls.map g = tabs) (f : β → ℤ) :
    ∑ x, f (g x) = (tabs.map f).sum := by
  rw [hu, Finset.sum_mk, Multiset.map_coe, Multiset.sum_coe, ← hg]
  simp only [List.map_map, Function.comp_def]

theorem numericRow_sum (t : Fin 8) (f : NumericRowEntry → ℤ) :
    ∑ b : RowEntry t.val, f (rowToNumeric t b) = ((numericRowData t).map f).sum := by
  fin_cases t
  · exact sum_table rowEntryList_0 (by decide) numericRowData_0 _ rowEntryChecked_0 numericRowDataChecked_0 f
  · exact sum_table rowEntryList_1 (by decide) numericRowData_1 _ rowEntryChecked_1 numericRowDataChecked_1 f
  · exact sum_table rowEntryList_2 (by decide) numericRowData_2 _ rowEntryChecked_2 numericRowDataChecked_2 f
  · exact sum_table rowEntryList_3 (by decide) numericRowData_3 _ rowEntryChecked_3 numericRowDataChecked_3 f
  · exact sum_table rowEntryList_4 (by decide) numericRowData_4 _ rowEntryChecked_4 numericRowDataChecked_4 f
  · exact sum_table rowEntryList_5 (by decide) numericRowData_5 _ rowEntryChecked_5 numericRowDataChecked_5 f
  · exact sum_table rowEntryList_6 (by decide) numericRowData_6 _ rowEntryChecked_6 numericRowDataChecked_6 f
  · exact sum_table rowEntryList_7 (by decide) numericRowData_7 _ rowEntryChecked_7 numericRowDataChecked_7 f

theorem memoScaledFourTrace_numeric (D : ℕ) (t : Fin 8) (r s : CopyLabel D) :
    memoScaledFourTrace D t r s = numericFourTrace D t r.val.val s.val.val := by
  unfold memoScaledFourTrace numericFourTrace
  congr 1
  rw [← numericRow_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← numericRow_sum]
  rfl

theorem integerRowsFourTrace_numeric {D : ℕ} (hD : D ≤ 23) (r s : CopyLabel D) :
    integerRowsFourTrace D r s = (numericRowsFourTrace D r.val.val s.val.val : ℚ) / fourCommonDenominator := by
  rw [integerRowsFourTrace_memo hD]
  unfold memoScaledRowsFourTrace numericRowsFourTrace
  simp only [memoScaledFourTrace_numeric]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FasterTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Faster Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem numericRowTerm_short (D t r s : ℕ) (b c : NumericRowEntry) :
    numericRowTerm D t r s b c = shortNumericRowTerm D t r s b c := by
  unfold numericRowTerm shortNumericRowTerm
  dsimp only
  split_ifs <;> simp_all

theorem directIntegerSum_spec {α : Type*} (f : α → ℤ) (ls : List α) :
    (ls.map f).sum = directIntegerSum f ls := by
  induction ls with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, List.sum_cons, directIntegerSum, ih]

theorem numericFourTrace_short (D : ℕ) (t : Fin 8) (r s : ℕ) :
    numericFourTrace D t r s = shortNumericFourTrace D t r s := by
  simp only [numericFourTrace, shortNumericFourTrace, numericRowTerm_short, directIntegerSum_spec]

theorem integerRowsFourTrace_short {D : ℕ} (hD : D ≤ 23) (r s : CopyLabel D) :
    integerRowsFourTrace D r s = (shortNumericRowsFourTrace D r.val.val s.val.val : ℚ) / fourCommonDenominator := by
  rw [integerRowsFourTrace_numeric hD]
  simp only [numericRowsFourTrace, numericFourTrace_short, Fin.sum_univ_succ]
  simp only [shortNumericRowsFourTrace]
  congr 2
  simp only [Fin.isValue, Fin.succ_zero_eq_one]
  abel

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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate07
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate07. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_7 (r s : CopyLabel 7) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 7 r s = fourYData_7 r s := by
  rw [integerRowsFourTrace_short (by decide)]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_7_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · have h : (7:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_7_3_1
  · exact fourYNumber_7_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_7_5_1
  · exact fourYNumber_7_5_3
  · exact fourYNumber_7_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_7_7_1
  · exact fourYNumber_7_7_3
  · exact fourYNumber_7_7_5
  · exact fourYNumber_7_7_7

theorem fourYChecked_7_oai (r s : CopyLabel 7) :
    integerRowsFourTrace 7 r s = fourYData_7 r s := by
  have hh : ∀ r s : CopyLabel 7, fourYData_7 r s = fourYData_7 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_7 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_7 s r (by omega), hh]

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYChecked_7_oai := @OAI.LaughlinFock.fourYChecked_7_oai
