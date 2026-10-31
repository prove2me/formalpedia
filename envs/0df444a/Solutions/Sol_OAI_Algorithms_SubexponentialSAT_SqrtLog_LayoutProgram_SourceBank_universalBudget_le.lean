-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universalBudget_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:47:36.57719+00:00
-- url     : https://prove2.me/submissions/8910d5e3-b765-4e54-8000-99e1cf74a0c8

import Mathlib
import Definitions.Def_OAIQ081S168

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A scalar generating polynomial for the actual matrix entries

The coefficient of degree j equals 2^j times the j-th elementary projector
kernel. Consequently normalized coefficients need only scalar polynomial
arithmetic, with no enumeration of subsets in the eventual implementation.
-/

/-! The scalar kernel has only three nonzero local factors: 1, -X, and 1+X. -/

/-!
# Exact binomial formula for the implemented multicolor matrix

This connects scalar additions and sign changes to the very same matrix
used in the support and rank proofs. The only normalization hypothesis is
that the field has characteristic different from two.
-/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ} {K : Type*} [Field K]

theorem same_not_swap_iff (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    (pair i u l = pair i y l ∧ (u.slot i l, u.head l) ≠ pair i y l) ↔
      (u.head l ≠ u.slot i l ∧ pair i u l = pair i y l) := by
  constructor
  · rintro ⟨hs, ht⟩
    refine ⟨?_, hs⟩
    intro hf
    apply ht
    have he : (u.slot i l, u.head l) = pair i u l := by simp [pair, hf]
    exact he.trans hs
  · rintro ⟨hf, hs⟩
    refine ⟨hs, ?_⟩
    intro ht
    exact hf (congrArg Prod.fst (hs.trans ht.symm))

theorem swap_not_same_iff (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    ((u.slot i l, u.head l) = pair i y l ∧ pair i u l ≠ pair i y l) ↔
      (u.head l ≠ u.slot i l ∧ (u.slot i l, u.head l) = pair i y l) := by
  constructor
  · rintro ⟨ht, hs⟩
    refine ⟨?_, ht⟩
    intro hf
    apply hs
    have he : pair i u l = (u.slot i l, u.head l) := by simp [pair, hf]
    exact he.trans ht
  · rintro ⟨hf, ht⟩
    refine ⟨ht, ?_⟩
    intro hs
    exact hf (congrArg Prod.fst (hs.trans ht.symm))

end SubexponentialSAT.Subexp.MatrixEntryKernel

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic meaning of the two physical unary counters and the
compatibility register, including the one-hot color encoding boundary. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

theorem encodeColor_injective {r : ℕ} : Function.Injective (@encodeColor r) := by
  intro c d h
  have he := congrFun (List.ofFn_injective h) c
  simp only [decide_true] at he
  exact (of_decide_eq_true he.symm).symm

@[simp] theorem encodeColor_eq_iff {r : ℕ} (c d : Fin r) :
    encodeColor c = encodeColor d ↔ c = d := encodeColor_injective.eq_iff

theorem encodeColor_pair_eq {r : ℕ} (a b c d : Fin r) :
    encodeColor a ++ encodeColor b = encodeColor c ++ encodeColor d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    exact ⟨encodeColor_injective h1, encodeColor_injective h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem same_typedRow {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (l : Fin Q) :
    same (typedRow i u y l) = decide (u.head l = y.head l ∧ u.slot i l = y.slot i l) := by
  simp [same, typedRow, encodeColor_pair_eq]

theorem swapped_typedRow {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (l : Fin Q) :
    swapped (typedRow i u y l) = decide (u.slot i l = y.head l ∧ u.head l = y.slot i l) := by
  simp [swapped, typedRow, encodeColor_pair_eq]

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Connect the concrete scan counters and adjacent-add value to the actual
joint matrix. These are refinement lemmas for the physical component programs,
not alternative definitions of their runtime instructions. -/

namespace SubexponentialSAT.Subexp.MatrixEntryEvaluation

open MulticolorTypes MatrixScanProgram
open scoped BigOperators

variable {r Q Δ : ℕ}

theorem unchangedCount_sum (ws : List ColorRow) :
    unchangedCount ws = (ws.map (fun w => if same w && !swapped w then 1 else 0)).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [unchangedCount, ih, Nat.add_comm]

theorem transposedCount_sum (ws : List ColorRow) :
    transposedCount ws = (ws.map (fun w => if swapped w && !same w then 1 else 0)).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [transposedCount, ih, Nat.add_comm]

theorem same_pair (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    same (typedRow i u y l) = decide (MatrixEntryKernel.pair i u l = MatrixEntryKernel.pair i y l) := by
  simpa [MatrixEntryKernel.pair, Prod.mk.injEq] using same_typedRow i u y l

theorem swapped_pair (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    swapped (typedRow i u y l) = decide ((u.slot i l, u.head l) = MatrixEntryKernel.pair i y l) := by
  simpa [MatrixEntryKernel.pair, Prod.mk.injEq] using swapped_typedRow i u y l

theorem unchanged_test (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    (same (typedRow i u y l) && !swapped (typedRow i u y l)) =
      decide (u.head l ≠ u.slot i l ∧ MatrixEntryKernel.pair i u l = MatrixEntryKernel.pair i y l) := by
  apply Bool.eq_iff_iff.mpr
  simpa [same_pair, swapped_pair] using MatrixEntryKernel.same_not_swap_iff i u y l

theorem transposed_test (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    (swapped (typedRow i u y l) && !same (typedRow i u y l)) =
      decide (u.head l ≠ u.slot i l ∧ (u.slot i l, u.head l) = MatrixEntryKernel.pair i y l) := by
  apply Bool.eq_iff_iff.mpr
  simpa [same_pair, swapped_pair] using MatrixEntryKernel.swap_not_same_iff i u y l

theorem unchangedCount_rows (i : Fin Δ) (u y : UniversalType r Q Δ) :
    unchangedCount (rows i u y) = (MatrixEntryKernel.allUnchanged i u y).card := by
  rw [unchangedCount_sum]
  simp only [rows, List.map_ofFn, List.sum_ofFn, Function.comp_def, unchanged_test, decide_eq_true_eq]
  simp [MatrixEntryKernel.allUnchanged]

theorem transposedCount_rows (i : Fin Δ) (u y : UniversalType r Q Δ) :
    transposedCount (rows i u y) = (MatrixEntryKernel.allTransposed i u y).card := by
  rw [transposedCount_sum]
  simp only [rows, List.map_ofFn, List.sum_ofFn, Function.comp_def, transposed_test, decide_eq_true_eq]
  simp [MatrixEntryKernel.allTransposed]

theorem unchangedCount_le (i : Fin Δ) (u y : UniversalType r Q Δ) :
    unchangedCount (rows i u y) ≤ Q := by
  rw [unchangedCount_rows]
  have h := Finset.card_le_card (Finset.filter_subset
    (fun l : Fin Q => u.head l ≠ u.slot i l ∧
      MatrixEntryKernel.pair i u l = MatrixEntryKernel.pair i y l) Finset.univ)
  simpa [MatrixEntryKernel.allUnchanged] using h

theorem transposedCount_le (i : Fin Δ) (u y : UniversalType r Q Δ) :
    transposedCount (rows i u y) ≤ Q := by
  rw [transposedCount_rows]
  have h := Finset.card_le_card (Finset.filter_subset
    (fun l : Fin Q => u.head l ≠ u.slot i l ∧
      (u.slot i l, u.head l) = MatrixEntryKernel.pair i y l) Finset.univ)
  simpa [MatrixEntryKernel.allTransposed] using h

end SubexponentialSAT.Subexp.MatrixEntryEvaluation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The scalar callback calls the actual integer numerator program, then the
actual binary-to-ring scaler. Its integer result is never supplied as input. -/


/-! Closed correction-table construction from type metadata and integer/ring
caches. No correction-scalar table is supplied to the program or theorem. -/


/-! Uniform polynomial accounting and per-index observation of generated
correction tables. All parameters describe actual bytes and runtime counts. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators

theorem scalar_cost_le (A R Q W P n h : ℕ) (hn : n ≤ Q) (hh : h ≤ Q) :
    LayoutProgramScalar.FromCounts.totalCost A R n h W P ≤ scalarAllowance A R Q W P := by
  unfold LayoutProgramScalar.FromCounts.totalCost scalarAllowance
    LayoutProgramScalar.FromCounts.binomialCost LayoutProgramScalar.numeratorPrepareCost
    LayoutProgramScalar.numeratorFoldCost
  gcongr <;> omega

theorem numerator_cost_le {r Q : ℕ} (A R W P : ℕ) (node : Fin Q)
    (u y : UniversalType r Q 1) :
    LayoutProgram.Numerator.budget A R W P node u y ≤ numeratorAllowance r Q A R W P := by
  have hu := Subexp.MatrixEntryEvaluation.unchangedCount_le (0 : Fin 1) u y
  have hh := Subexp.MatrixEntryEvaluation.transposedCount_le (0 : Fin 1) u y
  have hs := scalar_cost_le A R Q W P
    (Subexp.MatrixScanProgram.unchangedCount (Subexp.MatrixEntryEvaluation.rows 0 u y)-1)
    (Subexp.MatrixScanProgram.transposedCount (Subexp.MatrixEntryEvaluation.rows 0 u y))
    (by omega) hh
  have hg : Subexp.MatrixExtendedEntryProgram.guardStageCost r Q 1 0 node.val ≤
      Subexp.MatrixExtendedEntryProgram.guardStageCost r Q 1 0 Q := by
    unfold Subexp.MatrixExtendedEntryProgram.guardStageCost
    gcongr
    exact node.isLt.le
  unfold LayoutProgram.Numerator.budget numeratorAllowance
  omega

theorem numeratorBudget_le {r Q : ℕ} (A R W P : ℕ) (u y : UniversalType r Q 1) :
    numeratorBudget A R W P u y ≤ Q * numeratorAllowance r Q A R W P := by
  unfold numeratorBudget
  calc
    _ ≤ ∑ _node : Fin Q, numeratorAllowance r Q A R W P := by
      exact Finset.sum_le_sum fun node _ => numerator_cost_le A R W P node u y
    _ = _ := by simp

theorem tableBudget_polynomial {r Q : ℕ} (A R W P t d : ℕ)
    (u y : UniversalType r Q 1) :
    tableBudget A R W P t d u y ≤ polynomialBudget r Q A R W P t d := by
  unfold tableBudget polynomialBudget callbackBudget
  gcongr
  exact numeratorBudget_le A R W P u y

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial resource bounds for the concrete universal source
branch. Typed table entries contribute their actual d*B bit width. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

variable {r Q d : ℕ}

theorem universalBudget_le_oai (p : Parameters r Q d) (S : ℕ) (u y : UniversalType r Q 1) :
    universalBudget p S u y ≤ uniformBudget p S := by
  have hh := LayoutSourceValuesProgram.Native.tableBudget_polynomial
    p.aWord.length p.R p.width.length (pairLength p.power) p.t d u y
  unfold universalBudget uniformBudget
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universalBudget_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universalBudget_le_oai
