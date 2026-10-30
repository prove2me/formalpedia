-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanFormula_eq_scalarEntry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:52:23.737831+00:00
-- url     : https://prove2.me/submissions/5d942152-c254-4a7b-9308-08e33cf3b403

import Mathlib
import Definitions.Def_OAIQ081S055
import Definitions.Def_OAIQ081S064

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
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

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes Polynomial
open scoped BigOperators

variable {r Q Δ : ℕ} {K : Type*} [Field K]

theorem joint_anchor_nonfixed (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u : Joint t g i) : u.val.head t ≠ u.val.slot i t := by
  intro h
  exact u.property.2 (h.symm.trans u.property.1)

theorem joint_anchor_not_transposed (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g i) : (u.val.slot i t, u.val.head t) ≠ pair i y.val t := by
  intro h
  exact u.property.2 ((congrArg Prod.fst h).trans y.property.1)

theorem allCompatible_iff_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g i) :
    AllCompatible i u.val y.val ↔ Compatible i t u.val y.val := by
  constructor
  · rintro ⟨hs, hp⟩
    exact ⟨hs, (hp t).resolve_right (joint_anchor_not_transposed i t g u y),
      fun l _ => hp l⟩
  · rintro ⟨hs, ht, hp⟩
    refine ⟨hs, fun l => ?_⟩
    by_cases h : l = t
    · subst l
      exact Or.inl ht
    · exact hp l h

theorem allUnchanged_eq_insert_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g i) (hc : Compatible i t u.val y.val) :
    allUnchanged i u.val y.val = insert t (unchanged i t u.val y.val) := by
  ext l
  by_cases h : l = t
  · subst l
    simp [allUnchanged, joint_anchor_nonfixed i t g u, hc.2.1]
  · simp [allUnchanged, unchanged, MatrixSupport.activePositions, h]

theorem allTransposed_eq_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g i) :
    allTransposed i u.val y.val = transposed i t u.val y.val := by
  ext l
  by_cases h : l = t
  · subst l
    simp [allTransposed, transposed, MatrixSupport.activePositions,
      joint_anchor_not_transposed i t g u y]
  · simp [allTransposed, transposed, MatrixSupport.activePositions, h]

/-- Remove one token from the physical all-coordinate unchanged counter. -/
theorem allUnchanged_card_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g i) (hc : AllCompatible i u.val y.val) :
    (allUnchanged i u.val y.val).card = (unchanged i t u.val y.val).card + 1 := by
  have ht : t ∉ unchanged i t u.val y.val := by
    simp [unchanged, MatrixSupport.activePositions]
  rw [allUnchanged_eq_insert_joint i t g u y ((allCompatible_iff_joint i t g u y).mp hc),
    Finset.card_insert_of_notMem ht]

end SubexponentialSAT.Subexp.MatrixEntryKernel

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
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

end SubexponentialSAT.Subexp.MatrixEntryEvaluation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixExtendedEntrySemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact joint-membership meaning of the three selected-color comparisons. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

open MulticolorTypes

variable {r Q Δ : ℕ}

theorem anchorValid_iff_joint (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    anchorValid i t u y ↔ u ∈ joint t (y.head t) i ∧ y ∈ joint t (y.head t) i := by
  simp [anchorValid, and_assoc]

end SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramEntrySemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Convert the paid all-coordinate classifier's counters to the literal
integer matrix entry after the paid anchor guard succeeds. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixScanProgram SubexponentialSAT.Subexp.MatrixEntryEvaluation
open SubexponentialSAT.Subexp.MatrixEntryKernel SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

variable {r Q : ℕ}

/-- The physical scan includes the anchor; its unchanged count therefore loses
exactly one token before the scalar preparation program is called. -/
theorem scanFormula_eq_scalarEntry_oai (A R : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1) (ha : anchorValid (0 : Fin 1) t u y) :
    (if AllCompatible (0 : Fin 1) u y then
      LayoutCoefficientAlgorithm.scalarSum A R
        (unchangedCount (rows (0 : Fin 1) u y)-1)
        (transposedCount (rows (0 : Fin 1) u y)) else 0) =
      LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u y := by
  have hj := (anchorValid_iff_joint (0 : Fin 1) t u y).mp ha
  let uj : Joint t (y.head t) (0 : Fin 1) := ⟨u,hj.1⟩
  let yj : Joint t (y.head t) (0 : Fin 1) := ⟨y,hj.2⟩
  have hi : AllCompatible (0 : Fin 1) u y ↔ Compatible (0 : Fin 1) t u y :=
    allCompatible_iff_joint (0 : Fin 1) t (y.head t) uj yj
  rw [unchangedCount_rows,transposedCount_rows]
  unfold LayoutCoefficientAlgorithm.scalarEntry
  by_cases hc : AllCompatible (0 : Fin 1) u y
  · have hc' := hi.mp hc
    rw [ite_eq_left hc,ite_eq_left hc',
      allUnchanged_card_joint (0 : Fin 1) t (y.head t) uj yj hc,
      allTransposed_eq_joint (0 : Fin 1) t (y.head t) uj yj]
    simp [uj,yj]
  · have hc' : ¬ Compatible (0 : Fin 1) t u y := fun h => hc (hi.mpr h)
    simp [hc,hc']

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanFormula_eq_scalarEntry_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanFormula_eq_scalarEntry_oai
