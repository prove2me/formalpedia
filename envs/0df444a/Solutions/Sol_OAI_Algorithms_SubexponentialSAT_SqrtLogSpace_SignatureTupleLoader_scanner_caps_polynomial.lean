-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.scanner_caps_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:16:31.009391+00:00
-- url     : https://prove2.me/submissions/942bb35c-93c6-4be3-af27-9e9e9ec31b19

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S168

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureRescan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual bounded-word predecessor rescan and its uniform source-prefix storage. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

/-- Both concrete resource expressions have one fixed degree, independent of
head width, matrix dimensions, coefficient values and the candidate cursor. -/
theorem budgets_le_monomial (W : List Bool) (rows : List (List (List Bool))) (h B S : ℕ)
    (hS : 1 ≤ S) (hW : W.length ≤ S) (hd : rows.length ≤ S) (hh : h ≤ S)
    (hB : B ≤ S) (hM : (words (rows.map words)).length ≤ S) :
    polynomialBudget W rows h B ≤ 100000 * S ^ 6 ∧
      spaceBudget W rows h B ≤ 100000 * S ^ 6 := by
  let width := 1 + S * (S + 1 + S)
  let row := (S + 1) * (200 * (width + 2) ^ 2 + 34) + 9 * width + 22
  let signature := 9 * (S * (2 * S + 1)) + 7 + (7 * S + 5) + 2 +
    (row + 1) + 8 * (width + 1) + 8
  let key := S * (2 * (width + 1) + 1)
  let total := 14 * S + 2 * (S * (signature + 2)) + 38 * key + 62 * S + 129
  have hp : polynomialBudget W rows h B ≤ total := by
    dsimp [polynomialBudget, keyBound, signatureRowBound, rowCostBound, widthBound,
      total, signature, row, key, width]
    gcongr
  have hk : keyBound W h rows.length B ≤ key := by
    dsimp [keyBound, widthBound, key, width]
    gcongr
  have hs : spaceBudget W rows h B ≤ 40 * (S + S + key + 3 * S + 1) + total + 16 := by
    unfold spaceBudget
    gcongr
  have h0 : 1 ≤ S ^ 6 := one_le_pow₀ hS
  have h1 : S ≤ S ^ 6 := Nat.le_self_pow (by decide) _
  have h2 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by decide)
  have h3 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by decide)
  have h4 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by decide)
  have h5 : S ^ 5 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by decide)
  dsimp [total, signature, row, key, width] at hp hs
  constructor <;> nlinarith


end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured signed row scan, followed by a physical frame-order repair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedWords_length {W : List Bool} {xs : List SignedWord} {ys : List (List Bool)}
    (h : List.Forall₂ (shiftedWord W) xs ys) : xs.length=ys.length := by
  induction h with
  | nil => rfl
  | cons h hs ih => simpa using ih

theorem shiftedWords_totalLength {W : List Bool} {xs : List SignedWord} {ys : List (List Bool)}
    (h : List.Forall₂ (shiftedWord W) xs ys) :
    (ys.map List.length).sum ≤ preOutputLength W xs := by
  induction h with
  | nil => simp [preOutputLength]
  | cons h hs ih =>
      simp only [List.map_cons,List.sum_cons,preOutputLength] at *
      exact Nat.add_le_add h.2 ih

theorem preWords_length (ys : List (List Bool)) :
    (words ys).length=2*(ys.map List.length).sum+ys.length := by
  induction ys with
  | nil => simp [words]
  | cons y ys ih => simp [words,Encoding.length_frame,ih]; omega

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete row-major signed matrix preprocessor. All input and output
frames are scanned by fixed instructions; the original bound word is retained. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedMatrix_lengths {W : List Bool} {rows : List (List SignedWord)}
    {ys : List (List (List Bool))} (h : List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys) :
    rows.length=ys.length ∧ ((ys.map words).map List.length).sum ≤ preMatrixPayload W rows := by
  induction h with
  | nil => simp [preMatrixPayload]
  | cons h hs ih =>
      have hl := shiftedWords_totalLength h
      have hn := shiftedWords_length h
      simp only [List.length_cons,List.map_cons,List.sum_cons,preWords_length,preMatrixPayload] at *
      constructor <;> omega

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer semantics and explicit polynomial bounds for the concrete
signed-coefficient preprocessing machine. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.MatrixProgramSupport

theorem preStepCost_le (W : List Bool) (a : SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hP : a.1.length ≤ L) (hN : a.2.length ≤ L) :
    preStepCost W a ≤ 6000*(L+1)^2 := by
  have hsum : W.length+a.2.length+a.1.length+1 ≤ 3*L+1 := by omega
  have hsq := Nat.pow_le_pow_left hsum 2
  dsimp [preStepCost]
  nlinarith

theorem preRow_inputs (W : List Bool) (xs : List SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hb : preWordsBounded L xs) :
    preScanCost W xs ≤ (xs.length+1)*(6000*(L+1)^2+2) ∧
    preOutputLength W xs ≤ xs.length*(3*L+1) ∧
    (signedWords xs).length ≤ xs.length*(4*L+2) := by
  induction xs with
  | nil => simp [preScanCost,preOutputLength,signedWords]
  | cons a xs ih =>
      have ha := hb a (by simp)
      have ht := ih (fun x hx => hb x (by simp [hx]))
      have hc := preStepCost_le W a L hW ha.1 ha.2
      rcases a with ⟨P,N⟩
      simp only [preScanCost,preOutputLength,List.map_cons,List.sum_cons,
        List.length_cons,signedWords,List.length_append,Encoding.length_frame] at *
      constructor
      · nlinarith [ht.1]
      constructor
      · nlinarith [ht.2.1]
      · nlinarith [ht.2.2]

theorem preRowCost_le (W : List Bool) (xs : List SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hb : preWordsBounded L xs) :
    preRowCost W xs ≤ 7000*(xs.length+1)*(L+1)^2 := by
  have h := preRow_inputs W xs L hW hb
  have hlin : 3*L+1 ≤ 3*(L+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_left xs.length hlin
  have hs : 1 ≤ (L+1)^2 := by nlinarith
  have hn := Nat.mul_le_mul_left xs.length hs
  dsimp [preRowCost]
  nlinarith [h.1,h.2.1]

theorem preMatrixStepCost_le (W : List Bool) (row : List SignedWord) (L : ℕ)
    (hW : W.length ≤ L) (hb : preWordsBounded L row) :
    preMatrixStepCost W row ≤ 8000*(row.length+1)*(L+1)^2 := by
  have h := preRow_inputs W row L hW hb
  have hr := preRowCost_le W row L hW hb
  have hlin : 4*L+2 ≤ 4*(L+1)^2 := by nlinarith
  have hlin' : 3*L+1 ≤ 3*(L+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_left row.length hlin
  have hh' := Nat.mul_le_mul_left row.length hlin'
  have hs : 1 ≤ (L+1)^2 := by nlinarith
  have hn := Nat.mul_le_mul_left row.length hs
  dsimp [preMatrixStepCost]
  nlinarith [h.2.1,h.2.2]

theorem preMatrix_inputs (W : List Bool) (rows : List (List SignedWord)) (L h : ℕ)
    (hW : W.length ≤ L)
    (hb : ∀ row∈rows, preWordsBounded L row ∧ row.length ≤ h) :
    preMatrixScanCost W rows ≤ (rows.length+1)*(8000*(h+1)*(L+1)^2+2) ∧
    preMatrixPayload W rows ≤ rows.length*(2*h*(3*L+1)+h) := by
  induction rows with
  | nil => simp [preMatrixScanCost,preMatrixPayload]
  | cons row rows ih =>
      have hr := hb row (by simp)
      have ht := ih (fun r hr' => hb r (by simp [hr']))
      have hc := preMatrixStepCost_le W row L hW hr.1
      have hc' : preMatrixStepCost W row ≤ 8000*(h+1)*(L+1)^2 :=
        hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
      have hl := (preRow_inputs W row L hW hr.1).2.1
      have hl' := Nat.mul_le_mul_right (3*L+1) hr.2
      simp only [preMatrixScanCost,preMatrixPayload,List.map_cons,List.sum_cons,List.length_cons] at *
      constructor
      · nlinarith [ht.1]
      · nlinarith [ht.2]

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramCompatibility
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact serialization and state projection at the all-row bucket boundary. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem matrixRel_dimensions {Rel : ℕ → ℕ → Pair → Prop} {B D : ℕ} {js : List ℕ}
    {rows : List (List Pair)} (h : MatrixRel Rel B D js rows) :
    rows.length=D ∧ ∀ row ∈ rows, row.length=js.length := by
  refine ⟨?_,?_⟩
  · simpa [MatrixRel] using h.length_eq.symm
  · intro row hr
    have aux : ∀ (is : List ℕ) (rs : List (List Pair)),
        List.Forall₂ (fun j row => List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js row)
          is rs → ∀ row ∈ rs, row.length=js.length := by
      intro is rs hs
      induction hs with
      | nil => simp
      | cons hi ht ih =>
        intro row hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hi.length_eq.symm
        · exact ih row hr
    exact aux _ _ h row hr

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem count_le (p : ℕ → Bool) (n : ℕ) : count p n ≤ n := by
  simpa [count,chosenIds] using List.length_filter_le p (List.range n)

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoundsPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial cost of actual head-ID, support-mask, and factor-ID
preparation. Bounds include the real isolated-bank copy/cleanup costs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

 theorem selectedHeads_length (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ) :
    (selectedHeads n rows low z).length ≤ n :=
  HeadIdentifierProgram.count_le _ _

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

private theorem forallTwo_member {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {y : β} (hy : y∈ys) :
    ∃ x∈xs,R x y := by
  induction h with
  | nil => simp at hy
  | cons hxy ht ih =>
      rcases List.mem_cons.mp hy with rfl|hy
      · exact ⟨_,by simp,hxy⟩
      · obtain ⟨x,hx,hr⟩ := ih hy
        exact ⟨x,by simp [hx],hr⟩

theorem raw_pair_bounds {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {B D : ℕ} {js : List ℕ} {rows : List (List LayoutMatrixProgram.Pair)}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows) :
    ∀ row∈rows,BucketProgram.preWordsBounded B row := by
  intro row hrow p hp
  obtain ⟨j,_,hjr⟩ := forallTwo_member hr hrow
  obtain ⟨v,_,hvp⟩ := forallTwo_member hjr hp
  have hlen := hvp.2
  unfold LayoutMatrixProgram.pairLength at hlen
  exact ⟨by omega,by omega⟩

/-- The retained shifted matrix has D rows and every original head column.
Its size depends on physical coefficient word lengths, not their integer values. -/
theorem shifted_matrix_word_length (W : List Bool) {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {B D : ℕ} {js : List ℕ} {rows : List (List LayoutMatrixProgram.Pair)}
    {ys : List (List (List Bool))}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) rows ys) :
    (Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words)).length ≤
      D*(12*js.length*(B+W.length)+6*js.length+1) := by
  have hpairs := raw_pair_bounds hr
  obtain ⟨hrows,hwrows⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
  have hinputs := BucketProgram.preMatrix_inputs W rows (B+W.length) js.length
    (Nat.le_add_left _ _) (by
      intro row hrow
      refine ⟨?_,(hwrows row hrow).le⟩
      intro pair hpair
      have h := hpairs row hrow pair hpair
      exact ⟨h.1.trans (Nat.le_add_right _ _),h.2.trans (Nat.le_add_right _ _)⟩)
  obtain ⟨hlen,hpayload⟩ := BucketProgram.shiftedMatrix_lengths hy
  rw [BucketProgram.preWords_length,List.length_map,←hlen,hrows]
  rw [hrows] at hinputs
  nlinarith [hinputs.2]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NodeTimeSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native integer-entry and column costs are polynomials in actual
retained source-word lengths, with the full incidence count preserved. -/
namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing
open SubexponentialSAT.MulticolorTypes LayoutProgram LeafHeadSetupProgram
open LeafHeadSetupProgram.Bounds

private theorem integer_diagonal (X : ℕ) :
    EntryBank.integerBudget X X X X X X X ≤ 10000000000000*(X+1)^5 := by
  have hp (j : ℕ) (hj : j ≤ 5) : X^j ≤ (X+1)^5 :=
    (Nat.pow_le_pow_left (Nat.le_succ X) j).trans (Nat.pow_le_pow_right (by omega) hj)
  have h0 : 1 ≤ (X+1)^5 := by simpa using hp 0 (by decide)
  have h1 : X ≤ (X+1)^5 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  dsimp only [EntryBank.integerBudget,LayoutProgramScalar.termGrowth,
    LayoutSourceValuesProgram.Native.numeratorAllowance,LayoutSourceValuesProgram.Native.scalarAllowance,
    MatrixExtendedEntryProgram.guardStageCost,MatrixEntryProgram.scanStageCost,CollisionProgram.typeWidth,
    LayoutProgramScalar.FromCounts.binomialCost,LayoutProgramScalar.numeratorPrepareCost,
    LayoutProgramScalar.numeratorFoldCost,UniversalRowMismatchTypes.extractBudget]
  norm_num only [Fin.val_zero]
  conv_lhs => ring_nf
  omega

theorem integerBudget_le (r Q A R W P D X : ℕ)
    (hr : r ≤ X) (hQ : Q ≤ X) (hA : A ≤ X) (hR : R ≤ X)
    (hW : W ≤ X) (hP : P ≤ X) (hD : D ≤ X) :
    EntryBank.integerBudget r Q A R W P D ≤ 10000000000000*(X+1)^5 := by
  apply le_trans _ (integer_diagonal X)
  dsimp only [EntryBank.integerBudget, LayoutProgramScalar.termGrowth,
    LayoutSourceValuesProgram.Native.numeratorAllowance, LayoutSourceValuesProgram.Native.scalarAllowance,
    MatrixExtendedEntryProgram.guardStageCost, MatrixEntryProgram.scanStageCost, CollisionProgram.typeWidth,
    LayoutProgramScalar.FromCounts.binomialCost, LayoutProgramScalar.numeratorPrepareCost,
    LayoutProgramScalar.numeratorFoldCost, UniversalRowMismatchTypes.extractBudget, LayoutProgramScalar.termGrowth]
  gcongr

/-- The diagonal uses the encoded width, not the coefficient magnitude. -/
theorem integerLength_le (R W P D X : ℕ) (hR : R ≤ X) (hW : W ≤ X) (hP : P ≤ X) (hD : D ≤ X) :
    EntryBank.integerLength R W P D ≤ 100*(X+1)^2 := by
  unfold EntryBank.integerLength LayoutProgramScalar.termGrowth
  nlinarith [Nat.mul_le_mul hR (Nat.add_le_add (Nat.mul_le_mul_left 28 hW) (Nat.mul_le_mul_left 14 hP))]

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NodeTimeColumns
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing SubexpSetupStorage
open LeafHeadSetupProgram LeafHeadSetupProgram.Bounds
open LayoutProgram RowSelectionProgram

theorem inputBounds (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (h : Native.Ready s a) (B : ℕ) (hb : WordBound B a) : InputBounds s B := by
  have hp : (LayoutOwnerFiberProgram.stream s.plans).length ≤ B := by simpa only [h.plans] using hb 136
  have hc := Encoding.length_encodeList_lower (fun p : ℕ×ℕ => LayoutOwnerFiberProgram.pairPayload p.1 p.2) s.plans
  have hd : s.D ≤ B := by
    change s.plans.length+1 ≤ (LayoutOwnerFiberProgram.stream s.plans).length at hc
    rw [s.plans_length] at hc
    omega
  exact ⟨by simpa [h.ambient,unary] using hb 128,hd,
    by simpa [h.colors,unary] using hb 130,by simpa [h.nodes,unary] using hb 131,
    by simpa [h.order,unary] using hb 138,by simpa only [h.width] using hb 140,
    by simpa only [h.height] using hb 139,by simpa only [h.metadata] using hb 135,hp,
    by simpa [h.wordWidth,unary] using hb 132⟩

theorem columns_le {s : Native.Inputs} {B : ℕ} (h : InputBounds s B) :
    s.columnTime ≤ columnEnvelope (B+1) ∧ s.columnLength ≤ (B+1)*(100*(B+2)^2+2) := by
  let X := B+1
  have hx : B ≤ X := by dsimp [X]; omega
  have hn := h.n.trans hx
  have hd := h.D.trans hx
  have hr := h.r.trans hx
  have hq := h.Q.trans hx
  have ho := h.R.trans hx
  have hw := h.width.trans hx
  have hh := h.height.trans hx
  have hm := h.metadata.trans hx
  have hp := h.plans.trans hx
  have hqr := h.Qr.trans hx
  have hpower : s.power.1.length ≤ X := by
    simp only [Native.Inputs.power,IntegerCache.denominatorWord,List.length_append,
      List.length_replicate,List.length_singleton]
    dsimp [X]
    omega
  have hpair : pairLength s.power ≤ X := by
    simpa only [pairLength,Native.Inputs.power,List.length_nil,Nat.add_zero] using hpower
  have hlen : s.entryLength ≤ 100*(X+1)^2 := integerLength_le _ _ _ _ X ho hw hpair hpower
  have hib := integerBudget_le _ _ _ _ _ _ _ X hr hq hh ho hw hpair hpower
  have hs : s.size ≤ X*X+11*X+1 := by
    unfold Native.Inputs.size
    have hm := Nat.mul_le_mul ho hw
    omega
  have he : s.entryTime ≤ entryEnvelope X := by
    unfold Native.Inputs.entryTime Native.Inputs.lookupTime LayoutFiberSumProgram.nativeTime entryEnvelope
    have hu : 800*(s.metadata.length+s.D+1)^2+1 ≤ 800*(2*X+1)^2+1 := by gcongr ; omega
    dsimp only [Native.Inputs.entryLength] at hlen
    omega
  constructor
  · change s.columnTime ≤ columnEnvelope X
    unfold Native.Inputs.columnTime columnEnvelope
    gcongr ; omega
  · change s.D*(s.entryLength+2) ≤ X*(100*(X+1)^2+2)
    gcongr

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head reloads for the attained-signature DFS.  The matrix comes
from the fixed native integer-entry machine, and each reload restores one
fixed retained-word bound before the next candidate scan. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage


/-- The retained output cap itself is a fixed input polynomial, independent
of the caller's current storage bound and of the number of head reloads. -/
theorem retained_output_polynomial (s : Native.Inputs) (a : Data) (B : ℕ)
    (ha : Native.Ready s a) (hB : WordBound B a) :
    SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength B≤10000*(B+2)^6 := by
  let X := B+2
  have hX : 1≤X := by dsimp [X]; omega
  have hX2 : 1≤X^2 := one_le_pow₀ hX
  have h16 : X≤X^6 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1≤6)
  have h26 : X^2≤X^6 := pow_le_pow_right₀ hX (by decide)
  have h56 : X^5≤X^6 := pow_le_pow_right₀ hX (by decide)
  have h06 : 1≤X^6 := one_le_pow₀ hX
  have h13 : X≤X^3 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1≤3)
  have hi := NodeTime.inputBounds s a ha B hB
  have hc := (NodeTime.columns_le hi).2
  have hn : s.n≤X := hi.n.trans (by dsimp [X]; omega)
  have hN : s.N≤X := by
    have hb : s.N≤B := by simpa [ha.factors,unary] using hB 129
    dsimp [X]; omega
  have hD : s.D≤X := hi.D.trans (by dsimp [X]; omega)
  have hb : B≤X := by dsimp [X]; omega
  have hcol : s.columnLength≤102*X^3 := by
    apply hc.trans
    calc
      _≤X*(100*X^2+2) := by dsimp [X]; gcongr; omega
      _≤X*(102*X^2) := by gcongr; omega
      _=102*X^3 := by ring
  have hcB : s.columnLength+B≤103*X^3 := by omega
  calc
    _≤X*(2*X+2)+2+(2*X+2)*X+X*(12*X*(103*X^3)+6*X+1) := by
      unfold SignatureHeadLoader.retainedOutputBound
      gcongr
    _=1236*X^5+10*X^2+5*X+2 := by ring
    _≤10000*X^6 := by omega

section Storage
open SignatureTupleDFS SignatureTupleTraversal

theorem scanner_caps_polynomial_oai (s : Native.Inputs) (source : Data) (B z : ℕ)
    (ha : Native.Ready s source) (hB : WordBound B source) (W : List Bool) (hW : W.length≤B)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted) :
    let h := (selectedHeads s.n s.rows s.low z).length
    let C := 3*(s.columnLength+B)+1
    AttainedSignatureProgram.Rescan.polynomialBudget W shifted h C ≤ scannerEnvelope B ∧
      AttainedSignatureProgram.Rescan.spaceBudget W shifted h C ≤ scannerEnvelope B ∧
      AttainedSignatureProgram.Rescan.keyBound W h shifted.length C ≤ scannerEnvelope B := by
  dsimp only
  let X := B+2
  let C := 3*(s.columnLength+B)+1
  let R := SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength B
  let S := 1+B+s.D+s.n+C+R
  have hX : 1≤X := by dsimp [X]; omega
  have hX2 : 1≤X^2 := one_le_pow₀ hX
  have h16 : X≤X^6 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1≤6)
  have h36 : X^3≤X^6 := pow_le_pow_right₀ hX (by decide)
  have h06 : 1≤X^6 := one_le_pow₀ hX
  have hi := NodeTime.inputBounds s source ha B hB
  have hcol := (NodeTime.columns_le hi).2
  have hcol' : s.columnLength≤102*X^3 := by
    apply hcol.trans
    calc
      _≤X*(100*X^2+2) := by dsimp [X]; gcongr; omega
      _≤X*(102*X^2) := by gcongr; omega
      _=102*X^3 := by ring
  have hb : B≤X^6 := (show B≤X by dsimp [X]; omega).trans h16
  have hrCap : R≤10000*X^6 := retained_output_polynomial s source B ha hB
  have hnB := hi.n
  have hDB := hi.D
  have hS : S≤20000*X^6 := by dsimp [S,C]; omega
  have hpositive : 1≤S := by dsimp [S]; omega
  have hn : (selectedHeads s.n s.rows s.low z).length ≤ s.n := Bounds.selectedHeads_length ..
  have hlen : shifted.length=s.D := hy.length_eq.symm.trans
    (LayoutMatrixProgram.matrixRel_dimensions hr).1
  have hmatrix := SignatureHeadLoader.shifted_matrix_word_length W hr hy
  have hmatrix' : (Subexp.MatrixProgramSupport.words
      (shifted.map Subexp.MatrixProgramSupport.words)).length≤R := by
    apply hmatrix.trans
    apply le_trans (Nat.mul_le_mul_left s.D (show
      12*(selectedHeads s.n s.rows s.low z).length*(s.columnLength+W.length)+
        6*(selectedHeads s.n s.rows s.low z).length+1≤
      12*s.n*(s.columnLength+B)+6*s.n+1 by gcongr))
    dsimp [R,SignatureHeadLoader.retainedOutputBound]
    omega
  have hs := AttainedSignatureProgram.Rescan.budgets_le_monomial W shifted
    (selectedHeads s.n s.rows s.low z).length C S hpositive
    (by dsimp [S]; omega) (by rw [hlen]; dsimp [S]; omega)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hbudget : 100000*S^6 ≤ scannerEnvelope B :=
    Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left hS 6)
  have hp := hs.1.trans hbudget
  have hkey : AttainedSignatureProgram.Rescan.keyBound W
      (selectedHeads s.n s.rows s.low z).length shifted.length C≤
      AttainedSignatureProgram.Rescan.polynomialBudget W shifted
        (selectedHeads s.n s.rows s.low z).length C := by
    unfold AttainedSignatureProgram.Rescan.polynomialBudget
    omega
  exact ⟨hp,hs.2.trans hbudget,hkey.trans hp⟩

end Storage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.scanner_caps_polynomial_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.scanner_caps_polynomial_oai
