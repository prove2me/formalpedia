-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.generated_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:57:36.74562+00:00
-- url     : https://prove2.me/submissions/d3cbb6d6-2ba3-4886-99cd-1aced879573b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S179
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_rowCommand_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterNormalizeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual normalization of a positive binary counter word

The logarithm preparer reverses its input and removes high zeroes together
with the leading one. This wrapper physically restores that one and reverses
the remaining word. Positive inputs therefore retain their exact value and
have width log2(value)+1. All three registers and both work stacks are clean
at return, even when the incoming registers are arbitrary.
-/

namespace SubexponentialSAT.CounterNormalizeProgram

open BitProgram StructuredProgram StructuredCalls CounterPrograms

theorem normalized_value (bits : List Bool) (hp : 0 < value bits) :
    value (normalized bits) = value bits := by
  induction bits using List.reverseRecOn with
  | nil => simp [value] at hp
  | append_singleton bits bit ih =>
    cases bit with
    | false =>
      have hp' : 0 < value bits := by
        simpa [SubexpParameterProgram.value_append, value] using hp
      simpa [normalized, List.reverse_append, SubexpParameterProgram.trimTail,
        SubexpParameterProgram.value_append, value] using ih hp'
    | true =>
      simp [normalized, List.reverse_append, SubexpParameterProgram.trimTail]

theorem normalized_length (bits : List Bool) :
    (normalized bits).length = Nat.log2 (value bits) + 1 := by
  simp [normalized, SubexpParameterProgram.trimTail_reverse_length]

theorem normalized_eq_fixedBits (bits : List Bool) (hp : 0 < value bits) :
    normalized bits = SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits) := by
  have hcap : value bits < 2 ^ (Nat.log2 (value bits) + 1) := by
    simpa only [normalized_value bits hp, normalized_length] using
      SubexpParameterProgram.value_lt_two_pow_length (normalized bits)
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · rw [normalized_length, SubexpLiftRing.fixedBits_length]
  · rw [SubexpLiftRing.toNat_fixedBits_of_lt _ _ hcap,
      ← CounterPrograms.value_eq_toNat]
    exact normalized_value bits hp

end SubexponentialSAT.CounterNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit polynomial bounds for the physical integer-signature scan. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram
open SubexponentialSAT.Subexp.MatrixProgramSupport

theorem words_length_bound (xs : List (List Bool)) (B : ℕ)
    (hb : ∀ x∈xs,x.length ≤ B) : (words xs).length ≤ xs.length*(2*B+1) := by
  induction xs with
  | nil => simp [words]
  | cons x xs ih =>
      have hx := hb x (by simp)
      have ht := ih (fun y hy => hb y (by simp [hy]))
      simp only [words,List.length_append,Encoding.length_frame,List.length_cons]
      nlinarith

theorem sum_lengths_bound (xs : List (List Bool)) (B : ℕ)
    (hb : ∀ x∈xs,x.length ≤ B) : (xs.map List.length).sum ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hb x (by simp)
      have ht := ih (fun y hy => hb y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

theorem rowWidth_bound (W : List Bool) (xs : List (List Bool)) (B : ℕ)
    (hb : ∀ x∈xs,x.length ≤ B) : rowWidth W xs [true] ≤ widthBound W xs.length B := by
  have hs := sum_lengths_bound xs B hb
  simp only [rowWidth,List.length_singleton,widthBound]
  nlinarith

theorem rowKey_length_bound (W bits : List Bool) (row : List (List Bool))
    (hl : row.length=bits.length) :
    (rowKey W bits row).length ≤ rowWidth W row [true]+1 := by
  obtain ⟨t,ht,rf,out,he,hv,hlen⟩ := rowCommand_eval (fun _ => false) W row bits [true] hl
  have hv' : SubexponentialSAT.BinaryArithmetic.toNat out = 1+rowValue W row bits := by
    simpa [SubexponentialSAT.BinaryArithmetic.toNat] using hv
  have hp : 0 < SubexponentialSAT.CounterPrograms.value out := by
    rw [SubexponentialSAT.CounterPrograms.value_eq_toNat,hv']; omega
  have hn := SubexponentialSAT.CounterNormalizeProgram.normalized_eq_fixedBits out hp
  have htrim := SubexponentialSAT.SubexpParameterProgram.trimTail_length_le out.reverse
  have heq : rowKey W bits row = SubexponentialSAT.CounterNormalizeProgram.normalized out := by
    rw [hn]
    simp only [rowKey,canonical,SubexponentialSAT.CounterPrograms.value_eq_toNat,hv']
  rw [heq]
  simp only [SubexponentialSAT.CounterNormalizeProgram.normalized,List.length_reverse,List.length_cons]
  simp only [List.length_reverse] at htrim
  omega

theorem canonicalRowBudget_bound (W : List Bool) (row : List (List Bool)) (B : ℕ)
    (hb : ∀ x∈row,x.length ≤ B) : canonicalRowBudget W row ≤ rowCostBound W row.length B := by
  have hw := rowWidth_bound W row B hb
  unfold canonicalRowBudget rowBudget rowCostBound
  gcongr

theorem signatureStepCost_bound (W bits : List Bool) (row : List (List Bool)) (B : ℕ)
    (hl : row.length=bits.length) (hb : ∀ x∈row,x.length ≤ B) :
    signatureStepCost W bits row ≤ signatureRowBound W bits.length B := by
  have hw := rowWidth_bound W row B hb
  have hk := (rowKey_length_bound W bits row hl).trans (Nat.add_le_add_right hw 1)
  have hr := canonicalRowBudget_bound W row B hb
  have he := words_length_bound row B hb
  rw [hl] at hk hr he
  unfold signatureStepCost signatureRowBound
  omega

theorem signatureCost_bound (W bits : List Bool) (rows : List (List (List Bool))) (B : ℕ)
    (hl : ∀ row∈rows,row.length=bits.length)
    (hb : ∀ row∈rows,∀ x∈row,x.length ≤ B) :
    signatureCost W bits rows ≤ rows.length*(signatureRowBound W bits.length B+2)+1 := by
  unfold signatureCost
  suffices hs : (List.map (fun row => signatureStepCost W bits row+2) rows).sum ≤
      rows.length*(signatureRowBound W bits.length B+2) by omega
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have hx := signatureStepCost_bound W bits row B (hl row (by simp)) (hb row (by simp))
      have ht := ih (fun r hr => hl r (by simp [hr])) (fun r hr => hb r (by simp [hr]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

theorem cost_le (W bits : List Bool) (rows : List (List (List Bool))) (B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = bits.length)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) :
    cost W bits rows ≤ 7 * (words (rows.map words)).length +
      rows.length * (signatureRowBound W bits.length B + 2) + 8 := by
  have hs := signatureCost_bound W bits rows B hlen hwidth
  dsimp [cost]
  omega

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

theorem shiftedMatrix_rowWidth {W : List Bool} {xs : List (List SignedWord)}
    {ys : List (List (List Bool))} (h : List.Forall₂ (List.Forall₂ (shiftedWord W)) xs ys)
    (width : ℕ) (hw : ∀ row∈xs, row.length=width) :
    ∀ row∈ys, row.length=width := by
  induction h with
  | nil => simp
  | @cons a y xs ys hy hys ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (shiftedWords_length hy).symm.trans (hw a (by simp))
      · exact ih (fun a ha => hw a (by simp [ha])) z hz

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorLoadBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Source-parameter bounds for the full key produced from an actual shifted
incidence matrix. Every incidence row and every retained coefficient is charged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

/-- A member word is physically contained in its framed serialization. -/
theorem member_word_length_le {xs : List (List Bool)} {x : List Bool} (hx : x ∈ xs) :
    x.length ≤ (words xs).length := by
  have h := List.le_sum_of_mem (List.mem_map.mpr ⟨x,hx,rfl⟩ :
    x.length ∈ xs.map List.length)
  rw [BucketProgram.preWords_length]
  omega

theorem coefficient_length_le {ys : List (List (List Bool))}
    {row : List (List Bool)} {x : List Bool} (hrow : row ∈ ys) (hx : x ∈ row) :
    x.length ≤ (words (ys.map words)).length :=
  (member_word_length_le hx).trans
    (member_word_length_le (List.mem_map.mpr ⟨row,hrow,rfl⟩))

theorem matrix_length_le (W : List Bool)
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {n B D L : ℕ} {js : List ℕ} {raw : List (List LayoutMatrixProgram.Pair)}
    {ys : List (List (List Bool))}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys)
    (hn : js.length ≤ n) (hW : W.length ≤ L) :
    (words (ys.map words)).length ≤ matrixBound n D B L := by
  apply (SignatureHeadLoader.shifted_matrix_word_length W hr hy).trans
  unfold matrixBound
  gcongr

theorem coefficient_bound (W : List Bool)
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {n B D L : ℕ} {js : List ℕ} {raw : List (List LayoutMatrixProgram.Pair)}
    {ys : List (List (List Bool))}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys)
    (hn : js.length ≤ n) (hW : W.length ≤ L) :
    ∀ row ∈ ys,∀ x ∈ row,x.length ≤ matrixBound n D B L := by
  intro row hrow x hx
  exact (coefficient_length_le hrow hx).trans (matrix_length_le W hr hy hn hW)

theorem key_cost_le (W bits : List Bool)
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {n B D L : ℕ} {js : List ℕ} {raw : List (List LayoutMatrixProgram.Pair)}
    {ys : List (List (List Bool))}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys)
    (hn : js.length ≤ n) (hW : W.length ≤ L) (hbits : bits.length=js.length) :
    AttainedSignatureProgram.cost W bits ys ≤ keyCostBound n D B L := by
  obtain ⟨hraw,hrow⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
  have hrows : ys.length=D := hy.length_eq.symm.trans hraw
  have hwidth : ∀ row ∈ ys,row.length=bits.length := by
    rw [hbits]
    exact BucketProgram.shiftedMatrix_rowWidth hy js.length hrow
  have hm := matrix_length_le W hr hy hn hW
  have hc := AttainedSignatureProgram.cost_le W bits ys (matrixBound n D B L)
    hwidth (coefficient_bound W hr hy hn hW)
  have hb : bits.length ≤ n := hbits ▸ hn
  have hs : BucketProgram.signatureRowBound W bits.length (matrixBound n D B L) ≤       BucketProgram.signatureRowBound (List.replicate L false) n (matrixBound n D B L) := by
    unfold BucketProgram.signatureRowBound BucketProgram.rowCostBound BucketProgram.widthBound
    simp only [List.length_replicate]
    gcongr
  rw [hrows] at hc
  exact hc.trans (by dsimp [keyCostBound]; gcongr)

/-- Bounds consumed by the paid per-head evaluator. Only the actual generated
matrix relation, actual word lengths and fixed source scalars enter. -/
theorem generated_bounds_oai (s : LeafHeadSetupProgram.Native.Inputs) (z L : ℕ)
    (W bits : List Bool) (raw : List (List LayoutMatrixProgram.Pair))
    (ys : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys)
    (hW : W.length ≤ L)
    (hbits : bits.length=(LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z).length) :
    (words (ys.map words)).length ≤ matrixEnvelope s L ∧
      (∀ row ∈ ys,∀ x ∈ row,x.length ≤ matrixEnvelope s L) ∧
      16*(W.length+bits.length+(words (ys.map words)).length)+
        AttainedSignatureProgram.cost W bits ys+1 ≤ keyEnvelope s L := by
  have hn := LeafHeadSetupProgram.Bounds.selectedHeads_length s.n s.rows s.low z
  have hm := matrix_length_le W hr hy hn hW
  have hc := key_cost_le W bits hr hy hn hW hbits
  have hb : bits.length ≤ s.n := hbits ▸ hn
  refine ⟨hm,coefficient_bound W hr hy hn hW,?_⟩
  dsimp only [keyEnvelope,matrixEnvelope]
  dsimp only [keyCostBound] at hc
  omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.generated_bounds_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.generated_bounds_oai
