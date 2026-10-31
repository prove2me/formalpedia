-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.bodyBudget_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:34:48.982216+00:00
-- url     : https://prove2.me/submissions/349547a7-a644-43df-89a2-bf0b0c7593d9

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
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

theorem signatureValue_length_bound (W bits : List Bool) (rows : List (List (List Bool))) (B : ℕ)
    (hl : ∀ row∈rows,row.length=bits.length)
    (hb : ∀ row∈rows,∀ x∈row,x.length ≤ B) :
    (signatureValue W bits rows).length ≤ rows.length*(2*(widthBound W bits.length B+1)+1) := by
  have hs : ∀ x∈(rows.map (rowKey W bits)).reverse, x.length ≤ widthBound W bits.length B+1 := by
    intro x hx
    obtain ⟨row,hr,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
    have hrw := rowWidth_bound W row B (hb row hr)
    rw [hl row hr] at hrw
    exact (rowKey_length_bound W bits row (hl row hr)).trans (Nat.add_le_add_right hrw 1)
  simpa [signatureValue] using words_length_bound (rows.map (rowKey W bits)).reverse
    (widthBound W bits.length B+1) hs

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete correction-mask checking for a head rescan. This local routine
preserves its input masters and charges every stack at every source prefix. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

theorem widthBound_le_polynomial (W : List Bool) (h B : ℕ)
    (hW : W.length≤B) (hh : h≤B) : widthBound W h B≤widthPolynomial B := by
  dsimp [widthBound,widthPolynomial]
  gcongr

theorem rowBound_le_polynomial (W bits : List Bool) (B : ℕ)
    (hW : W.length≤B) (hh : bits.length≤B) :
    signatureRowBound W bits.length B ≤ rowPolynomial B := by
  have hw := widthBound_le_polynomial W bits.length B hW hh
  dsimp [signatureRowBound,rowCostBound,rowPolynomial]
  gcongr

/-- Uniform over every candidate, including losing checks. The desired key
may be any retained word; the current complete integer key is computed and charged. -/
theorem budget_uniform (W bits wanted : List Bool) (rows : List (List (List Bool))) (B : ℕ)
    (hlen : ∀ row ∈ rows,row.length=bits.length)
    (hwidth : ∀ row ∈ rows,∀ x ∈ row,x.length≤B)
    (hW : W.length≤B) (hh : bits.length≤B) (hwanted : wanted.length≤B)
    (hmatrix : (words (rows.map words)).length≤B) (hrows : rows.length≤B) :
    budget W bits rows wanted≤gatePolynomial B := by
  have hc := AttainedSignatureProgram.cost_le W bits rows B hlen hwidth
  have hk := signatureValue_length_bound W bits rows B hlen hwidth
  have hr := rowBound_le_polynomial W bits B hW hh
  have hw := widthBound_le_polynomial W bits.length B hW hh
  calc
    budget W bits rows wanted ≤
      7*(words (rows.map words)).length+rows.length*(signatureRowBound W bits.length B+2)+
        20*(rows.length*(2*(widthBound W bits.length B+1)+1))+
          9*wanted.length+29*bits.length+60 := by
      dsimp [budget]
      omega
    _ ≤ gatePolynomial B := by
      dsimp [gatePolynomial]
      calc
        _ ≤ 7*B+B*(rowPolynomial B+2)+20*(B*(2*(widthPolynomial B+1)+1))+
          9*B+29*B+60 := by gcongr
        _ = _ := by omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

theorem sourceLength_le (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length≤B) : sourceLength a≤6*B := by
  have h0 := ha 864; have h1 := ha 859; have h2 := ha 865
  have h3 := ha 866; have h4 := ha 867; have h5 := ha 868
  dsimp [sourceLength]
  omega

/-- Every candidate, successful or losing, is charged within one fixed
polynomial plus the separately charged accepted factor calculation. -/
theorem bodyBudget_uniform_oai (a : Data) (rows : List (List (List Bool))) (B acceptedCost : ℕ)
    (hmatrix : a.stacks 865=words (rows.map words))
    (hlen : ∀ row ∈ rows,row.length=(a.stacks 859).length)
    (hwidth : ∀ row ∈ rows,∀ x ∈ row,x.length≤B)
    (hrows : rows.length≤B) (ha : ∀ i, (a.stacks i).length≤B) :
    HeadGate.budget (a.stacks 864) (a.stacks 859) rows (a.stacks 866)+
      9*sourceLength a+acceptedCost+8*(a.stacks 859).length+58≤
      bodyPolynomial B+acceptedCost := by
  have hm : (words (rows.map words)).length≤B := by rw [←hmatrix]; exact ha 865
  have hg := HeadGate.budget_uniform (a.stacks 864) (a.stacks 859) (a.stacks 866) rows B
    hlen hwidth (ha 864) (ha 859) (ha 866) hm hrows
  have hs := sourceLength_le a B ha
  have hh := ha 859
  dsimp [bodyPolynomial]
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.bodyBudget_uniform_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.bodyBudget_uniform_oai
