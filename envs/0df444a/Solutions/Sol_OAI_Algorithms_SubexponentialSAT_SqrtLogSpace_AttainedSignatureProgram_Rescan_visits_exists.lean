-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.visits_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:19:49.681172+00:00
-- url     : https://prove2.me/submissions/5fbcd938-7db3-4bb7-a571-25516c8ed020

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_rowCommand_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_body_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterWidth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Width preservation below a binary overflow boundary

The input word may contain high zero bits. This lemma applies to actual ripple
increment results and does not assume a canonical binary representation.
-/

namespace SubexponentialSAT.CounterPrograms

/-- Increment stays within an n-bit word when its new value is below 2^n. -/
theorem increment_length_le_of_lt (bs : List Bool) (n : ℕ)
    (hlen : bs.length ≤ n) (hvalue : value bs + 1 < 2 ^ n) :
    (ripple true bs).length ≤ n := by
  induction n generalizing bs with
  | zero =>
      have he : bs = [] := List.length_eq_zero_iff.mp (by omega)
      subst bs
      simp at hvalue
  | succ n ih =>
      cases bs with
      | nil => simp [ripple]
      | cons bit bs =>
          cases bit with
          | false => simpa [ripple] using hlen
          | true =>
              have hl : bs.length ≤ n := by simpa using hlen
              have hv : value bs + 1 < 2 ^ n := by
                simp only [value, Bool.toNat_true, pow_succ] at hvalue
                omega
              simpa [ripple] using Nat.succ_le_succ (ih bs hl hv)

end SubexponentialSAT.CounterPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Counters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

/-- The actual ripple increment remains the next fixed-width word before overflow. -/
theorem increment_word {width : ℕ} (i : Fin (2 ^ width)) (h : i.val + 1 < 2 ^ width) :
    ripple true (wordEquiv width i).val = (wordEquiv width ⟨i.val + 1, h⟩).val := by
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · apply Nat.le_antisymm
    · exact (increment_length_le_of_lt (wordEquiv width i).val width
        (wordEquiv width i).property.le (by simpa [wordEquiv,
          ExecCNFTupleEnumeration.fixedBits_value width i i.isLt] using h)).trans_eq
          (wordEquiv width ⟨i.val + 1, h⟩).property.symm
    · have hlen : (wordEquiv width i).val.length ≤
          (ripple true (wordEquiv width i).val).length := by
        generalize (wordEquiv width i).val = xs
        induction xs with
        | nil => simp
        | cons b xs ih =>
            cases b
            · simp [ripple]
            · simp only [ripple, ↓reduceIte, Bool.not_true, List.length_cons] at *
              omega
      simpa only [(wordEquiv width i).property,
        (wordEquiv width ⟨i.val + 1, h⟩).property] using hlen
  · simp [wordEquiv, value_increment, ExecCNFTupleEnumeration.fixedBits_value, i.isLt, h]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
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

namespace Rescan

theorem bodyCost_le (W predecessor saved : List Bool) (rows : List (List (List Bool)))
    (h B : ℕ) (hp : predecessor.length = h)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) :
    bodyCost W predecessor saved rows ≤ bodyBound W saved rows h B := by
  have hr : ∀ row ∈ rows, row.length = predecessor.length := by simpa [hp] using hlen
  have hc := cost_le W predecessor rows B hr hwidth
  have hk := signatureValue_length_bound W predecessor rows B hr hwidth
  have hi := CounterPrograms.rippleCost_le true predecessor
  rw [hp] at hc hk hi
  unfold bodyCost bodyBound keyBound
  rw [hp]
  omega

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CounterLoops
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual binary counted loops whose invariant couples the current cursor to
remaining fuel. The invariant is transferred through the concrete decrement
and zero test, rather than through arbitrary changes to controller words. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CounterLoops

open BitProgram StructuredCalls CounterPrograms CounterForPrograms

/-- A measured callback can establish the next boundary invariant directly.
It is required only while the actual remaining counter value is positive. -/
theorem visits_exists_next {R S : ℕ} (p : Ports R S) (body : Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (spec : ∀ i d, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) →
      ∃ nb e, nb ≤ cost i ∧ Eval body nb d e ∧
        e.stacks p.counter = d.stacks p.counter ∧ e.stacks p.scratch = [] ∧
        I (i + 1) (nextState p e)) (fuel : ℕ) :
    ∀ i d, value (d.stacks p.counter) = fuel → d.stacks p.scratch = [] →
      d.regs (p.register 2) = !(isZero (d.stacks p.counter)) → I i d →
      ∃ costs n e, Visits p body costs n d e ∧ I (i + fuel) e ∧
        e.stacks p.scratch = [] ∧ costs.sum ≤ budgetSum cost i fuel := by
  induction fuel with
  | zero =>
      intro i d hv hs hf hi
      have hz : isZero (d.stacks p.counter) = true := (isZero_eq_true_iff _).2 hv
      exact ⟨[], 1, d, .done d (by simpa [hz] using hf) hv,
        by simpa using hi, hs, by simp [budgetSum]⟩
  | succ fuel ih =>
      intro i d hv hs hf hi
      have hp : 0 < value (d.stacks p.counter) := by omega
      have hz : isZero (d.stacks p.counter) = false := (isZero_eq_false_iff _).2 hp
      have hf' : d.regs (p.register 2) = true := by simpa [hz] using hf
      obtain ⟨nb, e, hnb, he, hc, hes, hei⟩ := spec i d hi hs hp
      have hep : 0 < value (e.stacks p.counter) := by simpa only [hc] using hp
      have hn : value ((nextState p e).stacks p.counter) = fuel := by
        rw [nextState_counter, hc]
        have hd := value_decrement hep
        rw [hc, hv] at hd
        omega
      obtain ⟨costs, nt, f, ht, hfi, hfs, hbudget⟩ :=
        ih (i + 1) (nextState p e) hn (nextState_scratch ..) (nextState_flag ..) hei
      refine ⟨nb :: costs, (nb + advanceCost p e) + nt + 1, f,
        .step hf' hp he hc hes ht, ?_, hfs, ?_⟩
      · simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hfi
      · simpa only [List.sum_cons, budgetSum] using Nat.add_le_add hnb hbudget

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CounterLoops
end

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

theorem workState_fuel_update (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel newFuel : List Bool)
    (fresh : Bool) :
    (workState regs W rows candidate saved predecessor newFuel fresh [] []).stacks =
      Function.update (workState regs W rows candidate saved predecessor fuel fresh [] []).stacks
        19 newFuel := by
  funext i
  fin_cases i <;> simp [workState]

theorem nextState_workState (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) :
    CounterForPrograms.nextState countdownPorts
      (workState regs W rows candidate saved predecessor fuel fresh [] []) =
      workState (CounterForPrograms.nextState countdownPorts
        (workState regs W rows candidate saved predecessor fuel fresh [] [])).regs
        W rows candidate saved predecessor (CounterPrograms.ripple false fuel) fresh [] [] := by
  let a := workState regs W rows candidate saved predecessor fuel fresh [] []
  have hs : (CounterForPrograms.nextState countdownPorts a).stacks =
      Function.update a.stacks 19 (CounterPrograms.ripple false fuel) := by
    funext i
    by_cases hc : i = 19
    · subst i
      rw [Function.update_self]
      exact CounterForPrograms.nextState_counter countdownPorts a
    rw [Function.update_of_ne hc]
    by_cases he : i = 20
    · subst i
      exact CounterForPrograms.nextState_scratch countdownPorts a
    exact (CounterForPrograms.nextState_outside countdownPorts a i hc he).symm
  apply congrArg (StructuredProgram.State.mk _)
  exact hs.trans (workState_fuel_update _ W rows candidate saved predecessor fuel _ fresh).symm

theorem body_scan_eval (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (i : ℕ) (hi : i < candidate.val)
    (fuel : List Bool) (regs : Fin 16 → Bool) :
    ∃ nb ≤ bodyBound W (naturalKey W rows h candidate) rows h B, ∃ rb,
      Eval body nb
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h i) fuel
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate i)) [] [])
        (workState rb W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h (i + 1)) fuel
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate (i + 1))) [] []) := by
  have hil : i < 2 ^ h := hi.trans candidate.isLt
  have hinext : i + 1 < 2 ^ h := by have := candidate.isLt; omega
  let current := ExecCNFTupleEnumeration.fixedBits h i
  let saved := naturalKey W rows h candidate
  let fresh := !(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate i)
  obtain ⟨nb, hnb, rb, hb⟩ := body_eval regs W rows
    (ExecCNFTupleEnumeration.fixedBits h candidate) saved current fuel fresh
    (by simpa [current] using hlen)
  have hbound : nb ≤ bodyBound W saved rows h B :=
    hnb.trans (bodyCost_le W current saved rows h B (by simp [current]) hlen hwidth)
  have hword : CounterPrograms.ripple true current =
      ExecCNFTupleEnumeration.fixedBits h (i + 1) :=
    Counters.increment_word (⟨i, hil⟩ : Fin (2 ^ h)) hinext
  have hfresh : (fresh && !decide (signatureValue W current rows = saved)) =
      !(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate (i + 1)) := by
    simp [AttainedSignatures.duplicateScan, fresh, saved, current, naturalKey, Bool.not_or]
    rfl
  rw [hword, hfresh] at hb
  exact ⟨nb, hbound, rb, hb⟩

theorem scan_spec (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) (candidate : Fin (2 ^ h)) :
    ∀ i a, ScanInvariant W rows h candidate i a → a.stacks countdownPorts.scratch = [] →
      0 < CounterPrograms.value (a.stacks countdownPorts.counter) →
      ∃ nb e, nb ≤ bodyBound W (naturalKey W rows h candidate) rows h B ∧ Eval body nb a e ∧
        e.stacks countdownPorts.counter = a.stacks countdownPorts.counter ∧
        e.stacks countdownPorts.scratch = [] ∧
        ScanInvariant W rows h candidate (i + 1) (CounterForPrograms.nextState countdownPorts e) := by
  intro i a hI _ hp
  obtain ⟨fuel, hl, hv, he⟩ := hI
  have hcounter : a.stacks countdownPorts.counter = fuel :=
    congrArg (fun d : Data => d.stacks countdownPorts.counter) he
  have hp' : 0 < CounterPrograms.value fuel := by simpa only [hcounter] using hp
  have hi : i < candidate.val := by omega
  obtain ⟨nb, hnb, rb, hb⟩ := body_scan_eval W rows h B hlen hwidth candidate i hi fuel a.regs
  let e := workState rb W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h (i + 1)) fuel
    (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate (i + 1))) [] []
  refine ⟨nb, e, hnb, ?_, ?_, rfl, ?_⟩
  · exact Eq.mpr (congrArg (fun d : Data => Eval body nb d e) he) hb
  · exact hcounter.symm
  · refine ⟨CounterPrograms.ripple false fuel,
      (CounterPrograms.decrement_length hp').trans hl, ?_, ?_⟩
    · have hd := CounterPrograms.value_decrement hp'
      omega
    · exact nextState_workState rb W rows _ _ _ fuel _

theorem visits_exists_oai (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (remaining : ℕ)
    (i : ℕ) (fuel : List Bool) (regs : Fin 16 → Bool)
    (htotal : i + remaining = candidate.val) (hl : fuel.length = h)
    (hv : CounterPrograms.value fuel = remaining)
    (hf : regs 15 = !(CounterPrograms.isZero fuel)) :
    ∃ costs n out,
      CounterForPrograms.Visits countdownPorts body costs n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h i) fuel
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate i)) [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h candidate)
          (List.replicate h false)
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) ∧
      costs.sum ≤ remaining * bodyBound W (naturalKey W rows h candidate) rows h B := by
  let a := workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h i) fuel
    (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate i)) [] []
  have hI : ScanInvariant W rows h candidate i a := ⟨fuel, hl, by omega, rfl⟩
  obtain ⟨costs, n, e, hrun, hIe, _, hcost⟩ := CounterLoops.visits_exists_next
    countdownPorts body (ScanInvariant W rows h candidate)
    (fun _ => bodyBound W (naturalKey W rows h candidate) rows h B)
    (scan_spec W rows h B hlen hwidth candidate) remaining i a hv rfl hf hI
  obtain ⟨finalFuel, hfl, hfv, he⟩ := hIe
  have hzero : CounterPrograms.value finalFuel = 0 := by omega
  have hz : finalFuel = List.replicate h false :=
    ExecCNFTupleEnumeration.word_eq_of_length_value (by simpa using hfl) (by simpa using hzero)
  rw [htotal, hz] at he
  rw [he] at hrun
  rw [CounterForPrograms.budgetSum_const] at hcost
  exact ⟨costs, n, e.regs, hrun, hcost⟩


end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.visits_exists_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.visits_exists_oai
