-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.advance_endpoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:58:33.30979+00:00
-- url     : https://prove2.me/submissions/29cf3ca1-bdd6-4590-bd40-ce5cad2c13c0

import Mathlib
import Definitions.Def_OAIQ081S152

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

/-- Every off-counter caller stack is preserved, including cleared scratch. -/
theorem incrementResult_stacks {R S : ℕ} (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    (incrementResult p d).stacks =
      Function.update d.stacks p.counter (ripple true (d.stacks p.counter)) := by
  funext i
  by_cases hc : i = p.counter
  · subst i
    simp
  · by_cases hi : i = p.scratch
    · subst i
      simp [hc, hs]
    · rw [Function.update_of_ne hc]
      exact install_other_stack p d _ _ _ _ _ i hc hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

theorem advanceState_candidate (a : State 40 896) :
    (advanceState a).stacks candidatePorts.counter =
      CounterPrograms.ripple true (a.stacks candidatePorts.counter) := by
  change (CounterForPrograms.nextState remainingPorts
    (Counters.incrementResult candidatePorts a)).stacks candidatePorts.counter = _
  rw [← CounterForPrograms.nextState_outside remainingPorts
    (Counters.incrementResult candidatePorts a) candidatePorts.counter
    (by decide) (by decide)]
  exact Counters.incrementResult_counter _ _

theorem advanceState_remaining (a : State 40 896)
    (hcs : a.stacks candidatePorts.scratch = []) :
    (advanceState a).stacks remainingPorts.counter =
      CounterPrograms.ripple false (a.stacks remainingPorts.counter) := by
  change (CounterForPrograms.nextState remainingPorts
    (Counters.incrementResult candidatePorts a)).stacks remainingPorts.counter = _
  rw [CounterForPrograms.nextState_counter, Counters.incrementResult_stacks candidatePorts a hcs]
  rw [Function.update_of_ne (by decide : remainingPorts.counter ≠ candidatePorts.counter)]

/-- Binary words remain short even at the final overflow to the exact bound.
The exhausted word is never passed to the signature evaluator. -/
theorem advanceState_widths (a : State 40 896) (width : ℕ)
    (hcs : a.stacks candidatePorts.scratch = [])
    (hc : (a.stacks candidatePorts.counter).length ≤ width + 1)
    (hrlen : (a.stacks remainingPorts.counter).length ≤ width + 1)
    (hr : 0 < CounterPrograms.value (a.stacks remainingPorts.counter))
    (htotal : CounterPrograms.value (a.stacks candidatePorts.counter) +
      CounterPrograms.value (a.stacks remainingPorts.counter) = 2 ^ width) :
    ((advanceState a).stacks candidatePorts.counter).length ≤ width + 1 ∧
      ((advanceState a).stacks remainingPorts.counter).length ≤ width + 1 := by
  constructor
  · rw [advanceState_candidate]
    apply CounterPrograms.increment_length_le_of_lt _ _ hc
    have hp : 0 < 2 ^ width := Nat.pow_pos (by decide)
    rw [pow_succ]
    omega
  · rw [advanceState_remaining a hcs, CounterPrograms.decrement_length hr]
    exact hrlen

/-- Every nonterminal cursor is exactly the fixed-width word consumed by the
attained-signature predicate, not merely a short encoding of the same value. -/
theorem advanceState_assignment (a : State 40 896) (h : ℕ) (candidate : Fin (2 ^ h))
    (hc : a.stacks candidatePorts.counter = ExecCNFTupleEnumeration.fixedBits h candidate)
    (hn : candidate.val + 1 < 2 ^ h) :
    (advanceState a).stacks candidatePorts.counter =
      ExecCNFTupleEnumeration.fixedBits h (candidate.val + 1) := by
  rw [advanceState_candidate, hc]
  exact Counters.increment_word candidate hn

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Concrete adapters for the attained-signature tuple controller

The cursor primitives are fixed in `SignatureTupleProgram`. This module
installs the actual head loader and predecessor predicate on the shared leaf
ABI, and relates their physical state to the attained-prefix traversal.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative

open BitProgram StructuredCalls SignatureTupleProgram

/-- Decrement retains the full `h+1`-bit remaining word, including leading
zeros. This matches the suspended-frame encoding after every candidate. -/
theorem remaining_word_after_advance (a : State 40 896) (h candidate : ℕ)
    (hc : candidate < 2 ^ h)
    (hs : a.stacks candidatePorts.scratch = [])
    (hr : a.stacks remainingPorts.counter =
      ExecCNFTupleEnumeration.fixedBits (h + 1) (2 ^ h - candidate)) :
    (advanceState a).stacks remainingPorts.counter =
      ExecCNFTupleEnumeration.fixedBits (h + 1) (2 ^ h - (candidate + 1)) := by
  have hpow : 0 < 2 ^ h := Nat.pow_pos (by decide)
  have hbound : 2 ^ h - candidate < 2 ^ (h + 1) := by
    rw [pow_succ]
    omega
  have hnext : 2 ^ h - (candidate + 1) < 2 ^ (h + 1) := by
    rw [pow_succ]
    omega
  have hv : CounterPrograms.value (a.stacks remainingPorts.counter) = 2 ^ h - candidate := by
    rw [hr]
    exact ExecCNFTupleEnumeration.fixedBits_value _ _ hbound
  have hp : 0 < CounterPrograms.value (a.stacks remainingPorts.counter) := by omega
  rw [advanceState_remaining a hs]
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · rw [CounterPrograms.decrement_length hp, hr]
    simp
  · rw [ExecCNFTupleEnumeration.fixedBits_value _ _ hnext]
    have hd := CounterPrograms.value_decrement hp
    omega

/-- No physical tape outside the two counters and their decrement scratch is
changed by advancement. The increment scratch is restored as well. -/
theorem advanceState_outside (a : State 40 896)
    (hs : a.stacks candidatePorts.scratch = []) (i : Fin 896)
    (hc : i ≠ candidatePorts.counter) (hr : i ≠ remainingPorts.counter)
    (ht : i ≠ remainingPorts.scratch) :
    (advanceState a).stacks i = a.stacks i := by
  change (CounterForPrograms.nextState remainingPorts
    (Counters.incrementResult candidatePorts a)).stacks i = a.stacks i
  rw [← CounterForPrograms.nextState_outside remainingPorts _ i hr ht]
  rw [Counters.incrementResult_stacks candidatePorts a hs, Function.update_of_ne hc]

theorem CursorWords.remaining_value {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) :
    CounterPrograms.value (a.stacks remainingPorts.counter) = 2 ^ h - c := by
  rw [hw.remaining]
  apply ExecCNFTupleEnumeration.fixedBits_value
  have hp : 0 < 2 ^ h := Nat.pow_pos (by decide)
  rw [pow_succ]
  omega

theorem CursorWords.advance {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) (hc : c < 2 ^ h) :
    CursorWords (advanceCandidateState a) h (c + 1) := by
  have hp : 0 < CounterPrograms.value (a.stacks remainingPorts.counter) := by
    rw [hw.remaining_value]
    omega
  have hwidth := advanceState_widths a h hw.incrementScratch hw.width
    (by rw [hw.remaining]; simp) hp (by rw [hw.value, hw.remaining_value]; omega)
  have hcandidate : (advanceCandidateState a).stacks candidatePorts.counter =
      (advanceState a).stacks candidatePorts.counter := by
    exact Function.update_of_ne (by decide : candidatePorts.counter ≠ tupleStacks 3) [] (advanceState a).stacks
  have hremaining : (advanceCandidateState a).stacks remainingPorts.counter =
      (advanceState a).stacks remainingPorts.counter := by
    exact Function.update_of_ne (by decide : remainingPorts.counter ≠ tupleStacks 3) [] (advanceState a).stacks
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcandidate, advanceState_candidate, CounterPrograms.value_increment, hw.value]
  · rw [hcandidate]
    exact hwidth.1
  · intro hn
    rw [hcandidate]
    exact advanceState_assignment a h ⟨c, hc⟩ (hw.exact hc) hn
  · rw [hremaining]
    exact remaining_word_after_advance a h c hc hw.incrementScratch hw.remaining
  · change Function.update (advanceState a).stacks (tupleStacks 3) [] candidatePorts.scratch = []
    rw [Function.update_of_ne (by decide)]
    rw [advanceState_outside a hw.incrementScratch candidatePorts.scratch
      (by decide) (by decide) (by decide), hw.incrementScratch]
  · change Function.update (advanceState a).stacks (tupleStacks 3) [] remainingPorts.scratch = []
    rw [Function.update_of_ne (by decide)]
    exact CounterForPrograms.nextState_scratch remainingPorts _


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual state refinements for the fixed attained-signature controller.
Each lemma follows concrete commands already installed in the native ABI. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open SignatureTupleDFS SignatureTupleTraversal

theorem advanceCandidateState_outside (a : State 40 896)
    (hs : a.stacks candidatePorts.scratch = []) (i : Fin 896)
    (hk : i ≠ tupleStacks 3) (hc : i ≠ candidatePorts.counter)
    (hr : i ≠ remainingPorts.counter) (ht : i ≠ remainingPorts.scratch) :
    (advanceCandidateState a).stacks i = a.stacks i := by
  change Function.update (advanceState a).stacks (tupleStacks 3) [] i = a.stacks i
  rw [Function.update_of_ne hk, advanceState_outside a hs i hc hr ht]

/-- Counter advancement and key disposal also restore the original boundary
cap, including the terminal candidate whose word has one extra bit. -/
theorem advance_endpoint_bound_oai (a : State 40 896) (h candidate F : ℕ)
    (hw : CursorWords a h candidate) (hc : candidate < 2 ^ h)
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hwidth : h + 1 ≤ F) :
    ∀ i, ((advanceCandidateState a).stacks i).length ≤ F := by
  have hn := hw.advance hc
  intro i
  by_cases hk : i = tupleStacks 3
  · subst i
    change (Function.update (advanceState a).stacks (tupleStacks 3) []
      (tupleStacks 3)).length ≤ F
    simp
  · by_cases hcan : i = candidatePorts.counter
    · subst i
      exact hn.width.trans hwidth
    · by_cases hrem : i = remainingPorts.counter
      · subst i
        rw [hn.remaining, ExecCNFTupleEnumeration.fixedBits_length]
        exact hwidth
      · by_cases hs : i = remainingPorts.scratch
        · subst i
          rw [hn.decrementScratch]
          simp
        · rw [advanceCandidateState_outside a hw.incrementScratch i hk hcan hrem hs]
          exact hframe i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.advance_endpoint_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.advance_endpoint_bound_oai
