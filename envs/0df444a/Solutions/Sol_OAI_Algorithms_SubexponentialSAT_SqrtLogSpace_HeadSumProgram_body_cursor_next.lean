-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_cursor_next
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:27:23.567997+00:00
-- url     : https://prove2.me/submissions/6a6011b1-b7d3-4f93-aff0-58d715887eec

import Mathlib
import Definitions.Def_OAIQ081S165

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The head rescan retains one raw Boolean assignment and a binary countdown.
The full-key/correction gate is executed for every candidate. Accepted values
are accumulated before the cursor advances, including the empty-head case. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

theorem Cursor.word {h i : ℕ} {d : Data} (hc : Cursor h i d)
    (hp : 0 < value (d.stacks 860)) :
    d.stacks 859 = (Counters.wordEquiv h ⟨i, hc.index_lt hp⟩).val := by
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · exact (hc.activeWidth (hc.index_lt hp)).trans (Counters.wordEquiv h _).property.symm
  · change value (d.stacks 859) = value (ExecCNFTupleEnumeration.fixedBits h i)
    rw [ExecCNFTupleEnumeration.fixedBits_value h i (hc.index_lt hp)]
    exact hc.rank

theorem Cursor.advance {h i : ℕ} {d e : Data} (hc : Cursor h i d)
    (hp : 0 < value (d.stacks 860))
    (hw : e.stacks 859 = ripple true (d.stacks 859))
    (hf : e.stacks 860 = d.stacks 860) :
    Cursor h (i + 1) (CounterForPrograms.nextState fuelPorts e) := by
  have hi := hc.index_lt hp
  have hn : (CounterForPrograms.nextState fuelPorts e).stacks 860 =
      ripple false (e.stacks 860) := CounterForPrograms.nextState_counter fuelPorts e
  have hnext := CounterForPrograms.nextState_outside fuelPorts e 859 (by decide) (by decide)
  have hword : (CounterForPrograms.nextState fuelPorts e).stacks 859 =
      ripple true (d.stacks 859) := hnext.symm.trans hw
  have hlen : (d.stacks 859).length = h := hc.activeWidth hi
  have hpow : 2 ^ h < 2 ^ (h + 1) := by
    have := Nat.two_pow_pos h
    simp only [pow_succ]
    omega
  constructor
  · rw [hword, value_increment, hc.rank]
  · rw [hn, hf]
    have hv := value_decrement hp
    have := hc.fuel
    omega
  · rw [hn, hf, decrement_length hp]
    exact hc.fuelWidth
  · rw [hword]
    apply increment_length_le_of_lt
    · omega
    · rw [hc.rank]
      omega
  · intro hactive
    rw [hword, hc.word hp, Counters.increment_word _ hactive]
    exact (Counters.wordEquiv h _).property
  · exact CounterForPrograms.nextState_scratch fuelPorts e


open HeadEvaluationProgram.StagedGate (copy copyState clear clearState )


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram


open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

/-- The counter interface sees the exact next index even after the last word
has overflowed; the overflow word is excluded from further callbacks. -/
theorem body_cursor_next_oai {h i : ℕ} {a b : Data} (hc : Cursor h i a)
    (hp : 0 < value (a.stacks 860))
    (hw : b.stacks 859 = a.stacks 859) (hf : b.stacks 860 = a.stacks 860)
    (hs : b.stacks 861 = []) :
    Cursor h (i + 1) (CounterForPrograms.nextState fuelPorts
      (Counters.incrementResult cursorPorts b)) := by
  apply hc.advance hp
  · rw [show (Counters.incrementResult cursorPorts b).stacks 859 =
        ripple true (b.stacks 859) from Counters.incrementResult_counter cursorPorts b, hw]
  · rw [Counters.incrementResult_stacks cursorPorts b hs]
    simpa [cursorPorts] using hf


open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_cursor_next_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_cursor_next_oai
