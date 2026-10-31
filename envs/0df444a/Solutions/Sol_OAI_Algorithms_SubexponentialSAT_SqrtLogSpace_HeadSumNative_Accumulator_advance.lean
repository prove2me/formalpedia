-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.Accumulator.advance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:40:04.577327+00:00
-- url     : https://prove2.me/submissions/c4e2c107-fd6a-440a-95ed-1e837bef3d74

import Mathlib
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumProgram_body_cursor_next

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Counters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Semantic correctness of the concrete head accumulator. Native dictionary
witnesses are retained only for the current partial sum, and their meaning is
proved using the actual finite-ring normalization program. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect

open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open scoped BigOperators


/-- Candidate increment and fuel decrement restore the same compact boundary,
including the final overflow word that is never passed to the evaluator. -/
theorem advance_word_bound {h i P : ℕ} {a b : Data} (hc : Cursor h i a)
    (hp : 0 < CounterPrograms.value (a.stacks 860))
    (hw : b.stacks 859 = a.stacks 859) (hf : b.stacks 860 = a.stacks 860)
    (hs : b.stacks 861 = []) (hb : ∀ j, (b.stacks j).length ≤ P)
    (hh : h + 1 ≤ P) :
    ∀ j, ((CounterForPrograms.nextState fuelPorts
      (Counters.incrementResult cursorPorts b)).stacks j).length ≤ P := by
  have hn := body_cursor_next hc hp hw hf hs
  intro j
  by_cases h859 : j = 859
  · subst j
    exact hn.wordWidth.trans hh
  by_cases h860 : j = 860
  · subst j
    exact hn.fuelWidth.le.trans hh
  by_cases h861 : j = 861
  · subst j
    simp [hn.scratch]
  rw [← CounterForPrograms.nextState_outside fuelPorts
      (Counters.incrementResult cursorPorts b) j h860 h861,
    Counters.incrementResult_stacks cursorPorts b hs]
  simpa [cursorPorts, h859] using hb j


open HeadIdentifierProgram

open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical frames for the native head rescan. Read-and-restore source words
are framed at command endpoints. The pair accumulator has the stronger static
property that no controller, overlay or dense-add instruction writes it. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumFrames

open OAI BitProgram StructuredCalls HeadSumProgram
open HeadEvaluationProgram.StagedGate (copy clear)

/-- The native cursor increment and fuel decrement change only their two
words and shared empty scratch; all semantic metadata survives this boundary. -/
theorem advance_frame (a : Data) (hs : a.stacks 861 = []) (i : Fin 896)
    (h859 : i ≠ 859) (h860 : i ≠ 860) (h861 : i ≠ 861) :
    (CounterForPrograms.nextState fuelPorts
      (Counters.incrementResult cursorPorts a)).stacks i = a.stacks i := by
  rw [← CounterForPrograms.nextState_outside fuelPorts
      (Counters.incrementResult cursorPorts a) i h860 h861,
    Counters.incrementResult_stacks cursorPorts a hs]
  exact Function.update_of_ne h859 _ _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Correctness of the fixed head rescan. The invariant retains the current
normalized dictionary and the actual immutable source words. Its compact
boundary is reused after every candidate; no execution service is assumed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open HeadIdentifierProgram BucketTupleProgram.Concrete
open QueryTupleState (masterPorts QueryMasterFrame )
open scoped BigOperators

noncomputable section

private theorem retained_exclusions (j : Fin 896) (hj : j ∈ retainedPorts) :
    56 ≤ j.val ∧ j ∉ HeadSumAssembly.controllerPorts ∧ j ≠ 853 ∧
      j ≠ 859 ∧ j ≠ 860 ∧ j ≠ 861 := by
  have h : ∀ j ∈ retainedPorts, 56 ≤ j.val ∧ j ∉ HeadSumAssembly.controllerPorts ∧
      j ≠ 853 ∧ j ≠ 859 ∧ j ≠ 860 ∧ j ≠ 861 :=
    List.forall_iff_forall_mem.mp (by
      simp only [retainedPorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  exact h j hj

namespace Accumulator
variable {r Q n d : ℕ} {q : Factor.Spec r Q n d}
  {origin : HeadSumProgram.Data} {contribution : ℕ → Dense (q.p.model.O q.p.t) q.u q.J}
  {P i : ℕ} {a b : HeadSumProgram.Data}

/-- The semantic sum and immutable inputs survive the real increment and
countdown, including the terminal assignment overflow. -/
theorem advance_oai {h rank : ℕ} (hc : Cursor h rank a)
    (hp : 0 < CounterPrograms.value (a.stacks 860))
    (hw : b.stacks 859 = a.stacks 859) (hf : b.stacks 860 = a.stacks 860)
    (hs : b.stacks 861 = []) (hb : Accumulator q origin contribution P i b)
    (hh : h+1 ≤ P) : Accumulator q origin contribution P i
      (CounterForPrograms.nextState fuelPorts (Counters.incrementResult cursorPorts b)) := by
  refine ⟨HeadSumCorrect.advance_word_bound hc hp hw hf hs hb.compact hh, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨_,_,_,h859,h860,h861⟩ := retained_exclusions j hj
    exact (HeadSumFrames.advance_frame b hs j h859 h860 h861).trans (hb.retained j hj)
  · intro j
    have hv := j.isLt
    have hx (k : Fin 896) (hk : 56 ≤ k.val) : j.castAdd 840 ≠ k := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_castAdd] at this
      omega
    rw [HeadSumFrames.advance_frame b hs _ (hx 859 (by decide))
      (hx 860 (by decide)) (hx 861 (by decide))]
    exact hb.low j
  · rw [HeadSumFrames.advance_frame b hs 883 (by decide) (by decide) (by decide)]
    exact hb.scratch0
  · rw [HeadSumFrames.advance_frame b hs 884 (by decide) (by decide) (by decide)]
    exact hb.scratch1
  · obtain ⟨entries,hg,hw,hv⟩ := hb.partialSum
    exact ⟨entries,hg,(HeadSumFrames.advance_frame b hs 853 (by decide) (by decide) (by decide)).trans hw,hv⟩

end Accumulator

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.Accumulator.advance_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.Accumulator.advance_oai
