-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.attempt_entry_of_query
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:10:08.150121+00:00
-- url     : https://prove2.me/submissions/cb8b8716-17eb-4ac8-a597-ab228c907222

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S114
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyProgram_PadScore_leaf_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-- The parser reverses the current odometer word, exactly as the reference
candidate accessor does. No native decoding of the exponential rank occurs. -/
theorem payload_wordRank {m depth : ℕ} (word : List Bool)
    (hlen : word.length = HashCandidates.payloadWidth m depth) :
    HashCandidates.payload m depth (wordRank word hlen) = word.reverse := by
  apply congrArg List.reverse
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · simp [hlen]
  · exact ExecCNFTupleEnumeration.fixedBits_value _ _ (wordRank word hlen).isLt

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual fixed binary comparison/update used by the streaming selector.
Its queue port is a bounded iterator frame, not a list of candidate records. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators


namespace PadScore

open ModularPrograms ModularArithmetic

theorem exact_value (score shape : List Bool) (hlen : score.length ≤ shape.length) :
    BinaryArithmetic.toNat (padTo shape score) = BinaryArithmetic.toNat score ∧
      (padTo shape score).length = shape.length :=
  ⟨padTo_correct shape score hlen, padTo_length shape score⟩

end PadScore

namespace NativeRound

/-- Physical padding connects an actual complete query trace to the selector
score ABI. This lemma assumes executions, never an unimplemented query oracle. -/
theorem attempt_eval_of_query (mass : Cmd 40 896) (a b c : State 40 896)
    (np nq : ℕ) (payload score : List Bool)
    (hp : Eval HashCandidateProgram.Leaf.prepare np a b)
    (hprep : b.stacks = Function.update a.stacks 768 payload)
    (hq : Eval mass nq b c)
    (hquery : c.stacks = Function.update b.stacks 769 score)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (hlen : score.length ≤ (a.stacks 818).length) :
    ∃ d, Eval (attempt mass) (np + (nq + (23 * (a.stacks 818).length + 20))) a d ∧
      d.stacks = Function.update (Function.update a.stacks 768 payload) 769
        (ModularArithmetic.padTo (a.stacks 818) score) ∧
      BinaryArithmetic.toNat (d.stacks 769) = BinaryArithmetic.toNat score ∧
      (d.stacks 769).length = (a.stacks 818).length := by
  obtain ⟨d, he, hd⟩ := PadScore.leaf_eval c
    (by simp [hquery, hprep, h0]) (by simp [hquery, hprep, h1])
    (by simp [hquery, hprep, h2]) (by simpa [hquery, hprep] using hlen)
  have hf : d.stacks = Function.update (Function.update a.stacks 768 payload) 769
      (ModularArithmetic.padTo (a.stacks 818) score) := by
    simpa [hquery, hprep] using hd
  refine ⟨d, ?_, hf, ?_, ?_⟩
  · simpa only [attempt, hquery, hprep, Function.update_of_ne (by decide : (818 : Fin 896) ≠ 769),
      Function.update_of_ne (by decide : (818 : Fin 896) ≠ 768)] using hp.seq (hq.seq he)
  · simpa [hf] using (PadScore.exact_value score (a.stacks 818) hlen).1
  · simp [hf, ModularArithmetic.padTo_length]

end NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCandidate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact reference values for the payload and full natural score physically
produced by the native candidate attempt. These accessors are proof objects;
the executable program retains only the current word and running minimum. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

theorem candidate_at_word {m depth : ℕ} (word : List Bool)
    (hlen : word.length = HashCandidates.payloadWidth m depth) :
    candidate m depth (CounterPrograms.value word) = HashCandidates.normalize m depth word.reverse := by
  have h := HashCandidateRank.payload_wordRank word hlen
  simpa only [HashCandidates.payload, HashCandidateRank.wordRank, candidate] using
    congrArg (HashCandidates.normalize m depth) h

theorem padded_score_eq (word shape : List Bool) (score : ℕ)
    (hlen : word.length ≤ shape.length) (hvalue : BinaryArithmetic.toNat word = score) :
    ModularArithmetic.padTo shape word = ExecCNFTupleEnumeration.fixedBits shape.length score := by
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · simp [ModularArithmetic.padTo_length]
  · have hv := (PadScore.exact_value word shape hlen).1
    have hscore : score < 2 ^ shape.length := by
      rw [← hvalue]
      exact (ModularArithmetic.toNat_lt_pow_length word).trans_le
        (Nat.pow_le_pow_right (by decide) hlen)
    rw [CounterPrograms.value_eq_toNat, hv, hvalue,
      ExecCNFTupleEnumeration.fixedBits_value _ _ hscore]

/-- Actual candidate preparation, exact query and paid padding produce exactly
the reference entry used in the proven native minimum. The query premise is an
actual execution and exact full frame; the complete mass adapter must supply it. -/
theorem attempt_entry_of_query_oai {X : Type*} [Fintype X]
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m depth : ℕ) (rows : List (List Bool)) (mass : Cmd 40 896)
    (a b c : State 40 896) (np nq : ℕ) (word score : List Bool)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hp : Eval HashCandidateProgram.Leaf.prepare np a b)
    (hprep : b.stacks = Function.update a.stacks 768
      (HashCandidates.normalize m depth word.reverse))
    (hq : Eval mass nq b c) (hquery : c.stacks = Function.update b.stacks 769 score)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (hshape : (a.stacks 818).length = HashSelect.loopCap n m)
    (hlen : score.length ≤ HashSelect.loopCap n m)
    (hvalue : BinaryArithmetic.toNat score = HashSelect.mass rowAccept weight
      (HashCandidates.normalize m depth word.reverse :: rows)) :
    ∃ d, Eval (attempt mass) (np + (nq + (23 * HashSelect.loopCap n m + 20))) a d ∧
      d.stacks = Function.update (Function.update a.stacks 768
        (entry rowAccept weight n m depth rows (CounterPrograms.value word)).payload) 769
        (entry rowAccept weight n m depth rows (CounterPrograms.value word)).score := by
  obtain ⟨d, he, hd, _, _⟩ := attempt_eval_of_query mass a b c np nq _ score hp hprep hq hquery
    h0 h1 h2 (by simpa [hshape] using hlen)
  refine ⟨d, by simpa only [hshape] using he, ?_⟩
  rw [hd, padded_score_eq score (a.stacks 818) _ (by simpa [hshape] using hlen) hvalue]
  simp only [entry, candidate_at_word word hword, hshape]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.attempt_entry_of_query_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.attempt_entry_of_query_oai.{u_1}
