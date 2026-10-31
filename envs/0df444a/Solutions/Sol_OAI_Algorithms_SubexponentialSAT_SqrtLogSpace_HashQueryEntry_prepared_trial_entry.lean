-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_trial_entry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:08:34.197725+00:00
-- url     : https://prove2.me/submissions/72ef0525-5ef0-43e6-bbf2-a867660dd39b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S172
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashQueryEntry_trial_entry

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage

theorem worker_empty (a : Data) (he : WorkerEmpty a) :
    ∀ i : Fin 896, i.val < 768 → a.stacks i = [] := by
  intro i hi
  have h := he ⟨i.val, hi⟩
  simpa [workerStack] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual normalizer, trial source stage and marked-record parser supply
the literal query sources. These proofs impose no length cap on the suspended
reference tail or mass accumulator, and execute no extra marker stage. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry

open BitProgram StructuredCalls SqrtLog
open HighFrontendSources HashGreedyCode

/-- Preparation supplies the actual low-bank blanks and canonical master
words. The six mutable selector ports are exactly those allowed by the
staged-rounds callback; no global retained-word size premise is needed. -/
theorem prepared_trial_entry_oai {n B : ℕ} (F : DisjointReuse.RawCNF n) (hn : 0 < n)
    (hm : 0 < F.length) (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B) (rounds : ℕ) (word : List Bool)
    (base d a : Data) (e : Fin F.length) (tail : List Bool)
    (hbase : NativeLeafPreparation.Ready n F.length B (initial shifts Q) base)
    (hformula : base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hambient : BinaryArithmetic.toNat (base.stacks 785) = n)
    (hword : word.length = HashCandidates.payloadWidth F.length
      (SparseCode.distanceDenom F.length B))
    (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hhistory : d.stacks 777 = HashGreedyProgram.encodedHistory
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds))
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace
      (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
        (SparseCode.distanceDenom F.length B) word))) a) :
    MarkedEntry (trialQuery F hm shifts Q rounds word e d)
      (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
        (SparseCode.distanceDenom F.length B) word))
      (recordState a tail (Encoding.encodeNat e.val)) := by
  have hlo : ∀ i : Fin 896, i.val < 768 → d.stacks i = [] := by
    intro i hi
    have hne (j : Fin 896) (hj : 768 ≤ j.val) : i ≠ j := by
      intro he
      subst j
      omega
    rw [hframe i (hne 770 (by decide)) (hne 771 (by decide)) (hne 777 (by decide))
      (hne 778 (by decide)) (hne 779 (by decide)) (hne 781 (by decide))]
    exact NativeCodeAssembly.worker_empty base hbase.worker i hi
  refine trial_entry F hn hm shifts Q rounds word d a e tail hword ?_ hhistory ?_ ?_ ?_ ?_ ?_ hready
  · exact (hframe 784 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hformula
  · rw [hframe 783 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hbase.width]
    exact hbase.modulus_length
  · rw [hframe 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hbase.clauses
  · rw [hframe 785 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hambient
  · intro i _ _
    exact hlo (HighMarkedFrontend.stackMap i) i.isLt
  · exact hlo 767 (by decide)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_trial_entry_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_trial_entry_oai
