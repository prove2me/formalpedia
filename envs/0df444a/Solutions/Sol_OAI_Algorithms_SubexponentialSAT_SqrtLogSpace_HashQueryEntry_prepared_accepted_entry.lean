-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_accepted_entry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:07:19.748371+00:00
-- url     : https://prove2.me/submissions/f307f1b9-f4da-4645-bc2a-0e88bfa25f41

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S172
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashQueryEntry_accepted_entry

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

/-- The actual completed greedy `RowBoundary` restores preparation's master
words and all lower blank workspace before the history-only count stage. -/
theorem prepared_accepted_entry_oai {n B : ℕ} (F : DisjointReuse.RawCNF n) (hn : 0 < n)
    (hm : 0 < F.length) (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B) (rounds : ℕ) (base d : Data)
    (hbase : NativeLeafPreparation.Ready n F.length B (initial shifts Q) base)
    (hformula : base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hambient : BinaryArithmetic.toNat (base.stacks 785) = n)
    (hboundary : HashGreedyRound.RowBoundary base
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) d) :
    AcceptedEntry (acceptedQuery F hm shifts Q rounds d) (AcceptedQueryStage.staged d) := by
  refine accepted_entry F hn hm shifts Q rounds d ?_ hboundary.history ?_ ?_ ?_ ?_
  · exact (hboundary.frame 784 (by decide) (by decide)).trans hformula
  · rw [hboundary.frame 783 (by decide) (by decide), hbase.width]
    exact hbase.modulus_length
  · rw [hboundary.frame 782 (by decide) (by decide)]
    exact hbase.clauses
  · rw [hboundary.frame 785 (by decide) (by decide)]
    exact hambient
  · intro i _ _
    change d.stacks (HighMarkedFrontend.stackMap i) = []
    have hne (j : Fin 896) (hj : 768 ≤ j.val) : HighMarkedFrontend.stackMap i ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = j.val at hv
      omega
    rw [hboundary.frame _ (hne 777 (by decide)) (hne 781 (by decide))]
    exact NativeCodeAssembly.worker_empty base hbase.worker _ i.isLt

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_accepted_entry_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_accepted_entry_oai
