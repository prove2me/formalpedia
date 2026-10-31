-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:12:00.649893+00:00
-- url     : https://prove2.me/submissions/3c4d028f-5da5-42e6-a27a-074fe9da49ac

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S114
import Definitions.Def_OAIQ081S115
import Definitions.Def_OAIQ081S127
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_initialize_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete tape operations and traversal assertions for the outer CRT.
All operations in this module are fixed finite programs. Arithmetic is supplied
by the separately defined concrete CRT service commands. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem copy_run (d : Data) (src dst : Fin 320)
    (hsd : src ≠ dst) (hs : src ≠ 318) (hd : (318 : Fin 320) ≠ dst)
    (ht : d.stacks 318 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d
      (afterCopy d src dst 0 1) :=
  SubexpScanPrimitives.copy_eval d src dst 318 0 1 hsd hs hd (by decide) ht

theorem clearMany_run (d : Data) (ports : List (Fin 320)) :
    Eval (clearMany ports) (SubexpSetupStorage.clearManyCost ports d) d
      (SubexpSetupStorage.clearManyState ports d) := by
  have he : clearMany ports = SubexpSetupStorage.clearMany ports := by
    induction ports with
    | nil => rfl
    | cons p ps ih =>
      change Cmd.seq (clear p) (clearMany ps) =
        Cmd.seq (SubexpSetupStorage.clearCmd p) (SubexpSetupStorage.clearMany ps)
      rw [ih]
      rfl
  rw [he]
  exact SubexpSetupStorage.clearMany_eval ports d

theorem takeNode_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) (bits rest : List Bool)
    (hs : w.remaining = bits ++ rest) (hc : w.current = [])
    (ht : frame 278 = []) (hu : frame 279 = [])
    (hw : (frame 104).length = bits.length) :
    Eval takeNode (14 * bits.length + 11) (sweepState regs frame w)
      (sweepState (readRegs regs 0 1 none) frame
        {w with remaining := rest, current := bits}) := by
  have h := takeWord_eval (sweepState regs frame w) 104 278 279 257 259 0 1
    (by decide) (by decide) bits rest (by simpa [sweepState] using hs)
    (by simpa [sweepState] using ht) (by simpa [sweepState] using hu)
    (by simpa [sweepState] using hw)
  simpa only [takeNode, afterTake, sweepState, sweepStore_current, hc,
    List.append_nil, update_sweepStore_remaining, update_sweepStore_current] using h

theorem takeJet_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) (bits rest : List Bool)
    (hs : w.jets = bits ++ rest) (hc : w.jet = [])
    (ht : frame 278 = []) (hu : frame 279 = [])
    (hw : (frame 277).length = bits.length) :
    Eval takeJet (14 * bits.length + 11) (sweepState regs frame w)
      (sweepState (readRegs regs 0 1 none) frame
        {w with jets := rest, jet := bits}) := by
  have h := takeWord_eval (sweepState regs frame w) 277 278 279 266 225 0 1
    (by decide) (by decide) bits rest (by simpa [sweepState] using hs)
    (by simpa [sweepState] using ht) (by simpa [sweepState] using hu)
    (by simpa [sweepState] using hw)
  simpa only [takeJet, afterTake, sweepState, sweepStore_jet, hc,
    List.append_nil, update_sweepStore_jets, update_sweepStore_jet] using h

theorem copyCurrent_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) (ht : frame 318 = []) (he : w.nodeCopy = []) :
    Eval (copy 259 213) (7 * w.current.length + 5) (sweepState regs frame w)
      (sweepState (readRegs regs 0 1 none) frame {w with nodeCopy := w.current}) := by
  have h := copy_run (sweepState regs frame w) 259 213
    (by decide) (by decide) (by decide) (by simpa [sweepState] using ht)
  simpa only [afterCopy, sweepState, sweepStore_current, StackRoutines.copyStacks,
    sweepStore_nodeCopy, he, List.append_nil, update_sweepStore_nodeCopy] using h

theorem copyIndex_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) (ht : frame 318 = []) (he : w.indexCopy = []) :
    Eval (copy 260 216) (7 * w.index.length + 5) (sweepState regs frame w)
      (sweepState (readRegs regs 0 1 none) frame {w with indexCopy := w.index}) := by
  have h := copy_run (sweepState regs frame w) 260 216
    (by decide) (by decide) (by decide) (by simpa [sweepState] using ht)
  simpa only [afterCopy, sweepState, sweepStore_index, StackRoutines.copyStacks,
    sweepStore_indexCopy, he, List.append_nil, update_sweepStore_indexCopy] using h

/-- Exact physical loading of one node, its index, and its matching padded jet. -/
theorem loadCurrent_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) (node nodes jet jets : List Bool)
    (hn : w.remaining = node ++ nodes) (hj : w.jets = jet ++ jets)
    (hc : w.current = []) (hcopy : w.nodeCopy = [])
    (hi : w.indexCopy = []) (hjet : w.jet = [])
    (ht : frame 278 = []) (hu : frame 279 = []) (hv : frame 318 = [])
    (hw : (frame 104).length = node.length) (hjw : (frame 277).length = jet.length) :
    Eval loadCurrent (21 * node.length + 7 * w.index.length + 14 * jet.length + 32)
      (sweepState regs frame w)
      (sweepState (readRegs regs 0 1 none) frame (loadedWords w node nodes jet jets)) := by
  have h1 := takeNode_run regs frame w node nodes hn hc ht hu hw
  have h2 := copyCurrent_run (readRegs regs 0 1 none) frame
    {w with remaining := nodes, current := node} hv hcopy
  have h3 := copyIndex_run (readRegs regs 0 1 none) frame
    {w with remaining := nodes, current := node, nodeCopy := node} hv hi
  have h4 := takeJet_run (readRegs regs 0 1 none) frame
    {w with remaining := nodes, current := node, nodeCopy := node, indexCopy := w.index}
    jet jets hj hjet ht hu hjw
  simp only [StackRoutines.readRegs_reset] at h2 h3 h4
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1 <;> try rfl
  omega

theorem clearCurrent_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) :
    Eval (clearMany [213,216,225,259])
      (2 * w.nodeCopy.length + 2 * w.indexCopy.length + 2 * w.jet.length +
        2 * w.current.length + 12)
      (sweepState regs frame w)
      (sweepState (readRegs regs 0 1 none) frame (cleanedWords w)) := by
  have h := clearMany_run (sweepState regs frame w) [213,216,225,259]
  simp [SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearManyState,
    SubexpSetupStorage.clearState, sweepState, StackRoutines.readRegs_reset,
    Nat.add_assoc] at h
  convert h using 1 <;> try rfl
  omega

theorem incrementIndex_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) :
    Eval incrementIndex 2 (sweepState regs frame w)
      (sweepState (Function.update regs 0 false) frame {w with index := false :: w.index}) := by
  have h1 := StructuredProgram.Eval.atom (.set (0 : Fin 16) false) (sweepState regs frame w)
  have h2 := StructuredProgram.Eval.atom (.push (260 : Fin 320) (0 : Fin 16))
    ((StructuredProgram.Atom.set 0 false).eval (sweepState regs frame w))
  have h := Eval.base (h1.seq h2)
  simpa [incrementIndex, sweepState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h

theorem advance_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) (ht : frame 318 = []) :
    Eval advance
      (9 * w.current.length + 2 * w.nodeCopy.length + 2 * w.indexCopy.length +
        2 * w.jet.length + 19)
      (sweepState regs frame w)
      (sweepState (Function.update (readRegs regs 0 1 none) 0 false) frame
        (advancedWords w)) := by
  have h1 := copy_run (sweepState regs frame w) 259 258
    (by decide) (by decide) (by decide) (by simpa [sweepState] using ht)
  have e1 : afterCopy (sweepState regs frame w) 259 258 0 1 =
      sweepState (readRegs regs 0 1 none) frame
        {w with processed := w.current ++ w.processed} := by
    simp only [afterCopy, sweepState, StackRoutines.copyStacks,
      sweepStore_current, sweepStore_processed, update_sweepStore_processed]
  rw [e1] at h1
  have h2 := clearCurrent_run (readRegs regs 0 1 none) frame
    {w with processed := w.current ++ w.processed}
  simp only [StackRoutines.readRegs_reset] at h2
  have h3 := incrementIndex_run (readRegs regs 0 1 none) frame
    (cleanedWords {w with processed := w.current ++ w.processed})
  have h := h1.seq (h2.seq h3)
  convert h using 1 <;> try rfl
  simp only [sweepState, sweepStore_current]
  omega

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterSweep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordered execution of the concrete outer CRT tape loop. The only remaining
premise is an actual execution of its arithmetic middle command on the exact
loaded state; all loading, index updates, traversal guards, and transport costs
are discharged here. This premise is instantiated by the concrete CRT services.
-/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem advanced_loadedReady {I A : Type*} (encode : I → List Bool) (jet : I → List Bool)
    (encodeAcc : A → List Bool) (processed remaining : List I) (item : I) (acc : A) :
    advancedWords (loadedReady encode jet encodeAcc processed remaining item acc) =
      readyWords encode jet encodeAcc (item :: processed) remaining acc := by
  simp [advancedWords, cleanedWords, loadedReady, loadedWords, readyWords,
    List.replicate_succ]

theorem testNodes_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) :
    Eval testNodes 1 (sweepState regs frame w)
      (sweepState (readRegs regs 0 15 w.remaining.head?) frame w) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.peek 257 0 15)
    (sweepState regs frame w))
  simpa only [testNodes, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    sweepState, sweepStore_remaining] using h

theorem sweepIteration_run {I A R : Type*} [AddMonoid R]
    (encode : I → List Bool) (jet : I → List Bool) (encodeAcc : A → List Bool)
    (value : A → R) (term : I → R) (frame : Fin 320 → List Bool)
    (middle : Code) (nodeWidth jetWidth K : ℕ)
    (hwidth : ∀ i, (encode i).length = nodeWidth)
    (hjetWidth : ∀ i, (jet i).length = jetWidth)
    (ht : frame 278 = []) (hu : frame 279 = []) (hv : frame 318 = [])
    (hw : (frame 104).length = nodeWidth) (hjw : (frame 277).length = jetWidth)
    (processed remaining : List I) (item : I) (acc : A) (regs : Fin 16 → Bool)
    (hmid : ∀ rr, ∃ n ≤ K, ∃ rf b,
      Eval middle n
        (sweepState rr frame (loadedReady encode jet encodeAcc processed remaining item acc))
        (sweepState rf frame (loadedReady encode jet encodeAcc processed remaining item b)) ∧
      value b = value acc + term item) :
    ∃ n ≤ K + transportCost nodeWidth jetWidth processed.length, ∃ rf b,
      Eval (sweepIteration middle) n
        (sweepState regs frame (readyWords encode jet encodeAcc processed (item :: remaining) acc))
        (sweepState rf frame (readyWords encode jet encodeAcc (item :: processed) remaining b)) ∧
      value b = value acc + term item := by
  have hload := loadCurrent_run regs frame
    (readyWords encode jet encodeAcc processed (item :: remaining) acc)
    (encode item) (remaining.flatMap encode) (jet item) (remaining.flatMap jet)
    (by simp [readyWords]) (by simp [readyWords]) rfl rfl rfl rfl ht hu hv
    (hw.trans (hwidth item).symm) (hjw.trans (hjetWidth item).symm)
  obtain ⟨n, hn, rf, b, hmiddle, hvalue⟩ := hmid (readRegs regs 0 1 none)
  have hadvance := advance_run rf frame
    (loadedReady encode jet encodeAcc processed remaining item b) hv
  rw [advanced_loadedReady] at hadvance
  have h := hload.seq (hmiddle.seq hadvance)
  refine ⟨_, ?_, _, b, h, hvalue⟩
  simp only [readyWords, loadedReady, loadedWords, List.length_replicate,
    hwidth, hjetWidth, transportCost] at *
  omega

/-- The loop invariant records physical processed order, remaining order,
matching jet order, and the unary index. The arithmetic premise is an actual
finite-program trace, not a supplied answer or cost annotation. -/
theorem sweepLoop_run {I A R : Type*} [AddMonoid R]
    (encode : I → List Bool) (jet : I → List Bool) (encodeAcc : A → List Bool)
    (value : A → R) (term : I → R) (frame : Fin 320 → List Bool)
    (middle : Code) (nodeWidth jetWidth K : ℕ) (full : List I)
    (hwidth : ∀ i, (encode i).length = nodeWidth)
    (hjetWidth : ∀ i, (jet i).length = jetWidth) (hpos : 0 < nodeWidth)
    (ht : frame 278 = []) (hu : frame 279 = []) (hv : frame 318 = [])
    (hw : (frame 104).length = nodeWidth) (hjw : (frame 277).length = jetWidth)
    (hmid : ∀ processed remaining item acc, full = processed.reverse ++ item :: remaining →
      ∀ rr, ∃ n ≤ K, ∃ rf b,
        Eval middle n
          (sweepState rr frame (loadedReady encode jet encodeAcc processed remaining item acc))
          (sweepState rf frame (loadedReady encode jet encodeAcc processed remaining item b)) ∧
        value b = value acc + term item)
    (processed remaining : List I) (acc : A) (regs : Fin 16 → Bool)
    (hfull : full = processed.reverse ++ remaining) :
    ∃ n ≤ remaining.length * (K + transportCost nodeWidth jetWidth full.length + 2) + 1,
      ∃ rf b,
        Eval (sweepLoop middle) n
          (sweepState (readRegs regs 0 15 (remaining.flatMap encode).head?) frame
            (readyWords encode jet encodeAcc processed remaining acc))
          (sweepState rf frame
            (readyWords encode jet encodeAcc (remaining.reverse ++ processed) [] b)) ∧
        value b = value acc + (remaining.map term).sum := by
  induction remaining generalizing processed acc regs with
  | nil =>
      refine ⟨1, by simp, readRegs regs 0 15 none, acc, ?_, by simp⟩
      exact Eval.while_false (by simp [sweepState, readRegs])
  | cons item rest ih =>
      let r0 := readRegs regs 0 15 ((item :: rest).flatMap encode).head?
      obtain ⟨n, hn, r1, a1, hstep, hvalue⟩ :=
        sweepIteration_run encode jet encodeAcc value term frame middle nodeWidth jetWidth K
          hwidth hjetWidth ht hu hv hw hjw processed rest item acc r0
          (hmid processed rest item acc hfull)
      have hp := testNodes_run r1 frame
        (readyWords encode jet encodeAcc (item :: processed) rest a1)
      have hfull' : full = (item :: processed).reverse ++ rest := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hfull
      obtain ⟨m, hm, rf, b, hrest, hvrest⟩ := ih (item :: processed) a1 r1 hfull'
      have hg : (sweepState r0 frame
          (readyWords encode jet encodeAcc processed (item :: rest) acc)).regs 15 = true := by
        have hne : encode item ≠ [] := by
          intro hz
          have := hwidth item
          simp only [hz, List.length_nil] at this
          omega
        cases he : encode item with
        | nil => exact False.elim (hne he)
        | cons bit bits => simp [r0, sweepState, readRegs, he]
      have hrun := Eval.while_true hg (hstep.seq hp) hrest
      have hlen : processed.length ≤ full.length := by
        have h := congrArg List.length hfull
        simp only [List.length_append, List.length_reverse, List.length_cons] at h
        omega
      have hcost : transportCost nodeWidth jetWidth processed.length ≤
          transportCost nodeWidth jetWidth full.length := by
        unfold transportCost
        omega
      refine ⟨n + 1 + m + 1, ?_, rf, b, ?_, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · simpa only [sweepLoop, readyWords, List.reverse_cons, List.append_assoc,
          List.singleton_append] using hrun
      · rw [hvrest, hvalue]
        simp only [List.map_cons, List.sum_cons, add_assoc]

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Final cleanup and complete tape-loop costs for scalar reconstruction.
The arithmetic-middle premise below is an actual execution of a fixed command;
its concrete implementation is assembled separately from the CRT services. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open scoped BigOperators

theorem sweepStore_of_agree (f : Fin 320 → List Bool) (w : SweepWords)
    (h213 : f 213 = w.nodeCopy) (h216 : f 216 = w.indexCopy) (h225 : f 225 = w.jet)
    (h257 : f 257 = w.remaining) (h258 : f 258 = w.processed) (h259 : f 259 = w.current)
    (h260 : f 260 = w.index) (h261 : f 261 = w.accumulator) (h266 : f 266 = w.jets) :
    sweepStore f w = f := by
  funext j
  unfold sweepStore
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9
  · subst j; exact h213.symm
  · subst j; exact h216.symm
  · subst j; exact h225.symm
  · subst j; exact h257.symm
  · subst j; exact h258.symm
  · subst j; exact h259.symm
  · subst j; exact h260.symm
  · subst j; exact h261.symm
  · subst j; exact h266.symm
  · rfl

theorem flatMap_length_of_width {I : Type*} (encode : I → List Bool) (W : ℕ)
    (hw : ∀ x, (encode x).length = W) (xs : List I) :
    (xs.flatMap encode).length = xs.length * W := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, hw, Nat.add_mul, Nat.add_comm]

theorem cleanup_ready_cost {I A : Type*}
    (encode : I → List Bool) (jet : I → List Bool) (encodeAcc : A → List Bool)
    (W J D : ℕ) (full : List I) (a : A) (regs : Fin 16 → Bool)
    (frame : Fin 320 → List Bool) (hw : ∀ x, (encode x).length = W)
    (h104 : (frame 104).length = W)
    (h214 : (frame 214).length = full.length * W)
    (h268 : (frame 268).length ≤ D) (h277 : (frame 277).length = J) :
    SubexpSetupStorage.clearManyCost [104,214,257,258,260,266,268,277]
      (sweepState regs frame (readyWords encode jet encodeAcc full.reverse [] a)) ≤
      cleanupBudget W J full.length D := by
  have hlen := flatMap_length_of_width encode W hw full.reverse
  simp only [List.length_reverse] at hlen
  have hsum := flatMap_length_of_width encode W hw full
  simp only [List.length_flatMap] at hsum
  simp [SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState, sweepState,
    sweepStore, readyWords, h104, h214, h277, cleanupBudget]
  nlinarith [hsum]

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-table outer Hermite traversal for arbitrary coefficient width.
Only the arithmetic middle is parameterized; this module charges all input
copying, node/jet transport, indexing, iteration and final cleanup. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

/-- Join physical initialization, ordered traversal and final cleanup. The
sole remaining service premise is the arithmetic middle's actual execution
on each exact loaded state, for the binary exponent produced by initialization. -/
theorem controller_run_framed_oai {I A R : Type*} [AddMonoid R]
    (encode : I → List Bool) (jet : I → List Bool) (encodeAcc : A → List Bool)
    (value : A → R) (term : I → R) (middle : Code)
    (d : Data) (D K : ℕ) (full : List I) (zero : A)
    (hd : d.stacks 243 = List.replicate D true)
    (hclean : ∀ j ∈ initialCleanPorts, d.stacks j = [])
    (hwidth : ∀ i, (encode i).length = (d.stacks 280).length)
    (hjet : ∀ i, (jet i).length = D * ((d.stacks 280).length))
    (hpos : 0 < (d.stacks 280).length)
    (hnodes : d.stacks 256 = full.flatMap encode)
    (hjets : d.stacks 265 = full.flatMap jet)
    (hz : encodeAcc zero = d.stacks 280)
    (hvz : value zero = 0)
    (hmid : ∀ exponent, BinaryArithmetic.toNat exponent = D → exponent.length ≤ D →
      ∀ processed remaining item acc, full = processed.reverse ++ item :: remaining →
      ∀ rr, ∃ n ≤ K, ∃ rf b,
        Eval middle n
          (sweepState rr (initializedStacks d D exponent)
            (loadedReady encode jet encodeAcc processed remaining item acc))
          (sweepState rf (initializedStacks d D exponent)
            (loadedReady encode jet encodeAcc processed remaining item b)) ∧
        value b = value acc + term item) :
    ∃ n ≤ controllerBudget (d.stacks 280).length D full.length K,
      ∃ (out : Data) (b : A), Eval (controller middle) n d out ∧
        out.stacks = Function.update d.stacks 261 (encodeAcc b) ∧ value b = (full.map term).sum := by
  have hc (j : Fin 320) (hj : j ∈ ([104,261,268,277,278,279,316,317,318,214,257,266] :
      List (Fin 320))) : d.stacks j = [] :=
    hclean j (List.mem_append_left _ hj)
  obtain ⟨ni, hni, ri, exponent, hi, he, hl⟩ := initialize_run d D hd hc
  let f := initializedStacks d D exponent
  have hready : (⟨ri, f⟩ : Data) =
      sweepState ri f (readyWords encode jet encodeAcc [] full zero) := by
    refine SubexpScanPrimitives.state_ext rfl ?_
    refine (sweepStore_of_agree f _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).symm
    all_goals simp [f, initializedStacks, readyWords, hnodes, hjets, hz,
      hclean 213 (by decide), hclean 216 (by decide), hclean 225 (by decide),
      hclean 258 (by decide), hclean 259 (by decide), hclean 260 (by decide)]
  have hw : (f 104).length = (d.stacks 280).length := by simp [f, initializedStacks]
  have hjw : (f 277).length = D * ((d.stacks 280).length) := by
    simp [f, initializedStacks]
  have hnw : (f 214).length = full.length * ((d.stacks 280).length) := by
    simpa [f, initializedStacks, hnodes] using flatMap_length_of_width encode _ hwidth full
  have htest := testNodes_run ri f (readyWords encode jet encodeAcc [] full zero)
  obtain ⟨nl, hnl, rf, b, hloop, hvalue⟩ := sweepLoop_run encode jet encodeAcc value term f
    middle (d.stacks 280).length (D * (d.stacks 280).length) K full hwidth hjet hpos
    (by simpa [f, initializedStacks] using hc 278 (by simp))
    (by simpa [f, initializedStacks] using hc 279 (by simp))
    (by simpa [f, initializedStacks] using hc 318 (by simp))
    hw hjw (hmid exponent he hl) [] full zero ri (by simp)
  simp only [List.append_nil] at hloop
  let last := sweepState rf f (readyWords encode jet encodeAcc full.reverse [] b)
  let out := SubexpSetupStorage.clearManyState [104,214,257,258,260,266,268,277] last
  have hclear := clearMany_run last [104,214,257,258,260,266,268,277]
  have hcost := cleanup_ready_cost encode jet encodeAcc (d.stacks 280).length
    (D * (d.stacks 280).length) D full b rf f hwidth hw hnw
    (by simpa [f, initializedStacks] using hl) hjw
  change SubexpSetupStorage.clearManyCost [104,214,257,258,260,266,268,277] last ≤
    cleanupBudget (d.stacks 280).length (D * (d.stacks 280).length) full.length D at hcost
  have hrun := htest.seq (hloop.seq hclear)
  rw [← hready] at hrun
  have hnlen := flatMap_length_of_width encode _ hwidth full
  have hjlen := flatMap_length_of_width jet _ hjet full
  rw [hnodes, hjets, hnlen, hjlen] at hni
  refine ⟨_, ?_, out, b, hi.seq hrun, ?_, ?_⟩
  · unfold controllerBudget
    omega
  · funext j
    simp only [out, SubexpSetupStorage.clearMany_stacks]
    by_cases hj : j ∈ ([104,214,257,258,260,266,268,277] : List (Fin 320))
    · rw [ite_eq_left hj]
      have hj261 : j ≠ (261 : Fin 320) := by
        intro he; subst j; simp at hj
      rw [Function.update_of_ne hj261]
      exact (hclean j (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide)).symm
    · rw [ite_eq_right hj]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      have hj104 := hj.1
      have hj214 := hj.2.1
      have hj257 := hj.2.2.1
      have hj258 := hj.2.2.2.1
      have hj260 := hj.2.2.2.2.1
      have hj266 := hj.2.2.2.2.2.1
      have hj268 := hj.2.2.2.2.2.2.1
      have hj277 := hj.2.2.2.2.2.2.2
      by_cases h213 : j = 213 <;> by_cases h216 : j = 216 <;>
        by_cases h225 : j = 225 <;> by_cases h259 : j = 259 <;> by_cases h261 : j = 261 <;>
        simp [last, sweepState, sweepStore, readyWords, f, initializedStacks, hj104, hj214, hj257, hj258, hj260, hj266, hj268, hj277,
          h213, h216, h225, h259, h261, hclean 213 (by decide), hclean 216 (by decide),
          hclean 225 (by decide), hclean 259 (by decide)]
  · simpa only [hvz, zero_add] using hvalue


end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed_oai.{u_1, u_2, u_3} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed_oai.{u_1, u_2, u_3}
