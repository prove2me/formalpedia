-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.popCurrent_boundary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:34:30.970632+00:00
-- url     : https://prove2.me/submissions/1391f385-3538-49f9-b674-01ef33f07c32

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BitProgramSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Data-size bounds for the concrete Boolean-stack machine. A single
instruction can allocate at most one new bit. These bounds concern the actual
configurations on measured traces, not an auxiliary cost annotation. -/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

theorem stackBits_update {s : ℕ} (stk : Fin s → List Bool) (k : Fin s)
    (word : List Bool) :
    stackBits (Function.update stk k word) + (stk k).length = stackBits stk + word.length := by
  have lengths : (fun i => (Function.update stk k word i).length) =
      Function.update (fun i => (stk i).length) k word.length := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  unfold stackBits
  rw [lengths, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun i => (stk i).length) (Finset.mem_univ k)
  omega

theorem execInstr_dataBits {r s l : ℕ} (i : Instr r s l) (c : Cfg r s l) :
    dataBits (execInstr i c) ≤ dataBits c + 1 := by
  cases i <;> try simp [dataBits, execInstr]
  · rename_i stack src next
    have h := stackBits_update c.stacks stack (c.regs src :: c.stacks stack)
    simp only [List.length_cons] at h
    change stackBits (Function.update c.stacks stack (c.regs src :: c.stacks stack)) ≤ _
    omega
  · rename_i stack value present next
    have h := stackBits_update c.stacks stack (c.stacks stack).tail
    have htail : (c.stacks stack).tail.length ≤ (c.stacks stack).length := by
      cases c.stacks stack <;> simp
    change stackBits (Function.update c.stacks stack (c.stacks stack).tail) ≤ _
    omega

theorem step_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l}
    (h : step p a = some b) : dataBits b ≤ dataBits a + 1 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some label =>
      simp [step, hp] at h
      rw [← h]
      exact execInstr_dataBits _ _

theorem trace_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : Trace p n a b) : dataBits b ≤ dataBits a + n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hstep := step_dataBits p hs
      omega

end SubexponentialSAT.BitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StructuredSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix resource preservation for the actual finite instruction linker.
The source bound concerns every intermediate configuration. Unassigned caller
stacks retain their original contents. Local runtime bounds may be used for
polynomial subroutines, but no accumulated outer-loop time appears here. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

open BitProgram

/-- Every prefix of a relocated source execution is exactly the relocation of
the same-length source prefix, including a halt changed to a return jump. -/
theorem relocate_trace_prefix {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps prefixSteps : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b) {intermediate : Cfg R S L}
    (hle : prefixSteps ≤ steps)
    (hp : Trace q prefixSteps
      (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate) :
    ∃ source, Trace p prefixSteps a source ∧
      intermediate = ProgramLinking.embedCfg register stack label returnPc frame source := by
  obtain ⟨source, hsource⟩ := trace_prefix_exists tr hle
  refine ⟨source, hsource, ?_⟩
  exact trace_same_length_unique hp
    (ProgramLinking.relocate_trace p q register stack label returnPc frame
      hregister hstack hcode hsource)

/-- Port embedding preserves a uniform local stack bound and the caller's
off-port bound separately. It never charges the caller's frame repeatedly. -/
theorem relocate_trace_stack_bound {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace q prefixSteps
        (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  intro prefixSteps intermediate hle hp i
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix p q register stack label
    returnPc frame hregister hstack hcode tr hle hp
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [ProgramLinking.embedCfg_stack register stack label returnPc frame source hstack]
    exact (hsource prefixSteps source hle hs j).trans (Nat.le_max_left _ _)
  · rw [ProgramLinking.embedCfg_stack_frame register stack label returnPc frame source i hi]
    exact (hframe i).trans (Nat.le_max_right _ _)

theorem liftProgram_stack_bound {r s l R S : ℕ}
    (p : Program r s l) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram p register stack) prefixSteps
        (ProgramLinking.embedCfg register stack id none frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound :=
  relocate_trace_stack_bound p _ register stack id none frame hregister hstack
    (fun _ => rfl) tr hsource hframe

/-- A structured call retains its callee's every-prefix stack bound in the
actual caller table. The table premise is the same one used by eval_trace. -/
theorem call_stack_bound {r s l L : ℕ} (routine : Program r s l)
    (caller : Program r s L) (label : Fin l → Fin L) (exit : Fin L)
    (hcode : ∀ pc, caller.code (label pc) =
      StructuredCalls.code (.call routine) label exit pc)
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (tr : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps (a.withPC (some (label routine.entry))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  have hinitial : ProgramLinking.embedCfg id id label (some exit)
      (a.withPC (some (label routine.entry))) (a.withPC (some routine.entry)) =
      a.withPC (some (label routine.entry)) := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC]
  rw [← hinitial] at hp
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix routine caller id id label
    (some exit) (a.withPC (some (label routine.entry)))
    Function.injective_id Function.injective_id hcode tr hle hp
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseFrontierProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete LIFO storage for normalized formula bodies.

Stack zero is the current body, stack two is the framed pending list, and stack
three is scratch. Stack one is preserved and may hold the declared variable
count. The list's final false bit is retained; emptiness is tested by peeking,
so an empty frontier never causes an unguarded removal of a sentinel.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram

open BitProgram StructuredCalls SubexpPostfixControl

theorem transfer_eval (src dst : Fin 4) (hsd : src ≠ dst) (d : State 3 4) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d
      ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩ := by
  exact Eval.call _ (ListRegisterProgram.transfer_run src dst 0 1 hsd (by decide)
    d.regs d.stacks)

theorem reader_state (base : State 3 4) (current saved source payload : List Bool)
    (v p flag : Bool)
    (h0 : base.stacks 0 = current) (h1 : base.stacks 1 = saved) :
    RecordPrograms.state readerPorts base v p flag source payload =
      state v p flag current saved source payload := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [readerPorts, triple]
  · funext i
    fin_cases i <;> simp [readerPorts, quadruple, h0, h1]

theorem pop_eval (body saved pending : List Bool) (v p flag : Bool) :
    Eval pop (9 * body.length + 8)
      (state v p flag [] saved (true :: (Encoding.frame body ++ pending)) [])
      (state false false flag body saved pending []) := by
  have hp : Eval (.base (.atom (.pop (2 : Fin 4) (0 : Fin 3) 1))) 1
      (state v p flag [] saved (true :: (Encoding.frame body ++ pending)) [])
      (state true true flag [] saved (Encoding.frame body ++ pending) []) := by
    simpa [state, SubexpNormalizeProgram.filterState, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr, readRegs]
      using Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 4) (0 : Fin 3) 1)
        (state v p flag [] saved (true :: (Encoding.frame body ++ pending)) []))
  let base := state true true flag [] saved (Encoding.frame body ++ pending) []
  have hr : Eval (RecordPrograms.reader readerPorts) (6 * body.length + 4)
      base (state false true flag [] saved pending body.reverse) := by
    have h := RecordPrograms.reader_eval readerPorts base body pending [] true true flag
    rw [reader_state base [] saved _ _ _ _ _ rfl rfl,
      reader_state base [] saved _ _ _ _ _ rfl rfl] at h
    simpa [base] using h
  have ht : Eval (transfer 3 0) (3 * body.length + 3)
      (state false true flag [] saved pending body.reverse)
      (state false false flag body saved pending []) := by
    simpa [state, SubexpNormalizeProgram.filterState, StackRoutines.transferStacks,
      readRegs] using transfer_eval 3 0 (by decide)
        (state false true flag [] saved pending body.reverse)
  convert hp.seq (hr.seq ht) using 1 <;> first | rfl | omega

theorem test_eval (b : Bool) (tail current saved scratch : List Bool) (v p flag : Bool) :
    Eval test 1 (state v p flag current saved (b :: tail) scratch)
      (state v true b current saved (b :: tail) scratch) := by
  simpa [test, state, SubexpNormalizeProgram.filterState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr, readRegs]
    using Eval.base (StructuredProgram.Eval.atom (.peek (2 : Fin 4) (2 : Fin 3) 1)
      (state v p flag current saved (b :: tail) scratch))

theorem popIfPresent_cons (body saved pending : List Bool) (v p flag : Bool) :
    Eval popIfPresent (9 * body.length + 10)
      (state v p flag [] saved (true :: (Encoding.frame body ++ pending)) [])
      (state false false true body saved pending []) := by
  have ht := test_eval true (Encoding.frame body ++ pending) [] saved [] v p flag
  have hp : Eval (.ite (2 : Fin 3) pop (.base .skip)) (9 * body.length + 9)
      (state v true true [] saved (true :: (Encoding.frame body ++ pending)) [])
      (state false false true body saved pending []) := by
    simpa only [Nat.add_assoc] using
      Eval.ite_true (no := .base .skip) (test := (2 : Fin 3)) rfl
        (pop_eval body saved pending v true true)
  convert ht.seq hp using 1 <;> first | rfl | omega

theorem popIfPresent_cons_trace (body saved pending : List Bool) (v p flag : Bool) :
    Trace popIfPresentProgram (9 * body.length + 11)
      ((state v p flag [] saved (true :: (Encoding.frame body ++ pending)) []).withPC
        (some popIfPresentProgram.entry))
      ((state false false true body saved pending []).withPC none) := by
  simpa only [popIfPresentProgram, Nat.add_assoc] using compiled_halt_trace
    (popIfPresent_cons body saved pending v p flag) 2 0

theorem state_dataBits {l : ℕ} (pc : Option (Fin l))
    (current saved pending scratch : List Bool) (v p flag : Bool) :
    dataBits ((state v p flag current saved pending scratch).withPC pc) =
      current.length + saved.length + pending.length + scratch.length := by
  simp [dataBits, stackBits, state, SubexpNormalizeProgram.filterState,
    quadruple, Fin.sum_univ_succ, Nat.add_assoc]

theorem popIfPresent_prefix_space (body saved pending : List Bool) (v p flag : Bool)
    (t : ℕ) (c : Cfg 3 4 (size popIfPresent + 1)) (ht : t ≤ 9 * body.length + 11)
    (hc : Trace popIfPresentProgram t
      ((state v p flag [] saved (true :: (Encoding.frame body ++ pending)) []).withPC
        (some popIfPresentProgram.entry)) c) :
    dataBits c ≤ saved.length + pending.length + 11 * body.length + 13 := by
  have h := trace_dataBits popIfPresentProgram hc
  rw [state_dataBits] at h
  simp only [List.length_nil, List.length_cons, List.length_append,
    Encoding.length_frame] at h
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSResource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Resource bounds for the actual outer DFS commands.

Cleanup is structurally nonallocating. The bounds below concern the concrete
finite tables and every source prefix, before applying the guarded primitive
compiler. The selector and leaf contracts still require their own executions.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource

open BitProgram StructuredCalls SparseDFSProgram

private theorem stackBits_single_le {S : ℕ} (words : Fin S → List Bool) (i : Fin S) :
    (words i).length ≤ stackBits words :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((words j).length)) (Finset.mem_univ i)

private theorem lifted_call_space {r s l steps localBound frameBound : ℕ}
    (routine : Program r s l) (register : Fin r ↪ Fin 80) (stack : Fin s ↪ Fin 1220)
    (frame : Data) {a b : State r s}
    (htrace : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hlocal : ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) c →
      ∀ i, (c.stacks i).length ≤ localBound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256)
        prefixSteps ((embedState register stack frame a).withPC
          (some (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ max localBound frameBound := by
  have hsource := StructuredSpace.liftProgram_stack_bound routine register stack
    (frame.withPC none) register.injective stack.injective htrace hlocal hframe
  have he := eval_call_lifted routine register stack frame register.injective stack.injective htrace
  cases he with
  | call p ht =>
      apply StructuredSpace.call_stack_bound (ProgramLinking.liftProgram routine register stack)
        (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256)
        (siteAddress (.call (ProgramLinking.liftProgram routine register stack)))
        (exitAddress (.call (ProgramLinking.liftProgram routine register stack)))
        (compiled_site (.call (ProgramLinking.liftProgram routine register stack)) 256 256) ht
      simpa only [ProgramLinking.embedCfg, ProgramLinking.relocatePc, embedState,
        StructuredProgram.State.withPC, id_eq] using hsource

/-- A real nonempty frontier pop decodes only its head record. All 1220 root
stacks are included, and no earlier traversal time appears in the bound. -/
theorem popCurrent_execution_space (frame : Data) (bodyWord saved pending : List Bool)
    (v p flag : Bool) (frameBound : ℕ)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    Eval popCurrent (9 * bodyWord.length + 11)
      (embedState (registers 3 (by decide)) frontierStack frame
        (SparseFrontierProgram.state v p flag [] saved
          (true :: (Encoding.frame bodyWord ++ pending)) []))
      (embedState (registers 3 (by decide)) frontierStack frame
        (SparseFrontierProgram.state false false true bodyWord saved pending [])) ∧
    ∀ prefixSteps c, prefixSteps ≤ 9 * bodyWord.length + 11 →
      Trace (compiled popCurrent 256 256) prefixSteps
        ((embedState (registers 3 (by decide)) frontierStack frame
          (SparseFrontierProgram.state v p flag [] saved
            (true :: (Encoding.frame bodyWord ++ pending)) [])).withPC
              (some (compiled popCurrent 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤
        max (saved.length + pending.length + 11 * bodyWord.length + 13) frameBound := by
  have htrace := SparseFrontierProgram.popIfPresent_cons_trace bodyWord saved pending v p flag
  refine ⟨eval_call_lifted SparseFrontierProgram.popIfPresentProgram
    (registers 3 (by decide)) frontierStack frame (registers 3 (by decide)).injective
    frontierStack.injective htrace, ?_⟩
  apply lifted_call_space SparseFrontierProgram.popIfPresentProgram
    (registers 3 (by decide)) frontierStack frame htrace _ hframe
  intro t c ht hc i
  exact (stackBits_single_le c.stacks i).trans
    (SparseFrontierProgram.popIfPresent_prefix_space bodyWord saved pending v p flag t c ht hc)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CountDFS
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Typed refinement of the concrete streaming frontier.

Depths and derivation trees below are proof indices. The physical pending tape
contains only formula bodies, and every formula keeps the same declared `Fin n`.
The selector and leaf execution contracts must still be supplied by their actual
finite programs; this module does not postulate a final counting service.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement

open SAT SparsePriorityProgram BitProgram StructuredCalls

variable {n : ℕ}

open SparseDFSProgram

theorem popCurrent_boundary_oai (threshold : List Bool) (node : Node n)
    (rest : List (Node n)) (total : ℕ) (d : Data) (bound : ℕ)
    (hb : Boundary threshold ⟨node :: rest, total⟩ d)
    (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    ∃ e, Eval popCurrent (9 * (SparseCountProgram.encodeBody node.formula).length + 11) d e ∧
      e.stacks 265 = SparseCountProgram.encodeBody node.formula ∧
      e.stacks 257 = pendingBytes rest ∧
      (∀ i, i ≠ 265 → i ≠ 257 → e.stacks i = d.stacks i) ∧
      (∀ i, i.val < 256 → e.stacks i = []) ∧
      e.regs 0 = false ∧ e.regs 1 = false ∧ e.regs 2 = true ∧
      ∀ prefixSteps c,
        prefixSteps ≤ 9 * (SparseCountProgram.encodeBody node.formula).length + 11 →
        Trace (compiled popCurrent 256 256) prefixSteps
          (d.withPC (some (compiled popCurrent 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max
          (n + 1 + (pendingBytes rest).length +
            11 * (SparseCountProgram.encodeBody node.formula).length + 13) bound := by
  let a := SparseFrontierProgram.state (d.regs 0) (d.regs 1) (d.regs 2)
    [] (Encoding.encodeNat n)
    (true :: (Encoding.frame (SparseCountProgram.encodeBody node.formula) ++
      pendingBytes rest)) []
  let b := SparseFrontierProgram.state false false true
    (SparseCountProgram.encodeBody node.formula) (Encoding.encodeNat n) (pendingBytes rest) []
  have hinput : embedState (registers 3 (by decide)) frontierStack d a = d := by
    apply embedState_eq_of_ports _ _ d d a (registers 3 (by decide)).injective
      frontierStack.injective
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      rfl
    · intro i
      fin_cases i
      · exact hb.current_empty
      · exact hb.header
      · change d.stacks 257 =
          true :: (Encoding.frame (SparseCountProgram.encodeBody node.formula) ++
            pendingBytes rest)
        simpa only [pendingBytes_cons, ExecWorklistProgram.record, List.cons_append]
          using hb.pending
      · exact hb.low_empty 23 (by decide)
    · intro i hi
      rfl
  obtain ⟨heval, hspace⟩ := SparseDFSResource.popCurrent_execution_space d
    (SparseCountProgram.encodeBody node.formula) (Encoding.encodeNat n) (pendingBytes rest)
    (d.regs 0) (d.regs 1) (d.regs 2) bound hbound
  change Eval popCurrent _ (embedState _ _ d a) (embedState _ _ d b) at heval
  rw [hinput] at heval
  let e := embedState (registers 3 (by decide)) frontierStack d b
  have hout (i : Fin 4) : e.stacks (frontierStack i) = b.stacks i :=
    embedState_stack _ _ _ _ frontierStack.injective i
  have hframe (i : Fin 1220) (hcurrent : i ≠ 265) (hpending : i ≠ 257) :
      e.stacks i = d.stacks i := by
    by_cases hi : ∃ j, frontierStack j = i
    · obtain ⟨j, rfl⟩ := hi
      fin_cases j
      · exact (hcurrent rfl).elim
      · exact (hout 1).trans hb.header.symm
      · exact (hpending rfl).elim
      · exact (hout 3).trans (hb.low_empty 23 (by decide)).symm
    · exact embedState_stack_frame _ _ _ _ i hi
  refine ⟨e, heval, hout 0, hout 2, hframe, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hframe i (by intro h; subst i; omega) (by intro h; subst i; omega)]
    exact hb.low_empty i hi
  · exact embedState_register _ _ _ _ (registers 3 (by decide)).injective 0
  · exact embedState_register _ _ _ _ (registers 3 (by decide)).injective 1
  · exact embedState_register _ _ _ _ (registers 3 (by decide)).injective 2
  · change ∀ prefixSteps c, prefixSteps ≤ _ →
      Trace (compiled popCurrent 256 256) prefixSteps
        ((embedState _ _ d a).withPC _) c → _ at hspace
    rw [hinput] at hspace
    simpa only [Encoding.length_encodeNat] using hspace


/- Typed empty-input cases. -/

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.popCurrent_boundary_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.popCurrent_boundary_oai
