-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame.lookup_lifted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:49:43.461622+00:00
-- url     : https://prove2.me/submissions/f0e927d1-7c5a-4459-b5d3-364f29180c37

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S123

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical packing metadata lookup

The raw packing table and query remain on stacks 0 and 1. A successful lookup
returns either a block/type pair on 2/3, or a leftover rank on 4. Register 4
distinguishes those cases; all other registers and stacks 5 through 11 are
cleared. Keys, indices, and type encodings are runtime words.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMetadata

open BitProgram StructuredCalls SubexpScanPrimitives


theorem clear_eval (src : Fin 12) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) := by
  exact .call _ (ListRegisterProgram.clear_run src (0 : Fin 5) 1 d.regs d.stacks)

theorem load_eval (regs : Regs) (master query : List Bool) :
    Eval load (7 * master.length + 10 * query.length + 13)
      (inputState regs master query)
      (work (reset regs) master query master [] query.reverse) := by
  let a := inputState regs master query
  let b := afterCopy a 0 5 0 1
  let c := afterCopy b 1 6 0 1
  let d := afterTransfer c 6 7 0 1
  have h1 := SubexpScanPrimitives.copy_eval a 0 5 11 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have h2 := SubexpScanPrimitives.copy_eval b 1 6 11 0 1
    (by decide) (by decide) (by decide) (by decide) (by rfl)
  have h3 := SubexpScanPrimitives.transfer_eval c 6 7 0 1 (by decide) (by decide)
  have he : d = work (reset regs) master query master [] query.reverse := by
    apply state_ext
    · simp [d, c, b, a, afterTransfer, afterCopy, inputState, work, reset,
        StackRoutines.readRegs_reset]
    · funext i
      fin_cases i <;> simp [d, c, b, a, afterTransfer, afterCopy, inputState,
        work, StackRoutines.copyStacks, StackRoutines.transferStacks]
  have h := h1.seq (h2.seq h3)
  change Eval load _ a d at h
  rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp [a, b, c, inputState, work, afterCopy, StackRoutines.copyStacks]
  omega

theorem selectorPort_injective : Function.Injective selectorPort := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 5 + i.val = 5 + j.val at hv
  omega

theorem selector_eval (records : List (List Bool × List Bool)) (query : List Bool)
    (regs : Regs) (master : List Bool) :
    ∃ n ≤ SelectorProgram.budget query records, ∃ rf tail,
      tail.length ≤ (SelectorProgram.rawRecords records).length + query.length + n ∧
      Eval selector n
        (work regs master query (SelectorProgram.rawRecords records) [] query.reverse)
        (work rf master query tail ((records.lookup query).getD query).reverse query.reverse) := by
  obtain ⟨n, hn, rf, tail, ht⟩ := SelectorProgram.program_trace query records regs
  have hspace := trace_dataBits SelectorProgram.program ht
  have htail : tail.length ≤ (SelectorProgram.rawRecords records).length + query.length + n := by
    simp [dataBits, stackBits,
      Fin.sum_univ_succ] at hspace
    omega
  let a := work regs master query (SelectorProgram.rawRecords records) [] query.reverse
  let b := work rf master query tail ((records.lookup query).getD query).reverse query.reverse
  have ha : embedState id selectorPort a
      (SubexpRecordScan.recordState regs (SelectorProgram.rawRecords records) [] query.reverse [] [] []) = a := by
    apply embedState_eq id selectorPort Function.injective_id selectorPort_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact (hj ⟨j, rfl⟩).elim
    · intro j hj; rfl
  have hb : embedState id selectorPort a
      (SubexpRecordScan.recordState rf tail ((records.lookup query).getD query).reverse query.reverse [] [] []) = b := by
    apply embedState_eq id selectorPort Function.injective_id selectorPort_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact (hj ⟨j, rfl⟩).elim
    · intro j hj
      fin_cases j <;> simp_all [a, b, work, selectorPort, Fin.exists_fin_succ]
  have he := eval_call_lifted SelectorProgram.program id selectorPort a
    Function.injective_id selectorPort_injective ht
  exact ⟨n, hn, rf, tail, htail, by simpa only [selector, ha, hb] using he⟩

theorem cleanup_eval (regs : Regs) (master query tail payload : List Bool) :
    Eval cleanup (2 * tail.length + 2 * query.length + 3 * payload.length + 9)
      (work regs master query tail payload.reverse query.reverse)
      (work (reset regs) master query payload [] []) := by
  let a := work regs master query tail payload.reverse query.reverse
  let b := cleared 5 a
  let c := cleared 7 b
  let d := afterTransfer c 6 5 0 1
  have h1 := clear_eval 5 a
  have h2 := clear_eval 7 b
  have h3 := SubexpScanPrimitives.transfer_eval c 6 5 0 1 (by decide) (by decide)
  have he : d = work (reset regs) master query payload [] [] := by
    apply state_ext
    · simp [d, c, b, a, cleared, afterTransfer, work, reset, StackRoutines.readRegs_reset]
    · funext i
      fin_cases i <;> simp [d, c, b, a, cleared, afterTransfer, work,
        StackRoutines.transferStacks]
  have h := h1.seq (h2.seq h3)
  change Eval cleanup _ a d at h
  rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp [a, b, c, cleared, work]
  omega

theorem parserReg_injective : Function.Injective parserReg := Fin.castAdd_injective 2 3
theorem parserPort_injective (src dst : Fin 12) (h : src ≠ dst) :
    Function.Injective (parserPort src dst) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [parserPort]

theorem frame_eval (d : Data) (src dst : Fin 12) (hsd : src ≠ dst)
    (bits rest : List Bool) (hin : d.stacks src = Encoding.frame bits ++ rest) :
    Eval (frame src dst) (6 * bits.length + 4) d (framed d src dst bits rest) := by
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (Encoding.frame bits ++ rest) (d.stacks dst)⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (bits.reverse ++ d.stacks dst)⟩
  have ha : embedState parserReg (parserPort src dst) d a = d := by
    apply embedState_eq _ _ parserReg_injective (parserPort_injective src dst hsd)
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
    · intro j hj; rfl
    · intro j hj; rfl
  have hb : embedState parserReg (parserPort src dst) d b = framed d src dst bits rest := by
    apply embedState_eq _ _ parserReg_injective (parserPort_injective src dst hsd)
    · intro i; fin_cases i <;> simp [framed, b, parserReg, ParserProgram.pair, readRegs]
    · intro i; fin_cases i <;> simp [framed, b, parserPort, ParserProgram.pair, hsd]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [parserReg] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [parserReg] using h.symm⟩
      simp [framed, readRegs, h0, h1]
    · intro j hj
      have hs : j ≠ src := fun h => hj ⟨0, by simpa [parserPort] using h.symm⟩
      have hd : j ≠ dst := fun h => hj ⟨1, by simpa [parserPort] using h.symm⟩
      simp [framed, hs, hd]
  have ht : Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) :=
    ParserProgram.frame_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have he := eval_call_lifted ParserProgram.frameProgram parserReg (parserPort src dst) d
    parserReg_injective (parserPort_injective src dst hsd) ht
  simpa only [frame, ha, hb] using he

theorem parse_eval (m : Metadata) (regs : Regs) (master query : List Bool) :
    Eval parse (parseCost m) (work regs master query m.encode [] [])
      (outputState master query m) := by
  cases m with
  | covered block typeCode =>
    let a := work regs master query (Metadata.covered block typeCode).encode [] []
    let b := headed a
    let c := framed b 5 6 block (Encoding.frame typeCode)
    let d := afterTransfer c 6 2 0 1
    let e := framed d 5 6 typeCode []
    let f := afterTransfer e 6 3 0 1
    have hh : Eval header 1 a b := .base (.atom _ _)
    have h1 := frame_eval b 5 6 (by decide) block (Encoding.frame typeCode) rfl
    have h2 := SubexpScanPrimitives.transfer_eval c 6 2 0 1 (by decide) (by decide)
    have h3 := frame_eval d 5 6 (by decide) typeCode [] (by simp [d, c, framed,
      afterTransfer, StackRoutines.transferStacks])
    have h4 := SubexpScanPrimitives.transfer_eval e 6 3 0 1 (by decide) (by decide)
    have hf := RegisterResetProgram.clear_eval ([0, 1, 2, 3] : List (Fin 5)) f
    have hfinal : RegisterResetProgram.cleared [0, 1, 2, 3] f =
        outputState master query (.covered block typeCode) := by
      apply state_ext
      · funext i
        fin_cases i <;> simp [RegisterResetProgram.cleared, f, e, d, c, b, a,
          framed, afterTransfer, headed, work, Metadata.encode, outputState,
          Metadata.coveredFlag, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr, readRegs]
      · funext i
        fin_cases i <;> simp [RegisterResetProgram.cleared, f, e, d, c, b, a,
          framed, afterTransfer, headed, work, Metadata.encode, outputState,
          Metadata.block, Metadata.typeCode, Metadata.rank, StackRoutines.transferStacks,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
    rw [hfinal] at hf
    have hbody := h1.seq (h2.seq (h3.seq h4))
    have hbranch : Eval (.ite 4 coveredBody leftoverBody) _ b f := .ite_true (by rfl) hbody
    have h := hh.seq (hbranch.seq hf)
    change Eval parse _ a (outputState master query (.covered block typeCode)) at h
    convert h using 1 ; simp [parseCost, c, d, e, framed, afterTransfer,
      StackRoutines.transferStacks, a, b, headed, work, Metadata.encode,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr] ; omega
  | leftover rank =>
    let a := work regs master query (Metadata.leftover rank).encode [] []
    let b := headed a
    let c := framed b 5 6 rank []
    let d := afterTransfer c 6 4 0 1
    have hh : Eval header 1 a b := .base (.atom _ _)
    have h1 := frame_eval b 5 6 (by decide) rank [] (by simp [b, a, headed, work,
      Metadata.encode, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr])
    have h2 := SubexpScanPrimitives.transfer_eval c 6 4 0 1 (by decide) (by decide)
    have hf := RegisterResetProgram.clear_eval ([0, 1, 2, 3] : List (Fin 5)) d
    have hfinal : RegisterResetProgram.cleared [0, 1, 2, 3] d =
        outputState master query (.leftover rank) := by
      apply state_ext
      · funext i
        fin_cases i <;> simp [RegisterResetProgram.cleared, d, c, b, a,
          framed, afterTransfer, headed, work, Metadata.encode, outputState,
          Metadata.coveredFlag, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr, readRegs]
      · funext i
        fin_cases i <;> simp [RegisterResetProgram.cleared, d, c, b, a,
          framed, afterTransfer, headed, work, Metadata.encode, outputState,
          Metadata.block, Metadata.typeCode, Metadata.rank, StackRoutines.transferStacks,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
    rw [hfinal] at hf
    have hbody := h1.seq h2
    have hbranch : Eval (.ite 4 coveredBody leftoverBody) _ b d := .ite_false (by rfl) hbody
    have h := hh.seq (hbranch.seq hf)
    change Eval parse _ a (outputState master query (.leftover rank)) at h
    convert h using 1 ; simp [parseCost, c, framed, a, b, headed, work, Metadata.encode,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr] ; omega

theorem parseCost_le (m : Metadata) : parseCost m ≤ 10 * m.encode.length + 20 := by
  cases m <;> simp [parseCost, Metadata.encode] <;> omega

theorem payload_length_le (records : List (List Bool × List Bool)) (query payload : List Bool)
    (h : records.lookup query = some payload) :
    payload.length ≤ (SelectorProgram.rawRecords records).length := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp [SelectorProgram.rawRecords, List.flatMap_append]
  omega

theorem scanBudget_le (records : List (List Bool × List Bool)) (query : List Bool) :
    SelectorProgram.scanBudget query records ≤
      (9 * query.length + 20) * (SelectorProgram.rawRecords records).length + 1 := by
  induction records with
  | nil => simp [SelectorProgram.scanBudget, SelectorProgram.rawRecords]
  | cons item records ih =>
    rcases item with ⟨key, payload⟩
    simp only [SelectorProgram.scanBudget, SelectorProgram.rawRecords,
      List.flatMap_cons, List.length_append, Encoding.length_frame] at *
    unfold SubexpRecordScan.recordCost
    nlinarith

theorem budget_le (records : List (List Bool × List Bool)) (query payload : List Bool)
    (h : records.lookup query = some payload) :
    SelectorProgram.budget query records ≤ 50 * (volume records query) ^ 2 := by
  have hs := scanBudget_le records query
  have hp := payload_length_le records query payload h
  unfold SelectorProgram.budget
  rw [h]
  simp only [SelectorProgram.materializeBudget]
  unfold volume
  nlinarith

theorem command_eval (records : List (List Bool × List Bool)) (query : List Bool)
    (m : Metadata) (h : records.lookup query = some m.encode) (regs : Regs) :
    ∃ n ≤ 300 * (volume records query) ^ 2,
      Eval command n (inputState regs (SelectorProgram.rawRecords records) query)
        (outputState (SelectorProgram.rawRecords records) query m) := by
  let master := SelectorProgram.rawRecords records
  obtain ⟨n, hn, rf, tail, ht, he⟩ := selector_eval records query (reset regs) master
  rw [h] at he
  have hp := parse_eval m (reset rf) master query
  have hc := cleanup_eval rf master query tail m.encode
  have hall := (load_eval regs master query).seq (he.seq (hc.seq hp))
  change Eval command _ (inputState regs master query) (outputState master query m) at hall
  refine ⟨_, ?_, hall⟩
  have hb := budget_le records query m.encode h
  have hm := payload_length_le records query m.encode h
  have hparse := parseCost_le m
  have hv : 1 ≤ volume records query := by unfold volume; omega
  have hsq : volume records query ≤ (volume records query) ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (volume records query) hv]
  change 7 * master.length + 10 * query.length + 13 +
    (n + (2 * tail.length + 2 * query.length + 3 * m.encode.length + 9 + parseCost m)) ≤ _
  dsimp [master] at *
  have hsmall : (SelectorProgram.rawRecords records).length + query.length + 1 =
      volume records query := rfl
  nlinarith

theorem program_runsIn (records : List (List Bool × List Bool)) (query : List Bool)
    (m : Metadata) (h : records.lookup query = some m.encode) (regs : Regs) :
    RunsIn program (400 * (volume records query) ^ 2)
      ((inputState regs (SelectorProgram.rawRecords records) query).withPC (some program.entry))
      ((outputState (SelectorProgram.rawRecords records) query m).withPC none) := by
  obtain ⟨n, hn, he⟩ := command_eval records query m h regs
  refine ⟨n + 1, ?_, compiled_halt_trace he 0 2⟩
  have hv : 0 < volume records query := by unfold volume; omega
  have hp := pow_pos hv 2
  omega

end SubexponentialSAT.Subexp.GlobalBasisMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramLookupPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Two actual metadata lookups with disjoint returned records. Both query
indices and the computed metadata master are preserved. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open GlobalBasisMetadata

private theorem rowRegisters_inj : Function.Injective rowRegisters := Fin.castAdd_injective _ _
private theorem colRegisters_inj : Function.Injective colRegisters := by decide
private theorem rowPorts_inj : Function.Injective rowPorts := by decide
private theorem colPorts_inj : Function.Injective colPorts := by decide

private theorem row_embed (regs : Fin 6 → Bool) (master row col : List Bool) (m : Metadata) :
    embedState rowRegisters rowPorts (state regs master row col [] [] [] [] [] [])
      (GlobalBasisMetadata.outputState master row m) =
      state ![false,false,false,false,m.coveredFlag,regs 5]
        master row col m.block m.typeCode m.rank [] [] [] := by
  apply embedState_eq_of_ports _ _ _ _ _ rowRegisters_inj rowPorts_inj
  · intro j; fin_cases j <;> simp [state,GlobalBasisMetadata.outputState,rowRegisters]
  · intro j hj
    have h : j = 5 := by
      fin_cases j <;> simp_all [rowRegisters,Fin.exists_fin_succ]
    subst j; rfl
  · intro j; fin_cases j <;> simp [state,GlobalBasisMetadata.outputState,rowPorts]
  · intro j hj
    fin_cases j <;> simp_all [state,rowPorts,Fin.exists_fin_succ]

private theorem col_embed (regs : Fin 6 → Bool) (master row col : List Bool)
    (rb rt rr : List Bool) (m : Metadata) :
    embedState colRegisters colPorts (state regs master row col rb rt rr [] [] [])
      (GlobalBasisMetadata.outputState master col m) =
      state ![false,false,false,false,regs 4,m.coveredFlag]
        master row col rb rt rr m.block m.typeCode m.rank := by
  apply embedState_eq_of_ports _ _ _ _ _ colRegisters_inj colPorts_inj
  · intro j; fin_cases j <;> simp [state,GlobalBasisMetadata.outputState,colRegisters]
  · intro j hj
    fin_cases j <;> simp_all [state,colRegisters,Fin.exists_fin_succ]
  · intro j; fin_cases j <;> simp [state,GlobalBasisMetadata.outputState,colPorts]
  · intro j hj
    fin_cases j <;> simp_all [state,colPorts,Fin.exists_fin_succ]

/-- The lookup hypotheses identify the actual serialized metadata records.
They are discharged by `PackingMetadata.lookup_eq`, not by a supplied oracle. -/
theorem program_runsIn (records : List (List Bool × List Bool)) (row col : List Bool)
    (mr mc : Metadata) (hr : records.lookup row = some mr.encode)
    (hc : records.lookup col = some mc.encode) (regs : Fin 6 → Bool) :
    RunsIn program (400*(volume records row)^2+400*(volume records col)^2+1)
      ((state regs (SelectorProgram.rawRecords records) row col [] [] [] [] [] []).withPC
        (some program.entry))
      ((state ![false,false,false,false,mr.coveredFlag,mc.coveredFlag]
        (SelectorProgram.rawRecords records) row col mr.block mr.typeCode mr.rank
          mc.block mc.typeCode mc.rank).withPC none) := by
  let master := SelectorProgram.rawRecords records
  let a := state regs master row col [] [] [] [] [] []
  obtain ⟨nr,hnr,tr⟩ := GlobalBasisMetadata.program_runsIn records row mr hr
    (regs ∘ rowRegisters)
  have hp : projectState rowRegisters rowPorts a =
      GlobalBasisMetadata.inputState (regs ∘ rowRegisters) master row := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a,state,rowPorts
]
  rw [← hp] at tr
  have er := eval_call_from_state GlobalBasisMetadata.program rowRegisters rowPorts a
    rowRegisters_inj rowPorts_inj tr
  rw [show a = state regs master row col [] [] [] [] [] [] from rfl,row_embed] at er
  let midregs : Fin 6 → Bool := ![false,false,false,false,mr.coveredFlag,regs 5]
  let b := state midregs master row col mr.block mr.typeCode mr.rank [] [] []
  obtain ⟨nc,hnc,tc⟩ := GlobalBasisMetadata.program_runsIn records col mc hc
    (midregs ∘ colRegisters)
  have hq : projectState colRegisters colPorts b =
      GlobalBasisMetadata.inputState (midregs ∘ colRegisters) master col := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [b,state,colPorts
]
  rw [← hq] at tc
  have ec := eval_call_from_state GlobalBasisMetadata.program colRegisters colPorts b
    colRegisters_inj colPorts_inj tc
  rw [show b = state midregs master row col mr.block mr.typeCode mr.rank [] [] [] from rfl,
    col_embed] at ec
  refine ⟨nr+nc+1,by omega,?_⟩
  exact compiled_halt_trace (er.seq ec) 0 3

end SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrameLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem lookup_lifted_oai {R S : ℕ} (register : Fin 6 → Fin R) (stack : Fin 16 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (a : State R S) (records : List (List Bool × List Bool)) (row col : List Bool)
    (mr mc : GlobalBasisMetadata.Metadata)
    (hr : records.lookup row=some mr.encode) (hc : records.lookup col=some mc.encode)
    (ha : projectState register stack a=LookupPair.state (a.regs ∘ register)
      (SelectorProgram.rawRecords records) row col [] [] [] [] [] []) :
    ∃ n ≤ 400*(GlobalBasisMetadata.volume records row)^2+
        400*(GlobalBasisMetadata.volume records col)^2+1,
      ∃ e : State R S,
      Eval (.call (ProgramLinking.liftProgram LookupPair.program register stack)) n a e ∧
      projectState register stack e=
        LookupPair.state ![false,false,false,false,mr.coveredFlag,mc.coveredFlag]
          (SelectorProgram.rawRecords records) row col mr.block mr.typeCode mr.rank
            mc.block mc.typeCode mc.rank ∧
      (∀ j, (¬ ∃ i, stack i=j) → e.stacks j=a.stacks j) ∧
      (∀ j, (¬ ∃ i, register i=j) → e.regs j=a.regs j) := by
  obtain ⟨n,hn,he⟩ := LookupPair.program_runsIn records row col mr mc hr hc (a.regs ∘ register)
  rw [← ha] at he
  let b := LookupPair.state ![false,false,false,false,mr.coveredFlag,mc.coveredFlag]
    (SelectorProgram.rawRecords records) row col mr.block mr.typeCode mr.rank
      mc.block mc.typeCode mc.rank
  refine ⟨n,hn,embedState register stack a b,
    eval_call_from_state LookupPair.program register stack a hregister hstack he,?_,?_,?_⟩
  · exact projectState_embed register stack a b hregister hstack
  · exact fun j hj => embedState_stack_frame register stack a b j hj
  · exact fun j hj => embedState_register_frame register stack a b j hj

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame.lookup_lifted_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame.lookup_lifted_oai
