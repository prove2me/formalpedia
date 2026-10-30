-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:39:51.606554+00:00
-- url     : https://prove2.me/submissions/224b1ff6-e742-404d-a8c3-91df82f82ce6

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S079
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S111
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_ExecClauseFiltersProgram_scan_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSemanticHelpers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact list identities used when composing executable CNF filters. -/
namespace SubexponentialSAT.Encoding
universe u

/-- Filtering discards complete frames; this bound needs no property of the
payload encoder. -/
theorem length_encodeList_filter_le {α : Type u} (enc : α → List Bool)
    (keep : α → Bool) (values : List α) :
    (encodeList enc (values.filter keep)).length ≤ (encodeList enc values).length := by
  induction values with
  | nil => simp
  | cons a values ih =>
    cases h : keep a with
    | false =>
      simp [ h, length_encodeList_cons] ; omega
    | true =>
      simp [ h, length_encodeList_cons] ; omega

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseFilterReverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared actual record reversal for the clause-filter storage layout. -/

namespace SubexponentialSAT.ExecClauseFilterReverse

open BitProgram StructuredCalls

theorem flags_self (regs : Regs) : flags regs (regs 0) (regs 1) (regs 14) = regs := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h14 : i = 14 <;>
    simp_all [flags ]

theorem regPort_injective : Function.Injective regPort := by decide
theorem stackPort_injective : Function.Injective stackPort := by decide

private theorem embed_reverse (regs : Regs) (value present found : Bool)
    (source0 output0 payload0 source output payload : List Bool) :
    embedState regPort stackPort (state regs source0 output0 payload0)
      (SubexpNormalizeProgram.filterState value present found source [] output payload) =
      state (flags regs value present found) output source payload := by
  apply embedState_eq_of_ports regPort stackPort _ _ _ regPort_injective stackPort_injective
  · intro i
    fin_cases i <;> simp [regPort, flags, state, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.triple]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h14 : i ≠ 14 := fun h => hi ⟨2, h.symm⟩
    simp [state, flags, h0, h1, h14]
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h14 : i ≠ 14 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1, h.symm⟩
    have h13 : i ≠ 13 := fun h => hi ⟨2, h.symm⟩
    have h15 : i ≠ 15 := fun h => hi ⟨3, h.symm⟩
    fin_cases i <;> simp_all [state]

/-- Reverse whole records from stack 14 onto the encoded accumulator in
stack 13. All thirteen work stacks and payload stack 15 finish empty. -/
theorem reverse_eval (records acc : List (List Bool)) (regs : Regs) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length,
      Eval command n
        (state regs (Encoding.encodeList id acc) (Encoding.encodeList id records) [])
        (state (flags regs false true false)
          (Encoding.encodeList id (records.reverse ++ acc)) [] []) := by
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc [] []
    (regs 0) (regs 1) (regs 14)
  simp only [List.append_nil] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram regPort stackPort
    (state regs (Encoding.encodeList id acc) (Encoding.encodeList id records) [])
    regPort_injective stackPort_injective ht
  refine ⟨n, hn, ?_⟩
  simpa only [embed_reverse, flags_self, command, program] using he

end SubexponentialSAT.ExecClauseFilterReverse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseFiltersProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact-order clause filters on encoded formulas

The relation scanner occupies stacks 0--12. The outer record pass uses stack
13 for unread records, stack 14 for the reversed output record list, and stack
15 for the reversed current payload. Two stack transfers put a clause into the
scanner and return it to the existing frame emitter.
-/


namespace SubexponentialSAT.ExecClauseFiltersProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)

theorem transfer_eval (source target : Fin 16) (d : Data) (hne : source ≠ target) :
    Eval (transfer source target) (3 * (d.stacks source).length + 3)
      d (transferred source target d) :=
  .call _ (ListRegisterProgram.transfer_run source target 0 1 hne (by decide) d.regs d.stacks)

theorem clear_eval (port : Fin 16) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) :=
  .call _ (ListRegisterProgram.clear_run port 0 1 d.regs d.stacks)

theorem transfer_into_query (regs : Regs) (bits master source output : List Bool) :
    Eval (transfer 15 9) (3 * bits.length + 3)
      (state regs [] [] master source output bits.reverse)
      (state (reset regs) bits [] master source output []) := by
  have heq : transferred 15 9 (state regs [] [] master source output bits.reverse) =
      state (reset regs) bits [] master source output [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state, StackRoutines.transferStacks]
  have h := transfer_eval 15 9 (state regs [] [] master source output bits.reverse) (by decide)
  rw [heq] at h
  simpa [state] using h

theorem transfer_from_query (regs : Regs) (bits master source output : List Bool) :
    Eval (transfer 9 15) (3 * bits.length + 3)
      (state regs bits [] master source output [])
      (state (reset regs) [] [] master source output bits.reverse) := by
  have heq : transferred 9 15 (state regs bits [] master source output []) =
      state (reset regs) [] [] master source output bits.reverse := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state, StackRoutines.transferStacks]
  have h := transfer_eval 9 15 (state regs bits [] master source output []) (by decide)
  rw [heq] at h
  simpa [state] using h

theorem clear_answer (regs : Regs) (answer : Bool) (query master source output : List Bool) :
    Eval (clear 11) 5
      (state regs query [answer] master source output [])
      (state (reset regs) query [] master source output []) := by
  have heq : cleared 11 (state regs query [answer] master source output []) =
      state (reset regs) query [] master source output [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state, StackRoutines.clearStacks]
  have h := clear_eval 11 (state regs query [answer] master source output [])
  rw [heq] at h
  simpa [state] using h

theorem emitRegs_injective : Function.Injective emitRegs := by decide
theorem emitStacks_injective : Function.Injective emitStacks := by decide

private theorem embed_emit (regs : Regs) (value present selected : Bool)
    (query0 source0 output0 payload0 query source output payload answer master : List Bool) :
    embedState emitRegs emitStacks (state regs query0 answer master source0 output0 payload0)
      (SubexpNormalizeProgram.filterState value present selected source query output payload) =
      state (flags regs value present selected) query answer master source output payload := by
  apply embedState_eq_of_ports emitRegs emitStacks _ _ _ emitRegs_injective emitStacks_injective
  · intro i
    fin_cases i <;> simp [emitRegs, flags, state, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.triple]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h14 : i ≠ 14 := fun h => hi ⟨2, h.symm⟩
    simp [state, flags, h0, h1, h14]
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h13 : i ≠ 13 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1, h.symm⟩
    have h14 : i ≠ 14 := fun h => hi ⟨2, h.symm⟩
    have h15 : i ≠ 15 := fun h => hi ⟨3, h.symm⟩
    fin_cases i <;> simp_all [state]

theorem emit_eval (regs : Regs) (bits master source output : List Bool) :
    Eval emit (SubexpNormalizeProgram.emitIfSelectedSteps (regs 14) bits + 1)
      (state regs [] [] master source output bits.reverse)
      (state (flags regs false true false) [] [] master source
        (if regs 14 then true :: (Encoding.frame bits ++ output) else output) []) := by
  have h := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram emitRegs emitStacks
    (state regs [] [] master source output bits.reverse) emitRegs_injective emitStacks_injective
    (SubexpNormalizeProgram.emitIfSelected_trace (regs 14) bits source [] output (regs 0) (regs 1))
  simpa only [embed_emit, flags_self, emit] using h

/-- A complete encoded clause-selection callback, including the actual
relation scan, result cleanup, and framed output emission. -/
theorem callback_eval (mode : Mode) (F : Formula) (Q : Clause) (regs : Regs)
    (source output : List Bool) :
    ∃ (n : ℕ) (rf : Regs), n ≤ callbackBound F Q ∧
      rf 0 = false ∧ rf 1 = true ∧ rf 14 = false ∧
      Eval (callback mode) n
        (state regs [] [] (encodeFormula F) source output (encodeClause Q).reverse)
        (state rf [] [] (encodeFormula F) source
          (if !(F.any (fun C => test mode C Q)) then
            true :: (Encoding.frame (encodeClause Q) ++ output) else output) []) := by
  obtain ⟨n, scanned, hn, hflag, hscan⟩ :=
    scan_eval mode F Q (reset regs) source output
  let restored := reset (reset scanned)
  let flipped := Function.update restored 14 (!(restored 14))
  have hflip : Eval (.base (.atom (.bnot 14 14))) 1
      (state restored [] [] (encodeFormula F) source output (encodeClause Q).reverse)
      (state flipped [] [] (encodeFormula F) source output (encodeClause Q).reverse) := by
    exact .base (.atom _ _)
  have hselected : flipped 14 = !(F.any (fun C => test mode C Q)) := by
    simp [flipped, restored, reset, readRegs, hflag]
  have hemit := emit_eval flipped (encodeClause Q) (encodeFormula F) source output
  rw [hselected] at hemit
  have hfull := (transfer_into_query regs (encodeClause Q) (encodeFormula F) source output).seq
    (hscan.seq ((clear_answer scanned (F.any (fun C => test mode C Q))
      (encodeClause Q) (encodeFormula F) source output).seq
      ((transfer_from_query (reset scanned) (encodeClause Q) (encodeFormula F) source output).seq
        (hflip.seq hemit))))
  refine ⟨_, flags flipped false true false, ?_, ?_, ?_, ?_, hfull⟩
  · have hcost := SubexpNormalizeProgram.emitIfSelected_steps_le
      (!(F.any (fun C => test mode C Q))) (encodeClause Q)
    unfold callbackBound
    omega
  · simp [flags]
  · simp [flags]
  · simp [flags]

theorem record_state (regs : Regs) (query answer master source output payload tail bits : List Bool)
    (v p f : Bool) :
    RecordPrograms.state ports (state regs query answer master source output payload)
      v p f tail bits = state (flags regs v p f) query answer master tail output bits := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ ports, state]

theorem state_invariant (F : Formula) (regs : Regs) (source output payload : List Bool) :
    invariant F (state regs [] [] (encodeFormula F) source output payload) :=
  ⟨regs, source, output, payload, rfl⟩

theorem callbackBound_le (F : Formula) (Q : Clause) :
    callbackBound F Q ≤ perClauseCost F (encodeClause Q) := by
  unfold callbackBound perClauseCost ExecClauseRelationScan.Preserving.bound
  nlinarith

theorem callback_contract (mode : Mode) (F : Formula) :
    RecordPrograms.CallbackContractWithOn ports (callback mode) (fun _ => false)
      (perClauseCost F) (invariant F) (SubexpNormalizeProgram.FilterEffect 14 (keep mode F))
      ClausePayload := by
  intro bits tail base hbits hbase
  obtain ⟨Q, rfl⟩ := hbits
  obtain ⟨regs, source, output, payload, rfl⟩ := hbase
  obtain ⟨n, rf, hn, h0, h1, h14, he⟩ :=
    callback_eval mode F Q (flags regs false true false) tail output
  let newOutput := if !(F.any (fun C => test mode C Q)) then
    true :: (Encoding.frame (encodeClause Q) ++ output) else output
  let next := state rf [] [] (encodeFormula F) [] newOutput []
  have hflags : flags rf false true false = rf := by
    simpa only [h0, h1, h14] using flags_self rf
  refine ⟨n, next, hn.trans (callbackBound_le F Q), state_invariant _ _ _ _ _, ?_, ?_⟩
  · simp [SubexpNormalizeProgram.FilterEffect, next, newOutput, state]
  · simpa only [next, record_state, hflags] using he

theorem encodeFormula_records (F : Formula) :
    encodeFormula F = Encoding.encodeList id (formulaRecords F) := by
  induction F with
  | nil => rfl
  | cons C F ih => simpa [encodeFormula, formulaRecords, Encoding.encodeList] using ih

theorem valid_formulaRecords (F : Formula) :
    ∀ bits ∈ formulaRecords F, ClausePayload bits := by
  intro bits hb
  obtain ⟨C, _, rfl⟩ := List.mem_map.mp hb
  exact ⟨C, rfl⟩

theorem filtered_formulaRecords (mode : Mode) (master F : Formula) :
    (formulaRecords F).filter (keep mode master) = formulaRecords (filtered mode master F) := by
  induction F with
  | nil => rfl
  | cons Q F ih =>
    simp only [formulaRecords, filtered] at ih
    cases h : !(master.any (fun C => test mode C Q)) <;>
      simp [formulaRecords, filtered, h, ih]

theorem filtered_length_le (mode : Mode) (master F : Formula) :
    (encodeFormula (filtered mode master F)).length ≤ (encodeFormula F).length :=
  Encoding.length_encodeList_filter_le encodeClause
    (fun Q => !(master.any (fun C => test mode C Q))) F

theorem filter_budget_le (master : Formula) (records : List (List Bool)) :
    3 + RecordPrograms.budget (perClauseCost master) records ≤
      620 * ((encodeFormula master).length + 1) *
        ((Encoding.encodeList id records).length + 1) := by
  induction records with
  | nil => simp [RecordPrograms.budget, Encoding.encodeList]; omega
  | cons bits records ih =>
    simp only [RecordPrograms.budget, perClauseCost, Encoding.length_encodeList_cons, id_eq]
    nlinarith

theorem encoded_reverse_length (records : List (List Bool)) :
    (Encoding.encodeList id records.reverse).length = (Encoding.encodeList id records).length := by
  change (ProgramEncoding.encodeRecords records.reverse).length =
    (ProgramEncoding.encodeRecords records).length
  simp [ProgramEncoding.encodeRecords_length, List.map_reverse]

theorem filterScan_eval (mode : Mode) (master F : Formula) (acc : List (List Bool)) (regs : Regs) :
    ∃ n ≤ 620 * ((encodeFormula master).length + 1) * ((encodeFormula F).length + 1),
      ∃ rf : Regs, Eval (filterScan mode) n
        (state regs [] [] (encodeFormula master) (encodeFormula F) (Encoding.encodeList id acc) [])
        (state rf [] [] (encodeFormula master) []
          (Encoding.encodeList id ((formulaRecords (filtered mode master F)).reverse ++ acc)) []) := by
  let d := state regs [] [] (encodeFormula master) (encodeFormula F) (Encoding.encodeList id acc) []
  obtain ⟨n, next, hn, hnext, hhistory, he⟩ := RecordPrograms.iterate_run_with_on
    ports (callback mode) (fun _ => false) (perClauseCost master) (invariant master)
    (SubexpNormalizeProgram.FilterEffect 14 (keep mode master)) ClausePayload
    (callback_contract mode master) (formulaRecords F) [] d (valid_formulaRecords F)
    (state_invariant _ _ _ _ _) (regs 0) (regs 1) (regs 14)
  have hout := SubexpNormalizeProgram.filterVisits_result 14 (keep mode master) hhistory acc
    (show d.stacks 14 = Encoding.encodeList id acc from rfl)
  obtain ⟨rf, source, output, payload, rfl⟩ := hnext
  have hany : (formulaRecords F).any (fun _ => false) = false := by simp
  have hout' : output = Encoding.encodeList id
      ((formulaRecords (filtered mode master F)).reverse ++ acc) := by
    change output = Encoding.encodeList id
      (((formulaRecords F).filter (keep mode master)).reverse ++ acc) at hout
    simpa only [filtered_formulaRecords] using hout
  refine ⟨n, ?_, flags rf false true false, ?_⟩
  · exact hn.trans (by simpa only [← encodeFormula_records] using filter_budget_le master (formulaRecords F))
  · simpa only [d, List.append_nil, record_state, flags_self, ← encodeFormula_records,
      hany, SubexpNormalizeProgram.unread_false, hout'] using he

theorem copyMaster_eval (regs : Regs) (source output payload : List Bool) :
    Eval copyMaster (7 * source.length + 5)
      (state regs [] [] [] source output payload)
      (state (reset regs) [] [] source source output payload) := by
  have h := ListRegisterProgram.copy_run (13 : Fin 16) 12 9 (0 : Fin 15) 1
    (by decide) (by decide) (by decide) (by decide)
    regs (state regs [] [] [] source output payload).stacks rfl
  have hs : StackRoutines.copyStacks 13 12
      (state regs [] [] [] source output payload).stacks =
      (state (reset regs) [] [] source source output payload).stacks := by
    funext i
    fin_cases i <;> simp [StackRoutines.copyStacks, state]
  rw [hs] at h
  apply Eval.call
  simpa [copyMaster, ListRegisterProgram.Run, reset, state] using h

theorem clearMaster_eval (regs : Regs) (master source output payload : List Bool) :
    Eval (clear 12) (2 * master.length + 3)
      (state regs [] [] master source output payload)
      (state (reset regs) [] [] [] source output payload) := by
  have hs : cleared 12 (state regs [] [] master source output payload) =
      state (reset regs) [] [] [] source output payload := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state, StackRoutines.clearStacks]
  have h := clear_eval 12 (state regs [] [] master source output payload)
  rw [hs] at h
  simpa [state] using h

theorem pushFalse_eval (stack : Fin 16) (d : Data) : Eval (pushFalse stack) 2 d (pushed stack d) := by
  let middle : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  have h1 : Eval (RecordPrograms.atom (.set 0 false)) 1 d middle := by
    exact .base (.atom _ _)
  have h2 : Eval (RecordPrograms.atom (.push stack 0)) 1 middle (pushed stack d) := by
    apply Eval.base
    simpa [middle, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 15) (s := 16) stack 0) middle
  exact h1.seq h2

theorem pushOutput_eval (regs : Regs) (master source output payload : List Bool) :
    Eval (pushFalse 14) 2
      (state regs [] [] master source output payload)
      (state (Function.update regs 0 false) [] [] master source (false :: output) payload) := by
  have hs : pushed 14 (state regs [] [] master source output payload) =
      state (Function.update regs 0 false) [] [] master source (false :: output) payload := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state]
  simpa only [hs] using pushFalse_eval 14 (state regs [] [] master source output payload)

theorem pushSource_eval (regs : Regs) (master source output payload : List Bool) :
    Eval (pushFalse 13) 2
      (state regs [] [] master source output payload)
      (state (Function.update regs 0 false) [] [] master (false :: source) output payload) := by
  have hs : pushed 13 (state regs [] [] master source output payload) =
      state (Function.update regs 0 false) [] [] master (false :: source) output payload := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state]
  simpa only [hs] using pushFalse_eval 13 (state regs [] [] master source output payload)

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseSelfFilterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Complete fixed-master clause filtering

This wrapper performs the actual initial copy, record scan, cleanup, and
record-order restoration. Its input and output are on stack 13; every other
stack is empty at both boundaries.
-/

namespace SubexponentialSAT.ExecClauseFiltersProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)


/-- A complete finite-program execution; the master copy and all temporary
records have been consumed when the ordered output is returned. -/
theorem selfFilter_eval (mode : Mode) (F : Formula) (regs : Regs) :
    ∃ n ≤ 999 * ((encodeFormula F).length + 1) ^ 2, ∃ rf : Regs,
      Eval (selfFilter mode) n
        (state regs [] [] [] (encodeFormula F) [] [])
        (state rf [] [] [] (encodeFormula (filtered mode F F)) [] []) := by
  let firstRegs := Function.update (reset regs) 0 false
  obtain ⟨n, hn, rf, hscan⟩ := filterScan_eval mode F F [] firstRegs
  simp only [List.append_nil] at hscan
  let finalRegs := Function.update (reset rf) 0 false
  obtain ⟨m, hm, hreverse⟩ := ExecClauseFilterReverse.reverse_eval
    (formulaRecords (filtered mode F F)).reverse [] finalRegs
  change Eval ExecClauseFilterReverse.command m
    (state finalRegs [] [] [] (Encoding.encodeList id [])
      (Encoding.encodeList id (formulaRecords (filtered mode F F)).reverse) [])
    (state (flags finalRegs false true false) [] [] []
      (Encoding.encodeList id ((formulaRecords (filtered mode F F)).reverse.reverse ++ [])) [] [])
    at hreverse
  simp only [List.reverse_reverse, List.append_nil, ← encodeFormula_records] at hreverse
  rw [encoded_reverse_length, ← encodeFormula_records] at hm
  have hlength := filtered_length_le mode F F
  have hfull := (copyMaster_eval regs (encodeFormula F) [] []).seq
    ((pushOutput_eval (reset regs) (encodeFormula F) (encodeFormula F) [] []).seq
      (hscan.seq ((clearMaster_eval rf (encodeFormula F) []
        (Encoding.encodeList id (formulaRecords (filtered mode F F)).reverse) []).seq
        ((pushSource_eval (reset rf) [] []
          (Encoding.encodeList id (formulaRecords (filtered mode F F)).reverse) []).seq hreverse))))
  refine ⟨_, ?_, flags finalRegs false true false, hfull⟩
  nlinarith

theorem state_ready (regs : Regs) (source : List Bool) :
    Ready (state regs [] [] [] source [] []) := by
  intro i hi
  fin_cases i <;> simp_all [state]

theorem ready_eq_state (d : Data) (hready : Ready d) :
    d = state d.regs [] [] [] (d.stacks 13) [] [] := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  by_cases hi : i = 13
  · subst i
    rfl
  · rw [hready i hi]
    fin_cases i <;> simp_all []

/-- The concrete in-place filter returns exactly the selected ordered list,
with no hidden callback or external execution premise. -/
theorem selfFilter_runsIn (mode : Mode) (F : Formula) (d : Data)
    (hsource : d.stacks 13 = encodeFormula F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = encodeFormula (filtered mode F F) ∧
      RunsIn (selfFilterProgram mode) (1000 * ((encodeFormula F).length + 1) ^ 2)
        (d.withPC (some (selfFilterProgram mode).entry)) (e.withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := selfFilter_eval mode F d.regs
  have hd : d = state d.regs [] [] [] (encodeFormula F) [] [] := by
    simpa only [hsource] using ready_eq_state d hready
  refine ⟨state rf [] [] [] (encodeFormula (filtered mode F F)) [] [],
    state_ready _ _, rfl, n + 1, ?_, ?_⟩
  · have hpos : 0 < ((encodeFormula F).length + 1) ^ 2 := pow_pos (by omega) _
    omega
  · have ht := compiled_halt_trace he 13 13
    change Trace (selfFilterProgram mode) (n + 1)
      ((state d.regs [] [] [] (encodeFormula F) [] []).withPC
        (some (selfFilterProgram mode).entry)) _ at ht
    simpa only [← hd] using ht

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Fixed-control encoded CNF normalization

The common boundary uses stack 13 for the formula and empty work stacks.
Literal cleanup and tautology removal are lifted into that boundary here;
clause deduplication and strict-subset deletion use the same boundary.
-/

namespace SubexponentialSAT.SubexpNormalizationProgram

open BitProgram StructuredCalls

theorem clauseCode_fields (C : List ℕ) :
    ExecClauseRelationScan.encodeClause (C.map Encoding.encodeNat) =
      ExecCleanLiteralsProgram.clauseCode C := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    simpa [ExecClauseRelationScan.encodeClause, ExecCleanLiteralsProgram.clauseCode,
      Encoding.encodeList] using ih

theorem formulaCode_fields (F : List (List ℕ)) :
    ExecClauseRelationScan.encodeFormula (bitFields F) = formulaCode F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    simpa [ExecClauseRelationScan.encodeFormula, bitFields, formulaCode,
      ExecCleanLiteralsProgram.formulaCode, Encoding.encodeList, clauseCode_fields] using ih

theorem filtered_fields (F : List (List ℕ)) :
    ExecClauseFiltersProgram.filtered .strictSubset (bitFields F) (bitFields F) =
      bitFields (removeSupersets F) := by
  simp only [ExecClauseFiltersProgram.filtered, bitFields, removeSupersets,
    List.filter_map, List.any_map, Function.comp_def, ExecClauseRelationScan.test,
    ExecCNFCodeTransport.strictSubset_map Encoding.encodeNat Encoding.encodeNat_injective]

theorem removeSupersetsCall_eval_oai (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 1000 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval removeSupersetsCall n d e ∧ Ready e ∧
      e.stacks 13 = formulaCode (removeSupersets F) := by
  have hs : d.stacks 13 = ExecClauseRelationScan.encodeFormula (bitFields F) := by
    simpa only [formulaCode_fields] using hsource
  obtain ⟨e, he, hout, n, hn, ht⟩ :=
    ExecClauseFiltersProgram.selfFilter_runsIn .strictSubset (bitFields F) d hs hready
  rw [filtered_fields, formulaCode_fields] at hout
  rw [formulaCode_fields] at hn
  exact ⟨n, hn, e, .call _ ht, he, hout⟩

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval_oai := @OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval_oai
