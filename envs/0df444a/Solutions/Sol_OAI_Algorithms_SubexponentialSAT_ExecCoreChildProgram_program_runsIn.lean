-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:14:18.735785+00:00
-- url     : https://prove2.me/submissions/9868056b-711f-49c6-abb1-f9083ad7e434

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S079
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S111
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_ExecClauseFiltersProgram_scan_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpNormalizationProgram_absorb_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving encoded clause relations

Two invocations of the concrete subset tester compute equivalence and strict
inclusion. The original encoded clauses occupy stacks 8 and 9 throughout;
stacks 0 through 7 are empty workspace at both boundaries. Registers 10 and
11 return equivalence and strict inclusion, respectively.
-/

namespace SubexponentialSAT.ExecClauseRelationsProgram

open BitProgram StructuredCalls

theorem encodeList_id_map {α : Type*} (enc : α → List Bool) (xs : List α) :
    Encoding.encodeList id (xs.map enc) = Encoding.encodeList enc xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList, ih]

theorem contains_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (x : α) (xs : List α) :
    ExecCNF.contains (f x) (xs.map f) = ExecCNF.contains x xs := by
  apply Bool.eq_iff_iff.mpr
  simp only [ExecCNF.contains_true, List.mem_map]
  constructor
  · rintro ⟨a, ha, heq⟩
    exact hf heq ▸ ha
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem subset_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (source target : List α) :
    ExecCNF.subset (source.map f) (target.map f) = ExecCNF.subset source target := by
  induction source with
  | nil => rfl
  | cons x xs ih => simp [ExecCNF.subset, contains_map_injective f hf, ih]

theorem equivalent_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (source target : List α) :
    ExecCNF.equivalent (source.map f) (target.map f) = ExecCNF.equivalent source target := by
  simp [ExecCNF.equivalent, subset_map_injective f hf]

theorem strictSubset_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (source target : List α) :
    ExecCNF.strictSubset (source.map f) (target.map f) = ExecCNF.strictSubset source target := by
  simp [ExecCNF.strictSubset, subset_map_injective f hf]

end SubexponentialSAT.ExecClauseRelationsProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScanEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact natural-code interfaces for the fixed encoded relation scanner. -/
namespace SubexponentialSAT.ExecClauseRelationScan
open BitProgram StructuredCalls

theorem test_codes (mode : Mode) (C Q : List ℕ) :
    test mode (codeClause C) (codeClause Q) = codeTest mode C Q := by
  cases mode <;>
    simp only [test, codeTest, codeClause,
      ExecClauseRelationsProgram.equivalent_map_injective Encoding.encodeNat
        Encoding.encodeNat_injective,
      ExecClauseRelationsProgram.strictSubset_map_injective Encoding.encodeNat
        Encoding.encodeNat_injective,
      ExecClauseRelationsProgram.subset_map_injective Encoding.encodeNat
        Encoding.encodeNat_injective]

theorem encodeClause_codes (C : List ℕ) :
    encodeClause (codeClause C) = Encoding.encodeList Encoding.encodeNat C :=
  ExecClauseRelationsProgram.encodeList_id_map _ _

theorem encodeFormula_codes (F : List (List ℕ)) :
    encodeFormula (codeFormula F) =
      Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    simp only [encodeFormula, codeFormula, List.map_cons, Encoding.encodeList,
      encodeClause_codes]
    exact congrArg (fun tail => true :: Encoding.frame
      (Encoding.encodeList Encoding.encodeNat C) ++ tail) ih

end SubexponentialSAT.ExecClauseRelationScan

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


theorem state_ready (regs : Regs) (source : List Bool) :
    Ready (state regs [] [] [] source [] []) := by
  intro i hi
  fin_cases i <;> simp_all [state]

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCoreChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded construction of the core child

The caller supplies a forward encoded core clause on stack 9, an encoded
selected family on stack 12, and the parent formula on stack 13. All other
stacks are empty. The program builds the core record, removes every clause
equivalent to a selected clause, restores record order, and calls the concrete
absorber. The result is on stack 13; every other stack is empty.

The finite program does not depend on any of its three input values. The
equivalence tests, framing, reversal, and absorption are actual bit programs.
-/

namespace SubexponentialSAT.ExecCoreChildProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram


/-- Construct a singleton encoded list by moving and escaping the actual
core payload. Neither the payload nor its length appears in finite control. -/
theorem seedCore_eval (regs : Regs) (bits master source : List Bool) :
    Eval seedCore (8 * bits.length + 18)
      (state regs bits [] master source [] [])
      (state (seedRegs regs) [] [] master source
        (Encoding.encodeList id [bits]) []) := by
  let r := Function.update (reset regs) 0 false
  have hset : Eval (.base (.atom (.set 14 true))) 1
      (state r [] [] master source [false] bits.reverse)
      (state (Function.update r 14 true) [] [] master source [false] bits.reverse) :=
    .base (.atom _ _)
  have hemit := emit_eval (Function.update r 14 true) bits master source [false]
  simp only [Function.update_self, ite_true, if_true] at hemit
  have hfull := (transfer_from_query regs bits master source []).seq
    ((pushOutput_eval (reset regs) master source [] bits.reverse).seq (hset.seq hemit))
  have hcost : 3 * bits.length + 3 + (2 + (1 + (5 * bits.length + 11 + 1))) =
      8 * bits.length + 18 := by omega
  simpa only [seedCore, seedRegs, r, SubexpNormalizeProgram.emitIfSelectedSteps,
    ite_true, if_true, Encoding.encodeList, id_eq, hcost] using hfull

theorem prepare_eval (master F : Formula) (H : Clause) (regs : Regs) :
    ∃ n ≤ 999 * (volume master F H) ^ 2, ∃ rf : Regs,
      Eval prepare n
        (state regs (encodeClause H) [] (encodeFormula master) (encodeFormula F) [] [])
        (state rf [] [] [] (encodeFormula (H :: filtered .equivalent master F)) [] []) := by
  obtain ⟨n, hn, rf, hscan⟩ := filterScan_eval .equivalent master F [encodeClause H]
    (seedRegs regs)
  let finalRegs := Function.update (reset rf) 0 false
  let records := (formulaRecords (filtered .equivalent master F)).reverse ++ [encodeClause H]
  obtain ⟨m, hm, hreverse⟩ := ExecClauseFilterReverse.reverse_eval records [] finalRegs
  have hrecords : records.reverse ++ [] =
      formulaRecords (H :: filtered .equivalent master F) := by
    simp [records, formulaRecords]
  change Eval ExecClauseFilterReverse.command m
    (state finalRegs [] [] [] (Encoding.encodeList id []) (Encoding.encodeList id records) [])
    (state (flags finalRegs false true false) [] [] []
      (Encoding.encodeList id (records.reverse ++ [])) [] []) at hreverse
  rw [hrecords, ← encodeFormula_records] at hreverse
  have hrecordLength : (Encoding.encodeList id records).length =
      (encodeFormula (H :: filtered .equivalent master F)).length := by
    have h := congrArg (fun xs => (Encoding.encodeList id xs).length) hrecords
    simpa only [List.append_nil, encoded_reverse_length, ← encodeFormula_records] using h
  rw [hrecordLength] at hm
  have hlength := filtered_length_le .equivalent master F
  have hfull := (seedCore_eval regs (encodeClause H) (encodeFormula master) (encodeFormula F)).seq
    (hscan.seq ((clearMaster_eval rf (encodeFormula master) [] (Encoding.encodeList id records) []).seq
      ((pushSource_eval (reset rf) [] [] (Encoding.encodeList id records) []).seq hreverse)))
  refine ⟨_, ?_, flags finalRegs false true false, hfull⟩
  simp only [encodeFormula, Encoding.length_encodeList_cons] at hm
  change m ≤ 10 * (2 * (encodeClause H).length + 2 +
    (encodeFormula (filtered .equivalent master F)).length) at hm
  dsimp [volume]
  nlinarith

theorem filtered_codes (selected F : List (List ℕ)) :
    filtered .equivalent (ExecClauseRelationScan.codeFormula selected)
      (ExecClauseRelationScan.codeFormula F) =
      ExecClauseRelationScan.codeFormula (ExecCNF.eraseClauses F selected) := by
  simp only [filtered, ExecClauseRelationScan.codeFormula, List.filter_map,
    List.any_map, Function.comp_def, ExecClauseRelationScan.test_codes,
    ExecClauseRelationScan.codeTest, ExecCNF.eraseClauses]
  congr 1
  apply congrArg (fun p : List ℕ → Bool => F.filter p)
  funext C
  apply congrArg Bool.not
  apply congrArg (fun p : List ℕ → Bool => selected.any p)
  funext D
  exact Bool.and_comm _ _

theorem prepare_codes_eval (F selected : List (List ℕ)) (H : List ℕ) (regs : Regs) :
    ∃ n ≤ 999 * (inputVolume F selected H) ^ 2, ∃ rf : Regs,
      Eval prepare n
        (state regs (clauseCode H) [] (formulaCode selected) (formulaCode F) [] [])
        (state rf [] [] [] (formulaCode (H :: ExecCNF.eraseClauses F selected)) [] []) := by
  obtain ⟨n, hn, rf, he⟩ := prepare_eval (ExecClauseRelationScan.codeFormula selected)
    (ExecClauseRelationScan.codeFormula F) (ExecClauseRelationScan.codeClause H) regs
  rw [filtered_codes] at he
  change Eval prepare n _ (state rf [] [] []
    (encodeFormula (ExecClauseRelationScan.codeFormula
      (H :: ExecCNF.eraseClauses F selected))) [] []) at he
  refine ⟨n, ?_, rf, ?_⟩
  · change n ≤ 999 * ((Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) selected).length +
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F).length +
        2 * (Encoding.encodeList Encoding.encodeNat H).length + 3) ^ 2
    simpa only [volume, ExecClauseRelationScan.encodeFormula_codes,
      ExecClauseRelationScan.encodeClause_codes] using hn
  · change Eval prepare n
      (state regs (Encoding.encodeList Encoding.encodeNat H) []
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) selected)
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F) [] [])
      (state rf [] [] []
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
          (H :: ExecCNF.eraseClauses F selected)) [] [])
    simpa only [ExecClauseRelationScan.encodeFormula_codes,
      ExecClauseRelationScan.encodeClause_codes] using he

theorem prepared_length_le (F selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (H :: ExecCNF.eraseClauses F selected)).length + 1 ≤
      inputVolume F selected H := by
  have h := Encoding.length_encodeList_filter_le clauseCode
    (fun C => !(selected.any fun D => ExecCNF.equivalent C D)) F
  change (formulaCode (ExecCNF.eraseClauses F selected)).length ≤ (formulaCode F).length at h
  change (Encoding.encodeList clauseCode (H :: ExecCNF.eraseClauses F selected)).length + 1 ≤ _
  rw [Encoding.length_encodeList_cons]
  change 2 * (clauseCode H).length + 2 +
    (formulaCode (ExecCNF.eraseClauses F selected)).length + 1 ≤ _
  unfold inputVolume
  omega

theorem inputReady_eq_state (d : Data) (hready : InputReady d) :
    d = state d.regs (d.stacks 9) [] (d.stacks 12) (d.stacks 13) [] [] := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  by_cases h9 : i = 9
  · subst i; rfl
  by_cases h12 : i = 12
  · subst i; rfl
  by_cases h13 : i = 13
  · subst i; rfl
  rw [hready i h9 h12 h13]
  fin_cases i <;> simp_all []

/-- The complete source execution has no assumed semantic callback. It
consumes the core and selected family, returning the exact absorbed child. -/
theorem command_eval (F selected : List (List ℕ)) (H : List ℕ) (d : Data)
    (hcore : d.stacks 9 = clauseCode H) (hselected : d.stacks 12 = formulaCode selected)
    (hsource : d.stacks 13 = formulaCode F) (hready : InputReady d) :
    ∃ n ≤ 3200 * (inputVolume F selected H) ^ 2, ∃ e : Data,
      Eval command n d e ∧ SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = formulaCode (result F selected H) := by
  have hd : d = state d.regs (clauseCode H) [] (formulaCode selected) (formulaCode F) [] [] := by
    simpa only [hcore, hselected, hsource] using inputReady_eq_state d hready
  obtain ⟨n, hn, rf, hprep⟩ := prepare_codes_eval F selected H d.regs
  let a := state rf [] [] [] (formulaCode (H :: ExecCNF.eraseClauses F selected)) [] []
  obtain ⟨m, hm, e, habsorb, he, hout⟩ :=
    SubexpNormalizationProgram.absorb_eval (H :: ExecCNF.eraseClauses F selected)
      a rfl (state_ready _ _)
  have hm' : m ≤ 2200 * (inputVolume F selected H) ^ 2 :=
    hm.trans (Nat.mul_le_mul_left 2200 (Nat.pow_le_pow_left (prepared_length_le F selected H) 2))
  refine ⟨n + m, by omega, e, ?_, he, hout⟩
  rw [hd]
  exact hprep.seq habsorb

/-- Fixed finite code, with its final halt charged to the same quadratic
bound in the lengths of the three actual encoded inputs. -/
theorem program_runsIn_oai (F selected : List (List ℕ)) (H : List ℕ) (d : Data)
    (hcore : d.stacks 9 = clauseCode H) (hselected : d.stacks 12 = formulaCode selected)
    (hsource : d.stacks 13 = formulaCode F) (hready : InputReady d) :
    ∃ e : Data, SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = formulaCode (result F selected H) ∧
      RunsIn program (3300 * (inputVolume F selected H) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hr, ho⟩ := command_eval F selected H d hcore hselected hsource hready
  refine ⟨e, hr, ho, n + 1, ?_, compiled_halt_trace he 13 13⟩
  have hv : 0 < inputVolume F selected H := by unfold inputVolume; omega
  have hp := pow_pos hv 2
  omega

end SubexponentialSAT.ExecCoreChildProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn_oai
