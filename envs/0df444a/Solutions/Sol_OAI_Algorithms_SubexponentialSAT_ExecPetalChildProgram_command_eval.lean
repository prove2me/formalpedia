-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:15:47.363645+00:00
-- url     : https://prove2.me/submissions/79d95e0c-747f-4369-b99d-6c25d6d113d8

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S079
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S111
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_ExecClauseFiltersProgram_scan_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_ExecPetalChildProgram_familyCall_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpNormalizationProgram_absorb_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFCodeTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact list transport through literal codes

These equalities preserve clause order and the last-occurrence conventions.
They connect the encoded normalization programs to the typed executable CNF
operations, rather than identifying only their finite-set semantics.
-/

namespace SubexponentialSAT.ExecCNFCodeTransport

open ExecCNF

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
private theorem filter_map_comm (f : α → β) (p : α → Bool) (q : β → Bool)
    (h : ∀ x, q (f x) = p x) (L : List α) :
    (L.map f).filter q = (L.filter p).map f := by
  induction L with
  | nil => rfl
  | cons x xs ih => cases hx : p x <;> simp [ h, hx, ih]

@[simp] theorem removeTautologies_map (f : α → β) (hf : Function.Injective f)
    (negα : α → α) (negβ : β → β) (hn : ∀ x, f (negα x) = negβ (f x))
    (F : Formula α) : removeTautologies negβ (F.map (List.map f)) =
      (removeTautologies negα F).map (List.map f) := by
  apply filter_map_comm (List.map f)
  intro C
  simp only [tautology_map f hf negα negβ hn]

@[simp] theorem absorb_map (f : α → β) (hf : Function.Injective f)
    (F : Formula α) : absorb (F.map (List.map f)) = (absorb F).map (List.map f) := by
  unfold absorb
  rw [dedupClauses_map f hf]
  apply filter_map_comm (List.map f)
  intro C
  simp only [List.any_map, Function.comp_def, strictSubset_map f hf]

@[simp] theorem normalize_map (f : α → β) (hf : Function.Injective f)
    (negα : α → α) (negβ : β → β) (hn : ∀ x, f (negα x) = negβ (f x))
    (F : Formula α) : ExecCNF.normalize negβ (F.map (List.map f)) =
      (ExecCNF.normalize negα F).map (List.map f) := by
  simp only [ExecCNF.normalize, cleanLiterals_map f hf,
    removeTautologies_map f hf negα negβ hn, absorb_map f hf]

@[simp] theorem eraseClauses_map (f : α → β) (hf : Function.Injective f)
    (F S : Formula α) : eraseClauses (F.map (List.map f)) (S.map (List.map f)) =
      (eraseClauses F S).map (List.map f) := by
  apply filter_map_comm (List.map f)
  intro C
  simp only [List.any_map, Function.comp_def, equivalent_map f hf]

/-- The actual petal filter commutes with injective literal encoding. -/
theorem petal_filter_map (f : α → β) (hf : Function.Injective f)
    (C H : Clause α) :
    (C.map f).filter (fun x => !decide (x ∈ H.map f)) =
      (C.filter (fun x => !decide (x ∈ H))).map f := by
  apply filter_map_comm f
  intro x
  simp [List.mem_map, hf.eq_iff]

theorem petal_family_map (f : α → β) (hf : Function.Injective f)
    (G : Formula α) (H : Clause α) :
    (G.map (List.map f)).map (fun C => C.filter (fun x => !decide (x ∈ H.map f))) =
      (G.map (fun C => C.filter (fun x => !decide (x ∈ H)))).map (List.map f) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro C _
  exact petal_filter_map f hf C H

end SubexponentialSAT.ExecCNFCodeTransport

end OAI.Algorithms
end

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

end SubexponentialSAT.SubexpNormalizationProgram

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


theorem encoded_append_length_le (xs ys : List (List Bool)) :
    (Encoding.encodeList id (xs ++ ys)).length ≤
      (Encoding.encodeList id xs).length + (Encoding.encodeList id ys).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, Encoding.length_encodeList_cons]
    omega

/-- This shared erasure block accepts any genuine encoded record accumulator.
Its bound counts the accumulator bits, even if none of the parent clauses is
retained. Every payload, including an empty payload, is copied by real loops. -/
theorem eraseWithAccumulator_eval (master F : Formula) (acc : List (List Bool)) (regs : Regs) :
    ∃ n ≤ 999 * ((encodeFormula master).length + (encodeFormula F).length +
        (Encoding.encodeList id acc).length + 1) ^ 2, ∃ rf : Regs,
      Eval eraseWithAccumulator n
        (state regs [] [] (encodeFormula master) (encodeFormula F)
          (Encoding.encodeList id acc) [])
        (state rf [] [] [] (Encoding.encodeList id
          (acc.reverse ++ formulaRecords (filtered .equivalent master F))) [] []) := by
  obtain ⟨n, hn, rf, hscan⟩ := filterScan_eval .equivalent master F acc regs
  let finalRegs := Function.update (reset rf) 0 false
  let records := (formulaRecords (filtered .equivalent master F)).reverse ++ acc
  obtain ⟨m, hm, hreverse⟩ := ExecClauseFilterReverse.reverse_eval records [] finalRegs
  change Eval ExecClauseFilterReverse.command m
    (state finalRegs [] [] [] (Encoding.encodeList id []) (Encoding.encodeList id records) [])
    (state (flags finalRegs false true false) [] [] []
      (Encoding.encodeList id (records.reverse ++ [])) [] []) at hreverse
  have hrecords : records.reverse ++ [] =
      acc.reverse ++ formulaRecords (filtered .equivalent master F) := by
    simp [records]
  rw [hrecords] at hreverse
  have hlength : (Encoding.encodeList id records).length ≤
      (encodeFormula F).length + (Encoding.encodeList id acc).length := by
    calc
      _ ≤ (Encoding.encodeList id (formulaRecords (filtered .equivalent master F)).reverse).length +
          (Encoding.encodeList id acc).length := encoded_append_length_le _ _
      _ = (encodeFormula (filtered .equivalent master F)).length +
          (Encoding.encodeList id acc).length := by rw [encoded_reverse_length, ← encodeFormula_records]
      _ ≤ _ := Nat.add_le_add_right (filtered_length_le .equivalent master F) _
  have hfull := hscan.seq
    ((clearMaster_eval rf (encodeFormula master) [] (Encoding.encodeList id records) []).seq
      ((pushSource_eval (reset rf) [] [] (Encoding.encodeList id records) []).seq hreverse))
  refine ⟨_, ?_, flags finalRegs false true false, hfull⟩
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

end SubexponentialSAT.ExecCoreChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual stable subtraction of a core from an encoded clause. Membership
tests, core copies, record emission, and order restoration use finite code. -/
namespace SubexponentialSAT.ExecPetalProgram
open BitProgram StructuredCalls

theorem result_encoded_length_le {α : Type*} [DecidableEq α]
    (enc : α → List Bool) (C H : List α) :
    (Encoding.encodeList enc (result C H)).length ≤ (Encoding.encodeList enc C).length :=
  Encoding.length_encodeList_filter_le enc _ C

end SubexponentialSAT.ExecPetalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual construction of the petal child. The core, selected family, and
parent occupy the same three ports as the core-child program. -/
namespace SubexponentialSAT.ExecPetalChildProgram
open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram

theorem copySelected_eval (regs : Regs) (core selected parent : List Bool) :
    Eval copySelected (7 * selected.length + 5)
      (frame regs [] core selected parent [])
      (frame (readRegs regs 0 1 none) selected core selected parent []) := by
  have h := ListRegisterProgram.copy_run (r := 15) (s := 16) 12 0 10 0 1
    (by decide) (by decide) (by decide) (by decide) regs
    (frame regs [] core selected parent []).stacks rfl
  have hs : StackRoutines.copyStacks 12 0 (frame regs [] core selected parent []).stacks =
      (frame (readRegs regs 0 1 none) selected core selected parent []).stacks := by
    funext i
    fin_cases i <;> simp [frame, StackRoutines.copyStacks]
  rw [show (frame regs [] core selected parent []).stacks 12 = selected by rfl] at h
  rw [hs] at h
  exact Eval.call _ (by
    simpa only [ListRegisterProgram.Run, StructuredProgram.State.withPC, frame] using h)

theorem clearCore_eval (regs : Regs) (core selected parent output : List Bool) :
    Eval (clear 9) (2 * core.length + 3)
      (state regs core [] selected parent output [])
      (state (reset regs) [] [] selected parent output []) := by
  have h := clear_eval 9 (state regs core [] selected parent output [])
  have heq : cleared 9 (state regs core [] selected parent output []) =
      state (reset regs) [] [] selected parent output [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [state, StackRoutines.clearStacks]
  change Eval (clear 9) (2 * core.length + 3)
    (state regs core [] selected parent output []) _ at h
  rw [heq] at h
  exact h

theorem petals_length_le (selected : Formula) (H : Clause) :
    (encodeFormula (petals selected H)).length ≤ (encodeFormula selected).length := by
  induction selected with
  | nil => exact le_rfl
  | cons C F ih =>
    have hc := ExecPetalProgram.result_encoded_length_le id C H
    change (encodeClause (ExecPetalProgram.result C H)).length ≤ (encodeClause C).length at hc
    simp only [petals, List.map_cons, encodeFormula, Encoding.length_encodeList_cons] at ih ⊢
    omega

theorem prepare_eval (F selected : Formula) (H : Clause) (regs : Regs) :
    ∃ n ≤ 6000 * (volume F selected H)^2, ∃ rf : Regs,
      Eval prepare n (state regs (encodeClause H) [] (encodeFormula selected) (encodeFormula F) [] [])
        (state rf [] [] []
          (encodeFormula (petals selected H ++ filtered .equivalent selected F)) [] []) := by
  obtain ⟨n, hn, rf, hf⟩ := familyCall_eval selected H (readRegs regs 0 1 none)
    (encodeFormula selected) (encodeFormula F)
  let acc := (formulaRecords (petals selected H)).reverse
  obtain ⟨m, hm, final, he⟩ := ExecCoreChildProgram.eraseWithAccumulator_eval
    selected F acc (reset rf)
  have hresult : acc.reverse ++ formulaRecords (filtered .equivalent selected F) =
      formulaRecords (petals selected H ++ filtered .equivalent selected F) := by
    simp [acc, formulaRecords]
  rw [hresult, ← encodeFormula_records] at he
  have hacc : (Encoding.encodeList id acc).length = (encodeFormula (petals selected H)).length := by
    simp only [acc, encoded_reverse_length, ← encodeFormula_records]
  have hp := petals_length_le selected H
  have hvolume : (encodeFormula selected).length + (encodeFormula F).length +
      (Encoding.encodeList id acc).length + 1 ≤ 2 * volume F selected H := by
    rw [hacc]
    dsimp [volume]
    omega
  have hm' : m ≤ 3996 * (volume F selected H)^2 := by
    apply hm.trans
    calc
      _ ≤ 999 * (2 * volume F selected H)^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hvolume 2)
      _ = _ := by ring
  refine ⟨(7 * (encodeFormula selected).length + 5) +
    (n + ((2 * (encodeClause H).length + 3) + m)), ?_, final, ?_⟩
  · dsimp [volume] at *
    nlinarith
  · exact (copySelected_eval regs (encodeClause H) (encodeFormula selected) (encodeFormula F)).seq
      (hf.seq ((clearCore_eval rf (encodeClause H) (encodeFormula selected)
        (encodeFormula F) (Encoding.encodeList id acc)).seq he))

theorem formulaCode_encoding (F : List (List ℕ)) :
    formulaCode F = Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F := by
  rw [← ExecClauseRelationScan.encodeFormula_codes]
  exact (SubexpNormalizationProgram.formulaCode_fields F).symm

theorem petals_codes (selected : List (List ℕ)) (H : List ℕ) :
    petals (ExecClauseRelationScan.codeFormula selected) (ExecClauseRelationScan.codeClause H) =
      ExecClauseRelationScan.codeFormula (petals selected H) := by
  simpa [petals, ExecPetalProgram.result, ExecClauseRelationScan.codeFormula,
    ExecClauseRelationScan.codeClause] using
    ExecCNFCodeTransport.petal_family_map Encoding.encodeNat Encoding.encodeNat_injective selected H

theorem prepare_codes_eval (F selected : List (List ℕ)) (H : List ℕ) (regs : Regs) :
    ∃ n ≤ 6000 * (inputVolume F selected H)^2, ∃ rf : Regs,
      Eval prepare n (state regs (clauseCode H) [] (formulaCode selected) (formulaCode F) [] [])
        (state rf [] [] [] (formulaCode (petals selected H ++ ExecCNF.eraseClauses F selected)) [] []) := by
  obtain ⟨n, hn, rf, he⟩ := prepare_eval (ExecClauseRelationScan.codeFormula F)
    (ExecClauseRelationScan.codeFormula selected) (ExecClauseRelationScan.codeClause H) regs
  rw [petals_codes, ExecCoreChildProgram.filtered_codes] at he
  have happend : ExecClauseRelationScan.codeFormula (petals selected H) ++
      ExecClauseRelationScan.codeFormula (ExecCNF.eraseClauses F selected) =
      ExecClauseRelationScan.codeFormula (petals selected H ++ ExecCNF.eraseClauses F selected) := by
    simp [ExecClauseRelationScan.codeFormula]
  rw [happend] at he
  refine ⟨n, ?_, rf, ?_⟩
  · simpa [volume, inputVolume, formulaCode_encoding, clauseCode,
      ExecCleanLiteralsProgram.clauseCode,
      ExecClauseRelationScan.encodeFormula_codes,
      ExecClauseRelationScan.encodeClause_codes] using hn
  · simpa only [formulaCode_encoding, ExecCleanLiteralsProgram.clauseCode,
      ExecClauseRelationScan.encodeFormula_codes,
      ExecClauseRelationScan.encodeClause_codes] using he

theorem encode_append_length_le {α : Type*} (enc : α → List Bool) (xs ys : List α) :
    (Encoding.encodeList enc (xs ++ ys)).length ≤
      (Encoding.encodeList enc xs).length + (Encoding.encodeList enc ys).length := by
  induction xs with
  | nil => simp [Encoding.encodeList]
  | cons x xs ih =>
    simp only [List.cons_append, Encoding.length_encodeList_cons]
    omega

theorem petals_code_length_le (selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (petals selected H)).length ≤ (formulaCode selected).length := by
  have h := petals_length_le (ExecClauseRelationScan.codeFormula selected)
    (ExecClauseRelationScan.codeClause H)
  simpa only [formulaCode_encoding, petals_codes,
    ExecClauseRelationScan.encodeFormula_codes] using h

theorem prepared_length_le (F selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (petals selected H ++ ExecCNF.eraseClauses F selected)).length + 1 ≤
      inputVolume F selected H := by
  have hp := petals_code_length_le selected H
  have he := Encoding.length_encodeList_filter_le clauseCode
    (fun C => !(selected.any fun D => ExecCNF.equivalent C D)) F
  change (formulaCode (ExecCNF.eraseClauses F selected)).length ≤ (formulaCode F).length at he
  have ha := encode_append_length_le clauseCode (petals selected H) (ExecCNF.eraseClauses F selected)
  change (formulaCode (petals selected H ++ ExecCNF.eraseClauses F selected)).length ≤
    (formulaCode (petals selected H)).length + (formulaCode (ExecCNF.eraseClauses F selected)).length at ha
  unfold inputVolume
  omega

theorem command_eval_oai (F selected : List (List ℕ)) (H : List ℕ) (d : Data)
    (hcore : d.stacks 9 = clauseCode H) (hselected : d.stacks 12 = formulaCode selected)
    (hsource : d.stacks 13 = formulaCode F) (hready : InputReady d) :
    ∃ n ≤ 19000 * (inputVolume F selected H)^2, ∃ e : Data,
      Eval command n d e ∧ SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = formulaCode (result F selected H) := by
  have hd : d = state d.regs (clauseCode H) [] (formulaCode selected) (formulaCode F) [] [] := by
    simpa only [hcore, hselected, hsource] using ExecCoreChildProgram.inputReady_eq_state d hready
  obtain ⟨n, hn, rf, hp⟩ := prepare_codes_eval F selected H d.regs
  let a := state rf [] [] [] (formulaCode (petals selected H ++ ExecCNF.eraseClauses F selected)) [] []
  obtain ⟨m, hm, e, he, hr, ho⟩ := SubexpNormalizationProgram.absorb_eval
    (petals selected H ++ ExecCNF.eraseClauses F selected) a rfl (ExecClauseFiltersProgram.state_ready _ _)
  have hm' : m ≤ 2200 * (inputVolume F selected H)^2 :=
    hm.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (prepared_length_le F selected H) 2))
  refine ⟨n + m, by omega, e, ?_, hr, ho⟩
  rw [hd]
  exact hp.seq he

end SubexponentialSAT.ExecPetalChildProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval_oai
