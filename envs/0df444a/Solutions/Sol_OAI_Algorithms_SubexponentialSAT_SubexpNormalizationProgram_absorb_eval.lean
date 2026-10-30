-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.absorb_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:38:24.444198+00:00
-- url     : https://prove2.me/submissions/2394e55d-da07-4d8d-8ffe-b11eb746caf8

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S111
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_ExecClauseFiltersProgram_scan_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpNormalizationProgram_removeSupersetsCall_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSemanticHelpers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact list identities used when composing executable CNF filters. -/

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

theorem any_strictSubset_dedupClauses (F : Formula α) (C : Clause α) :
    (dedupClauses F).any (fun D => strictSubset D C) =
      F.any (fun D => strictSubset D C) := by
  apply Bool.eq_iff_iff.mpr
  simp only [any_strictSubset_true, formulaSet_dedupClauses]

/-- An implementation may first remove duplicate clauses, then use that same
list as the scan master, without changing the exact ordered output of absorb. -/
theorem absorb_eq_filter_dedup (F : Formula α) :
    absorb F = (dedupClauses F).filter
      (fun C => !((dedupClauses F).any (fun D => strictSubset D C))) := by
  simp only [absorb, any_strictSubset_dedupClauses]

/-- Clause deduplication retains a subsequence of the original payloads. -/
theorem length_encodeList_dedupClauses_le (enc : Clause α → List Bool) (F : Formula α) :
    (Encoding.encodeList enc (dedupClauses F)).length ≤
      (Encoding.encodeList enc F).length := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    by_cases h : F.any (fun D => equivalent C D) = true
    · simp [dedupClauses, h, Encoding.length_encodeList_cons] ; omega
    · simp [dedupClauses, h, Encoding.length_encodeList_cons] ; omega

end SubexponentialSAT.ExecCNF

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecLiteralDedupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual stable literal deduplication

The fixed program tests each record against the remaining records, retains its
last occurrence, and restores record order. All membership, copy, emission,
and reversal calls are concrete finite programs with measured executions.
-/

namespace SubexponentialSAT.ExecLiteralDedupProgram

open BitProgram StructuredCalls

theorem encoded_reverse_length (records : List (List Bool)) :
    (Encoding.encodeList id records.reverse).length = (Encoding.encodeList id records).length := by
  change (ProgramEncoding.encodeRecords records.reverse).length =
    (ProgramEncoding.encodeRecords records).length
  simp [ProgramEncoding.encodeRecords_length, List.map_reverse]

end SubexponentialSAT.ExecLiteralDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseDedupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program for last-occurrence clause deduplication

The current clause is compared with the unread suffix using actual set
equivalence of its literal records. The suffix copy is cleared after each
query, and the final record reversal restores the prescribed clause order.
-/

namespace SubexponentialSAT.ExecClauseDedupProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram (Regs Data state reset flags)

theorem clean_canonical (regs : Regs) (source output payload : List Bool) :
    Clean (state regs [] [] [] source output payload) := by
  intro i
  fin_cases i <;> rfl

theorem eq_canonical (d : Data) (hc : Clean d) :
    d = state d.regs [] [] [] (d.stacks 13) (d.stacks 14) (d.stacks 15) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> first
    | exact hc 0
    | exact hc 1
    | exact hc 2
    | exact hc 3
    | exact hc 4
    | exact hc 5
    | exact hc 6
    | exact hc 7
    | exact hc 8
    | exact hc 9
    | exact hc 10
    | exact hc 11
    | exact hc 12
    | rfl

theorem copySuffix_eval (regs : Regs) (source output payload : List Bool) :
    Eval copySuffix (7 * source.length + 5)
      (state regs [] [] [] source output payload)
      (state (reset regs) [] [] source source output payload) := by
  have h := ListRegisterProgram.copy_run (r := 15) (s := 16)
    13 12 9 0 1 (by decide) (by decide) (by decide) (by decide)
    regs (state regs [] [] [] source output payload).stacks (by rfl)
  have hs : StackRoutines.copyStacks 13 12
      (state regs [] [] [] source output payload).stacks =
      (state (reset regs) [] [] source source output payload).stacks := by
    funext i
    fin_cases i <;> simp [StackRoutines.copyStacks, state]
  rw [hs] at h
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, state, reset] using h

theorem clearMaster_eval (regs : Regs) (master source output payload : List Bool) :
    Eval (ExecClauseFiltersProgram.clear 12) (2 * master.length + 3)
      (state regs [] [] master source output payload)
      (state (reset regs) [] [] [] source output payload) := by
  have heq : ExecClauseFiltersProgram.cleared 12 (state regs [] [] master source output payload) =
      state (reset regs) [] [] [] source output payload := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state, StackRoutines.clearStacks]
  have h := ExecClauseFiltersProgram.clear_eval 12
    (state regs [] [] master source output payload)
  rw [heq] at h
  simpa [state] using h

theorem equivalent_comm {α : Type*} [DecidableEq α] (C D : List α) :
    ExecCNF.equivalent C D = ExecCNF.equivalent D C := by
  exact Bool.and_comm _ _

theorem any_equivalent (rest : Formula) (clause : Clause) :
    rest.any (fun C => ExecClauseRelationScan.test .equivalent C clause) =
      rest.any (fun C => ExecCNF.equivalent clause C) := by
  congr 1
  funext C
  exact equivalent_comm C clause

theorem callback_canonical (rest : Formula) (clause : Clause) (regs : Regs)
    (output : List Bool) :
    ∃ (n : ℕ) (rf : Regs), n ≤ callbackBound rest clause ∧
      rf 0 = false ∧ rf 1 = false ∧ rf 14 = false ∧
      Eval callback n
        (state regs [] [] [] (encodeFormula rest) output (encodeClause clause).reverse)
        (state rf [] [] [] (encodeFormula rest)
          (if rest.any (fun C => ExecCNF.equivalent clause C) then output
            else true :: (Encoding.frame (encodeClause clause) ++ output)) []) := by
  obtain ⟨n, rf, hn, h0, h1, h14, he⟩ :=
    ExecClauseFiltersProgram.callback_eval .equivalent rest clause (reset regs)
      (encodeFormula rest) output
  rw [any_equivalent] at he
  have hout : (if !(rest.any (fun C => ExecCNF.equivalent clause C)) then
      true :: (Encoding.frame (encodeClause clause) ++ output) else output) =
      (if rest.any (fun C => ExecCNF.equivalent clause C) then output
        else true :: (Encoding.frame (encodeClause clause) ++ output)) := by
    cases rest.any (fun C => ExecCNF.equivalent clause C) <;> rfl
  rw [hout] at he
  refine ⟨(7 * (encodeFormula rest).length + 5) + (n + (2 * (encodeFormula rest).length + 3)),
    reset rf, ?_, ?_, ?_, ?_, ?_⟩
  · unfold callbackBound
    omega
  · simp [reset, readRegs]
  · simp [reset, readRegs]
  · simpa [reset, readRegs] using h14
  · exact Eval.seq (copySuffix_eval regs _ _ _) (Eval.seq he (clearMaster_eval rf _ _ _ _))

theorem callback_state_eval (rest : Formula) (clause : Clause) (base : Data)
    (hc : Clean base) :
    ∃ (n : ℕ) (next : Data), n ≤ callbackBound rest clause ∧ Clean next ∧
      next.stacks 14 = (if rest.any (fun C => ExecCNF.equivalent clause C) then base.stacks 14
        else true :: (Encoding.frame (encodeClause clause) ++ base.stacks 14)) ∧
      Eval callback n
        (RecordPrograms.state ports base false true false (encodeFormula rest) (encodeClause clause).reverse)
        (RecordPrograms.state ports next false false false (encodeFormula rest) []) := by
  let d := RecordPrograms.state ports base false true false (encodeFormula rest) (encodeClause clause).reverse
  have hd : Clean d := (clean_state _ _ _ _ _ _).mpr hc
  have hrepr : d = state d.regs [] [] [] (encodeFormula rest) (base.stacks 14)
      (encodeClause clause).reverse := by
    simpa [d, RecordPrograms.state, ports] using eq_canonical d hd
  obtain ⟨n, rf, hn, h0, h1, h14, he⟩ := callback_canonical rest clause d.regs (base.stacks 14)
  rw [← hrepr] at he
  let next := state rf [] [] [] (encodeFormula rest)
    (if rest.any (fun C => ExecCNF.equivalent clause C) then base.stacks 14
      else true :: (Encoding.frame (encodeClause clause) ++ base.stacks 14)) []
  have hend : RecordPrograms.state ports next false false false (encodeFormula rest) [] = next :=
    RecordPrograms.state_eq_self ports next false false false _ [] h0 h1 h14 rfl rfl
  refine ⟨n, next, hn, clean_canonical _ _ _ _, rfl, ?_⟩
  rw [hend]
  exact he

theorem encodeFormula_records (formula : Formula) :
    encodeFormula formula = Encoding.encodeList id (formula.map encodeClause) := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      exact congrArg (fun tail => true :: (Encoding.frame (encodeClause clause) ++ tail)) ih

theorem loop_run (formula : Formula) (acc : List (List Bool)) (base : Data)
    (hc : Clean base) (hacc : base.stacks 14 = Encoding.encodeList id acc) :
    ∃ (n : ℕ) (next : Data), n ≤ 1 + budget formula ∧ Clean next ∧
      next.stacks 14 = Encoding.encodeList id (((ExecCNF.dedupClauses formula).map encodeClause).reverse ++ acc) ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports base (formula.map encodeClause) [])
        (RecordPrograms.state ports next false true false [] []) := by
  induction formula generalizing base acc with
  | nil =>
      refine ⟨1, base, by simp [budget], hc, ?_, ?_⟩
      · simpa [ExecCNF.dedupClauses] using hacc
      · apply Eval.while_false
        simp [RecordPrograms.afterTag]
  | cons clause rest ih =>
      obtain ⟨n, middle, hn, hmiddle, hout, he⟩ := callback_state_eval rest clause base hc
      let acc' := if rest.any (fun C => ExecCNF.equivalent clause C) then acc else encodeClause clause :: acc
      have hacc' : middle.stacks 14 = Encoding.encodeList id acc' := by
        cases h : rest.any (fun C => ExecCNF.equivalent clause C) <;>
          simpa [acc', h, hacc, Encoding.encodeList] using hout
      obtain ⟨m, next, hm, hnext, hresult, hrest⟩ := ih acc' middle hmiddle hacc'
      have hreader : Eval (RecordPrograms.reader ports) (6 * (encodeClause clause).length + 4)
          (RecordPrograms.afterTag ports base ((clause :: rest).map encodeClause) [])
          (RecordPrograms.state ports base false true false (encodeFormula rest) (encodeClause clause).reverse) := by
        simpa [RecordPrograms.afterTag, ← encodeFormula_records] using RecordPrograms.reader_eval ports base
          (encodeClause clause) (Encoding.encodeList id (rest.map encodeClause)) [] true true false
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false false false (encodeFormula rest) [])
          (RecordPrograms.afterTag ports middle (rest.map encodeClause) []) := by
        apply Eval.ite_false (by simp)
        simpa [← encodeFormula_records] using RecordPrograms.pop_list_eval ports middle
          (rest.map encodeClause) [] false false
      have hbody := Eval.seq hreader (Eval.seq he hbranch)
      have hrun := Eval.while_true (body := RecordPrograms.body ports callback)
        (by simp [RecordPrograms.afterTag]) hbody hrest
      refine ⟨(6 * (encodeClause clause).length + 4 + (n + 2)) + m + 1,
        next, ?_, hnext, ?_, hrun⟩
      · simp only [budget]
        omega
      · cases h : rest.any (fun C => ExecCNF.equivalent clause C) <;>
          simpa [ExecCNF.dedupClauses, h, acc', List.reverse_cons, List.append_assoc] using hresult

theorem scan_eval (formula : Formula) (acc : List (List Bool)) (base : Data)
    (hc : Clean base) (hacc : base.stacks 14 = Encoding.encodeList id acc) (v pr f : Bool) :
    ∃ (n : ℕ) (next : Data), n ≤ 3 + budget formula ∧ Clean next ∧
      next.stacks 14 = Encoding.encodeList id (((ExecCNF.dedupClauses formula).map encodeClause).reverse ++ acc) ∧
      Eval scan n (RecordPrograms.state ports base v pr f (encodeFormula formula) [])
        (RecordPrograms.state ports next false true false [] []) := by
  obtain ⟨n, next, hn, hnext, hout, hloop⟩ := loop_run formula acc base hc hacc
  refine ⟨1 + (1 + n), next, by omega, hnext, hout, ?_⟩
  rw [encodeFormula_records]
  apply Eval.seq (RecordPrograms.set_found_eval ports base v pr f false _ [])
  apply Eval.seq _ hloop
  simpa using RecordPrograms.pop_list_eval ports base (formula.map encodeClause) [] v pr

theorem budget_le (formula : Formula) : budget formula ≤ 1000 * (encodeFormula formula).length ^ 2 := by
  induction formula with
  | nil => simp [budget, encodeFormula]
  | cons clause rest ih =>
      change budget rest ≤ 1000 * (Encoding.encodeList encodeClause rest).length ^ 2 at ih
      simp only [budget, callbackBound, ExecClauseFiltersProgram.callbackBound,
        ExecClauseRelationScan.Preserving.bound, encodeFormula, Encoding.length_encodeList_cons]
      nlinarith [Nat.zero_le ((encodeClause clause).length * (encodeClause clause).length),
        Nat.zero_le ((encodeClause clause).length * (Encoding.encodeList encodeClause rest).length)]

theorem encoded_dedup_length_le (formula : Formula) :
    (encodeFormula (ExecCNF.dedupClauses formula)).length ≤ (encodeFormula formula).length := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      unfold ExecCNF.dedupClauses
      split
      · simp only [encodeFormula, Encoding.length_encodeList_cons]
        exact ih.trans (by simp [encodeFormula])
      · simpa only [encodeFormula, Encoding.length_encodeList_cons] using
          Nat.add_le_add_left ih (2 * (encodeClause clause).length + 2)

theorem reverseCall_eval (records acc : List (List Bool)) (d : Data) (hc : Clean d)
    (hs : d.stacks 14 = Encoding.encodeList id records)
    (ho : d.stacks 13 = Encoding.encodeList id acc) (hp : d.stacks 15 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ e : Data,
      Eval reverseCall n d e ∧ Clean e ∧
      e.stacks 13 = Encoding.encodeList id (records.reverse ++ acc) ∧
      e.stacks 14 = [] ∧ e.stacks 15 = [] := by
  have hd : d = ExecClauseFilterReverse.state d.regs
      (Encoding.encodeList id acc) (Encoding.encodeList id records) [] := by
    simpa only [hs, ho, hp, ExecClauseFiltersProgram.state,
      ExecClauseFilterReverse.state] using eq_canonical d hc
  obtain ⟨n, hn, he⟩ := ExecClauseFilterReverse.reverse_eval records acc d.regs
  rw [← hd] at he
  refine ⟨n, hn, _, he, ?_, rfl, rfl, rfl⟩
  exact clean_canonical _ _ _ _

theorem pushFalse_eval (stack : Fin 16) (d : Data) : Eval (pushFalse stack) 2 d (pushed stack d) := by
  let middle : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  have h₁ : Eval (RecordPrograms.atom (.set 0 false)) 1 d middle := by
    apply Eval.base
    simpa [middle, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 15) (s := 16) 0 false) d
  have h₂ : Eval (RecordPrograms.atom (.push stack 0)) 1 middle (pushed stack d) := by
    apply Eval.base
    simpa [middle, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 15) (s := 16) stack 0) middle
  exact Eval.seq h₁ h₂

theorem ready_iff (d : Data) : Ready d ↔ Clean d ∧ d.stacks 14 = [] ∧ d.stacks 15 = [] := by
  constructor
  · intro h
    exact ⟨fun i => h (workPort i) (workPort_ne_source i), h 14 (by decide), h 15 (by decide)⟩
  · rintro ⟨hc, h14, h15⟩ i hi
    fin_cases i <;> first
      | exact hc 0
      | exact hc 1
      | exact hc 2
      | exact hc 3
      | exact hc 4
      | exact hc 5
      | exact hc 6
      | exact hc 7
      | exact hc 8
      | exact hc 9
      | exact hc 10
      | exact hc 11
      | exact hc 12
      | exact (hi rfl).elim
      | exact h14
      | exact h15

theorem command_eval (formula : Formula) (d : Data)
    (hsource : d.stacks 13 = encodeFormula formula) (hready : Ready d) :
    ∃ n ≤ 1000 * (encodeFormula formula).length ^ 2 + 10 * (encodeFormula formula).length + 7,
      ∃ e : Data, Eval command n d e ∧ Ready e ∧
        e.stacks 13 = encodeFormula (ExecCNF.dedupClauses formula) := by
  rcases (ready_iff d).mp hready with ⟨hclean, houtput, hpayload⟩
  let a := pushed 14 d
  have ha : Clean a := by
    simpa [a, pushed, Clean] using hclean
  have hao : a.stacks 14 = Encoding.encodeList id [] := by
    simp [a, pushed, houtput, Encoding.encodeList]
  obtain ⟨n, next, hn, hnext, hout, hs⟩ := scan_eval formula [] a ha hao
    (a.regs 0) (a.regs 1) (a.regs 14)
  have hstart : RecordPrograms.state ports a (a.regs 0) (a.regs 1) (a.regs 14)
      (encodeFormula formula) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, pushed, ports] using hsource
    · simpa [a, pushed, ports] using hpayload
  rw [hstart] at hs
  let b := RecordPrograms.state ports next false true false [] []
  let c := pushed 13 b
  have hc : Clean c := by
    simpa [c, pushed, b, Clean, RecordPrograms.state, ports] using hnext
  have hc14 : c.stacks 14 =
      Encoding.encodeList id ((ExecCNF.dedupClauses formula).map encodeClause).reverse := by
    simpa [c, pushed, b] using hout
  have hc13 : c.stacks 13 = Encoding.encodeList id [] := by
    simp [c, pushed, b, RecordPrograms.state, ports, Encoding.encodeList]
  have hc15 : c.stacks 15 = [] := by
    simp [c, pushed, b, RecordPrograms.state, ports]
  obtain ⟨m, hm, e, he, hce, he13, he14, he15⟩ :=
    reverseCall_eval ((ExecCNF.dedupClauses formula).map encodeClause).reverse [] c hc hc14 hc13 hc15
  have hcost := budget_le formula
  have hlength := encoded_dedup_length_le formula
  rw [ExecLiteralDedupProgram.encoded_reverse_length, ← encodeFormula_records] at hm
  refine ⟨2 + (n + (2 + m)), ?_, e, ?_, (ready_iff e).mpr ⟨hce, he14, he15⟩, ?_⟩
  · omega
  · exact Eval.seq (pushFalse_eval 14 d) (Eval.seq hs (Eval.seq (pushFalse_eval 13 b) he))
  · simpa only [List.reverse_reverse, List.append_nil, ← encodeFormula_records] using he13

theorem generic_runsIn (formula : Formula) (d : Data)
    (hsource : d.stacks 13 = encodeFormula formula) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = encodeFormula (ExecCNF.dedupClauses formula) ∧
      RunsIn program (1200 * ((encodeFormula formula).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hready', hout⟩ := command_eval formula d hsource hready
  refine ⟨e, hready', hout, n + 1, ?_, compiled_halt_trace he 13 13⟩
  nlinarith

theorem dedup_codes (formula : List (List ℕ)) :
    ExecCNF.dedupClauses (ExecClauseRelationScan.codeFormula formula) =
      ExecClauseRelationScan.codeFormula (ExecCNF.dedupClauses formula) :=
  ExecCNFCodeTransport.dedupClauses_map Encoding.encodeNat Encoding.encodeNat_injective formula

/-- The fixed program implements precisely the executable normalizer's
last-occurrence clause deduplication, including differently ordered clauses. -/
theorem program_runsIn (formula : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode formula) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = formulaCode (ExecCNF.dedupClauses formula) ∧
      RunsIn program (1200 * ((formulaCode formula).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  have hs : d.stacks 13 = encodeFormula (ExecClauseRelationScan.codeFormula formula) := by
    simpa only [formulaCode, ExecClauseRelationScan.encodeFormula_codes] using hsource
  obtain ⟨e, he, hout, hr⟩ := generic_runsIn (ExecClauseRelationScan.codeFormula formula) d hs hready
  rw [dedup_codes, ExecClauseRelationScan.encodeFormula_codes] at hout
  exact ⟨e, he, hout, by
    simpa only [formulaCode, ExecClauseRelationScan.encodeFormula_codes] using hr⟩

end SubexponentialSAT.ExecClauseDedupProgram

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

theorem removeSupersets_dedup (F : List (List ℕ)) :
    removeSupersets (ExecCNF.dedupClauses F) = ExecCNF.absorb F :=
  (ExecCNF.absorb_eq_filter_dedup F).symm

theorem dedup_length_le (F : List (List ℕ)) :
    (formulaCode (ExecCNF.dedupClauses F)).length ≤ (formulaCode F).length :=
  ExecCNF.length_encodeList_dedupClauses_le _ _

theorem dedupCall_eval (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 1200 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval dedupCall n d e ∧ Ready e ∧
      e.stacks 13 = formulaCode (ExecCNF.dedupClauses F) := by
  obtain ⟨e, he, hout, n, hn, ht⟩ := ExecClauseDedupProgram.program_runsIn F d hsource hready
  exact ⟨n, hn, e, .call _ ht, he, hout⟩

theorem absorb_eval_oai (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 2200 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval absorbCommand n d e ∧ Ready e ∧
      e.stacks 13 = formulaCode (ExecCNF.absorb F) := by
  obtain ⟨n, hn, a, hdup, ha, haout⟩ := dedupCall_eval F d hsource hready
  obtain ⟨m, hm, e, hfilter, he, heout⟩ :=
    removeSupersetsCall_eval (ExecCNF.dedupClauses F) a haout ha
  have hm' : m ≤ 1000 * ((formulaCode F).length + 1) ^ 2 :=
    hm.trans (Nat.mul_le_mul_left 1000
      (Nat.pow_le_pow_left (Nat.add_le_add_right (dedup_length_le F) 1) 2))
  refine ⟨n + m, by omega, e, hdup.seq hfilter, he, ?_⟩
  simpa only [removeSupersets_dedup] using heout

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.absorb_eval_oai := @OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.absorb_eval_oai
