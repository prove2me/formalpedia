-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.familyCall_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:16:17.480213+00:00
-- url     : https://prove2.me/submissions/e67d7470-99b9-42d2-92aa-e1da8ef6a76c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S097
import Definitions.Def_OAIQ081S111

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSubset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded clause subset testing

The fixed program uses ten Boolean registers and eight Boolean stacks. The
source clause is scanned destructively on stack 0. Stack 2 preserves the entire
encoded target clause. All comparisons use the proved encoded membership
program, after a real preserving copy of the target.
-/
namespace SubexponentialSAT.ExecCNFSubset
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem clear_eval (port : Fin 8) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have h := StackRoutines.clearProgram_trace (r := 10) (s := 8) port 0 1 d.regs d.stacks
  have hh : step (clearProgram port)
      (StackRoutines.clearResult 2 port 0 1 d.regs d.stacks) =
      some ((cleared port d).withPC none) := by
    simp [step, StackRoutines.clearResult, StructuredProgram.State.withPC, execInstr]
  apply Eval.call
  simpa [clearProgram, cleared, StructuredProgram.State.withPC, Nat.add_assoc] using
    h.trans (.cons hh (.refl _))

end SubexponentialSAT.ExecCNFSubset

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

end SubexponentialSAT.ExecClauseFiltersProgram

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

theorem emitReg_injective : Function.Injective emitReg := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitReg]

theorem emitStack_injective : Function.Injective emitStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitStack]

private theorem embed_restricted {r s R S : ℕ}
    (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame : State R S) :
    embedState reg stk frame ⟨frame.regs ∘ reg, frame.stacks ∘ stk⟩ = frame := by
  cases frame with
  | mk regs stackValues =>
      unfold embedState
      congr 1
      · funext i
        by_cases h : ∃ j, reg j = i
        · obtain ⟨j, rfl⟩ := h
          exact hr.extend_apply _ _ _
        · exact Function.extend_apply' _ _ _ h
      · funext i
        by_cases h : ∃ j, stk j = i
        · obtain ⟨j, rfl⟩ := h
          exact hs.extend_apply _ _ _
        · exact Function.extend_apply' _ _ _ h

theorem emitCall_eval (selected : Bool) (bits : List Bool) (d : Data)
    (hquery : d.stacks 1 = bits.reverse) (hselected : d.regs 9 = selected) :
    ∃ e : Data,
      Eval emitCall (SubexpNormalizeProgram.emitIfSelectedSteps selected bits + 1) d e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = (if selected then true :: (Encoding.frame bits ++ d.stacks 2) else d.stacks 2) ∧
      e.stacks 3 = d.stacks 3 ∧ e.stacks 4 = d.stacks 4 ∧
      e.stacks 5 = d.stacks 5 ∧ e.stacks 6 = d.stacks 6 ∧ e.stacks 7 = d.stacks 7 ∧
      e.regs 7 = false ∧ e.regs 8 = true ∧ e.regs 9 = false := by
  let a : State 3 4 := ⟨d.regs ∘ emitReg, d.stacks ∘ emitStack⟩
  have ha : a = SubexpNormalizeProgram.filterState (d.regs 7) (d.regs 8) selected
      (d.stacks 0) (d.stacks 7) (d.stacks 2) bits.reverse := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ emitReg, hselected]
    · funext i
      fin_cases i <;> simp [ emitStack, hquery]
  have ht := SubexpNormalizeProgram.emitIfSelected_trace selected bits
    (d.stacks 0) (d.stacks 7) (d.stacks 2) (d.regs 7) (d.regs 8)
  rw [← ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram
    emitReg emitStack d emitReg_injective emitStack_injective ht
  rw [embed_restricted emitReg emitStack emitReg_injective emitStack_injective d] at he
  let b := SubexpNormalizeProgram.filterState false true false
    (d.stacks 0) (d.stacks 7)
    (if selected then true :: (Encoding.frame bits ++ d.stacks 2) else d.stacks 2) []
  let e := embedState emitReg emitStack d b
  have hstack (i : Fin 4) : e.stacks (emitStack i) = b.stacks i :=
    embedState_stack _ _ _ _ emitStack_injective i
  have hreg (i : Fin 3) : e.regs (emitReg i) = b.regs i :=
    embedState_register _ _ _ _ emitReg_injective i
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hstack 0
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hstack 3
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hstack 2
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hstack 1
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hreg 0
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hreg 1
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hreg 2

theorem reverseStack_injective : Function.Injective reverseStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [reverseStack]

theorem reverseCall_eval (records acc : List (List Bool)) (d : Data)
    (hsource : d.stacks 2 = Encoding.encodeList id records)
    (houtput : d.stacks 0 = Encoding.encodeList id acc) (hpayload : d.stacks 1 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ e : Data,
      Eval reverseCall n d e ∧
      e.stacks 0 = Encoding.encodeList id (records.reverse ++ acc) ∧
      e.stacks 1 = [] ∧ e.stacks 2 = [] ∧
      e.stacks 3 = d.stacks 3 ∧ e.stacks 4 = d.stacks 4 ∧
      e.stacks 5 = d.stacks 5 ∧ e.stacks 6 = d.stacks 6 ∧ e.stacks 7 = d.stacks 7 := by
  let a : State 3 4 := ⟨d.regs ∘ emitReg, d.stacks ∘ reverseStack⟩
  have ha : a = SubexpNormalizeProgram.filterState (d.regs 7) (d.regs 8) (d.regs 9)
      (Encoding.encodeList id records) (d.stacks 7) (Encoding.encodeList id acc) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ emitReg ]
    · funext i
      fin_cases i <;> simp [ reverseStack,
        hsource, houtput, hpayload]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc []
    (d.stacks 7) (d.regs 7) (d.regs 8) (d.regs 9)
  simp only [List.append_nil] at ht
  rw [← ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    emitReg reverseStack d emitReg_injective reverseStack_injective ht
  rw [embed_restricted emitReg reverseStack emitReg_injective reverseStack_injective d] at he
  let b := SubexpNormalizeProgram.filterState false true false [] (d.stacks 7)
    (Encoding.encodeList id (records.reverse ++ acc)) []
  let e := embedState emitReg reverseStack d b
  have hstack (i : Fin 4) : e.stacks (reverseStack i) = b.stacks i :=
    embedState_stack _ _ _ _ reverseStack_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 2
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 3
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 0
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 1

theorem encoded_reverse_length (records : List (List Bool)) :
    (Encoding.encodeList id records.reverse).length = (Encoding.encodeList id records).length := by
  change (ProgramEncoding.encodeRecords records.reverse).length =
    (ProgramEncoding.encodeRecords records).length
  simp [ProgramEncoding.encodeRecords_length, List.map_reverse]

end SubexponentialSAT.ExecLiteralDedupProgram

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

theorem lowStack_injective : Function.Injective lowStack := Fin.castAdd_injective 8 1

private theorem embed_small_state (frameRegs regs : Regs)
    (source₀ query₀ output₀ target₀ source query output target core : List Bool) :
    embedState id lowStack (state frameRegs source₀ query₀ output₀ target₀ core)
      (smallState regs source query output target) = state regs source query output target core := by
  apply embedState_eq_of_ports id lowStack _ _ _ Function.injective_id lowStack_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hlo : 8 ≤ i.val := by
      by_contra h
      have hil : i.val < 8 := by omega
      exact hi ⟨⟨i.val, hil⟩, Fin.ext rfl⟩
    fin_cases i <;> simp_all [state]

theorem probe_eval (bits : List Bool) (H : List (List Bool)) (regs : Regs)
    (source output : List Bool) :
    ∃ n ≤ (20 * bits.length + 32) * (Encoding.encodeList id H).length + 10,
      ∃ rf : Regs, rf 4 = decide (bits ∈ H) ∧
      Eval probe n (smallState regs source bits.reverse output (Encoding.encodeList id H))
        (smallState rf source bits.reverse output []) := by
  let d := smallState regs source bits.reverse output (Encoding.encodeList id H)
  obtain ⟨n, hn, e, he, ha, hs, hp, hq, hc, ht, h0, h2, h7, hreg7, hreg8, hreg9⟩ :=
    ExecCNFSubset.memberCall_eval bits H d rfl rfl rfl rfl rfl
  let result := ExecCNFSubset.cleared 4 (ExecCNFSubset.cleared 3 e)
  have hresult : result = smallState result.regs source bits.reverse output [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [ smallState, StackRoutines.clearStacks,
        h0, h2, h7, hq, hc, ht, d]
  have hcost : (2 * ((ExecCNFSubset.cleared 3 e).stacks 4).length + 3) = 5 := by
    simp [ StackRoutines.clearStacks, hp]
  have hfull := he.seq ((ExecCNFSubset.clear_eval 3 e).seq
    (ExecCNFSubset.clear_eval 4 (ExecCNFSubset.cleared 3 e)))
  rw [hcost] at hfull
  change Eval probe _ d result at hfull
  rw [hresult] at hfull
  refine ⟨n + ((2 * (e.stacks 3).length + 3) + 5), ?_, result.regs, ?_, hfull⟩
  · nlinarith
  · simpa [result, ExecCNFSubset.cleared, readRegs] using ha

theorem wideProbe_eval (bits : List Bool) (H : List (List Bool)) (regs : Regs)
    (source output core : List Bool) :
    ∃ n ≤ (20 * bits.length + 32) * (Encoding.encodeList id H).length + 11,
      ∃ rf : Regs, rf 4 = decide (bits ∈ H) ∧
      Eval wideProbe n (state regs source bits.reverse output (Encoding.encodeList id H) core)
        (state rf source bits.reverse output [] core) := by
  obtain ⟨n, hn, rf, hr, he⟩ := probe_eval bits H regs source output
  have h := eval_call_lifted probeProgram id lowStack
    (state regs source bits.reverse output (Encoding.encodeList id H) core)
    Function.injective_id lowStack_injective (compiled_halt_trace he 3 4)
  rw [embed_small_state, embed_small_state] at h
  exact ⟨n + 1, by omega, rf, hr, h⟩

theorem copyCore_eval (regs : Regs) (source query output core : List Bool) :
    Eval copyCore (7 * core.length + 5)
      (state regs source query output [] core)
      (state (readRegs regs 0 1 none) source query output core core) := by
  have h := ListRegisterProgram.copy_run (r := 10) (s := 9) 8 3 7 0 1
    (by decide) (by decide) (by decide) (by decide) regs
    (state regs source query output [] core).stacks rfl
  have hs : StackRoutines.copyStacks 8 3 (state regs source query output [] core).stacks =
      (state (readRegs regs 0 1 none) source query output core core).stacks := by
    funext i
    fin_cases i <;> simp [state, StackRoutines.copyStacks]
  rw [hs] at h
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, state] using h

theorem emit_eval (selected : Bool) (bits : List Bool) (regs : Regs)
    (source output core : List Bool) (hr : regs 9 = selected) :
    ∃ rf : Regs, rf 7 = false ∧ rf 8 = true ∧ rf 9 = false ∧
      Eval emit (SubexpNormalizeProgram.emitIfSelectedSteps selected bits + 1)
        (state regs source bits.reverse output [] core)
        (state rf source []
          (if selected then true :: (Encoding.frame bits ++ output) else output) [] core) := by
  let d := smallState regs source bits.reverse output []
  obtain ⟨e, he, h0, h1, h2, h3, h4, h5, h6, h7, hr7, hr8, hr9⟩ :=
    ExecLiteralDedupProgram.emitCall_eval selected bits d rfl hr
  have heq : e = smallState e.regs source []
      (if selected then true :: (Encoding.frame bits ++ output) else output) [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [smallState, h0, h1, h2, h3, h4, h5, h6, h7, d]
  have ht : Trace ExecLiteralDedupProgram.emitProgram
      (SubexpNormalizeProgram.emitIfSelectedSteps selected bits + 1)
      (d.withPC (some ExecLiteralDedupProgram.emitProgram.entry)) (e.withPC none) := by
    cases he with
    | call _ h => exact h
  rw [heq] at ht
  have h := eval_call_lifted ExecLiteralDedupProgram.emitProgram id lowStack
    (state regs source bits.reverse output [] core) Function.injective_id lowStack_injective ht
  change Eval emit _ (embedState id lowStack _ (smallState regs source bits.reverse output [])) _ at h
  rw [embed_small_state, embed_small_state] at h
  exact ⟨e.regs, hr7, hr8, hr9, h⟩

theorem callback_eval (bits : List Bool) (H : List (List Bool)) (regs : Regs)
    (source output : List Bool) :
    ∃ n ≤ callbackCost H bits, ∃ rf : Regs,
      rf 7 = false ∧ rf 8 = true ∧ rf 9 = false ∧
      Eval callback n (state regs source bits.reverse output [] (Encoding.encodeList id H))
        (state rf source []
          (if bits ∈ H then output else true :: (Encoding.frame bits ++ output))
          [] (Encoding.encodeList id H)) := by
  obtain ⟨n, hn, rf, hr, he⟩ := wideProbe_eval bits H (readRegs regs 0 1 none)
    source output (Encoding.encodeList id H)
  let selected := Function.update rf 9 (!(rf 4))
  have hs : selected 9 = !(decide (bits ∈ H)) := by simp [selected, hr]
  obtain ⟨final, hf7, hf8, hf9, hf⟩ := emit_eval (!(decide (bits ∈ H))) bits selected
    source output (Encoding.encodeList id H) hs
  have hselect : Eval (RecordPrograms.atom (.bnot 9 4)) 1
      (state rf source bits.reverse output [] (Encoding.encodeList id H))
      (state selected source bits.reverse output [] (Encoding.encodeList id H)) :=
    .base (.atom _ _)
  have hfull := (copyCore_eval regs source bits.reverse output (Encoding.encodeList id H)).seq
    (he.seq (hselect.seq hf))
  have hcost := SubexpNormalizeProgram.emitIfSelected_steps_le (!(decide (bits ∈ H))) bits
  refine ⟨(7 * (Encoding.encodeList id H).length + 5) +
    (n + (1 + (SubexpNormalizeProgram.emitIfSelectedSteps (!(decide (bits ∈ H))) bits + 1))),
    ?_, final, hf7, hf8, hf9, ?_⟩
  · dsimp [callbackCost]
    nlinarith
  · simpa using hfull

end SubexponentialSAT.ExecPetalProgram
namespace SubexponentialSAT.ExecPetalProgram
open BitProgram StructuredCalls

theorem record_state (regs : Regs) (src query output target core tail bits : List Bool)
    (v p f : Bool) :
    RecordPrograms.state ports (state regs src query output target core) v p f tail bits =
      state (flags regs v p f) tail bits output target core := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ ports, state]

theorem state_invariant (H : List (List Bool)) (regs : Regs) (source output payload : List Bool) :
    invariant H (state regs source payload output [] (Encoding.encodeList id H)) :=
  ⟨regs, source, output, payload, rfl⟩

theorem result_eq_filter_keep (C H : List (List Bool)) :
    result C H = C.filter (keep H) := by
  unfold result
  apply List.filter_congr
  intro x hx
  simp [keep]

theorem result_encoded_length_le {α : Type*} [DecidableEq α]
    (enc : α → List Bool) (C H : List α) :
    (Encoding.encodeList enc (result C H)).length ≤ (Encoding.encodeList enc C).length :=
  Encoding.length_encodeList_filter_le enc _ C

theorem callback_contract (H : List (List Bool)) :
    RecordPrograms.CallbackContractWith ports callback (fun _ => false) (callbackCost H)
      (invariant H) (SubexpNormalizeProgram.FilterEffect 2 (keep H)) := by
  intro bits tail base hbase
  obtain ⟨regs, source, output, payload, rfl⟩ := hbase
  obtain ⟨n, hn, rf, h7, h8, h9, he⟩ :=
    callback_eval bits H (flags regs false true false) tail output
  let newOutput := if bits ∈ H then output else true :: (Encoding.frame bits ++ output)
  let next := state rf [] [] newOutput [] (Encoding.encodeList id H)
  have hflags : flags rf false true false = rf := by
    simpa only [h7, h8, h9] using flags_self rf
  refine ⟨n, next, hn, state_invariant _ _ _ _ _, ?_, ?_⟩
  · simp [SubexpNormalizeProgram.FilterEffect, keep, next, newOutput, state]
  · simpa only [next, record_state, hflags] using he

theorem budget_le (C H : List (List Bool)) :
    3 + RecordPrograms.budget (callbackCost H) C ≤
      80 * ((Encoding.encodeList id H).length + 1) * ((Encoding.encodeList id C).length + 1) := by
  induction C with
  | nil => simp [RecordPrograms.budget, Encoding.encodeList]; omega
  | cons x xs ih =>
    simp only [RecordPrograms.budget, callbackCost, Encoding.length_encodeList_cons, id_eq]
    nlinarith

theorem scan_eval (C H acc : List (List Bool)) (regs : Regs) :
    ∃ n ≤ 80 * ((Encoding.encodeList id H).length + 1) *
        ((Encoding.encodeList id C).length + 1), ∃ rf : Regs,
      Eval scan n
        (state regs (Encoding.encodeList id C) [] (Encoding.encodeList id acc) []
          (Encoding.encodeList id H))
        (state rf [] [] (Encoding.encodeList id ((result C H).reverse ++ acc)) []
          (Encoding.encodeList id H)) := by
  let d := state regs (Encoding.encodeList id C) [] (Encoding.encodeList id acc) []
    (Encoding.encodeList id H)
  obtain ⟨n, next, hn, hnext, hout, he⟩ := SubexpNormalizeProgram.filter_iterate_run
    ports callback (keep H) (callbackCost H) (invariant H) 2 (by decide) (by decide)
    (callback_contract H) C acc [] d (state_invariant _ _ _ _ _) rfl
    (regs 7) (regs 8) (regs 9)
  obtain ⟨rf, source, output, payload, rfl⟩ := hnext
  have hout' : output = Encoding.encodeList id ((result C H).reverse ++ acc) := by
    simpa [RecordPrograms.state, ports, state, result_eq_filter_keep] using hout
  refine ⟨n, hn.trans (budget_le C H), flags rf false true false, ?_⟩
  simpa only [d, record_state, flags_self, List.append_nil, hout'] using he

theorem reverse_eval (records acc : List (List Bool)) (regs : Regs) (core : List Bool) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ rf : Regs,
      Eval reverseCall n
        (state regs (Encoding.encodeList id acc) [] (Encoding.encodeList id records) [] core)
        (state rf (Encoding.encodeList id (records.reverse ++ acc)) [] [] [] core) := by
  let d := smallState regs (Encoding.encodeList id acc) [] (Encoding.encodeList id records) []
  obtain ⟨n, hn, e, he, h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    ExecLiteralDedupProgram.reverseCall_eval records acc d rfl rfl rfl
  have heq : e = smallState e.regs (Encoding.encodeList id (records.reverse ++ acc)) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [smallState, h0, h1, h2, h3, h4, h5, h6, h7, d]
  have ht : Trace ExecLiteralDedupProgram.reverseProgram n
      (d.withPC (some ExecLiteralDedupProgram.reverseProgram.entry)) (e.withPC none) := by
    cases he with
    | call _ h => exact h
  rw [heq] at ht
  have h := eval_call_lifted ExecLiteralDedupProgram.reverseProgram id lowStack
    (state regs (Encoding.encodeList id acc) [] (Encoding.encodeList id records) [] core)
    Function.injective_id lowStack_injective ht
  change Eval reverseCall n (embedState id lowStack _
    (smallState regs (Encoding.encodeList id acc) [] (Encoding.encodeList id records) [])) _ at h
  rw [embed_small_state, embed_small_state] at h
  exact ⟨n, hn, e.regs, h⟩

theorem pushFalse_eval (port : Fin 9) (d : Data) : Eval (pushFalse port) 2 d (pushed port d) := by
  have h := Eval.seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 10) (s := 9) 0 false) d))
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 10) (s := 9) port 0)
      ((StructuredProgram.Atom.set 0 false).eval d)))
  exact h

theorem pushOutput_eval (regs : Regs) (source output core : List Bool) :
    Eval (pushFalse 2) 2 (state regs source [] output [] core)
      (state (Function.update regs 0 false) source [] (false :: output) [] core) := by
  have h := pushFalse_eval 2 (state regs source [] output [] core)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ state]

theorem pushSource_eval (regs : Regs) (source output core : List Bool) :
    Eval (pushFalse 0) 2 (state regs source [] output [] core)
      (state (Function.update regs 0 false) (false :: source) [] output [] core) := by
  have h := pushFalse_eval 0 (state regs source [] output [] core)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ state]

theorem command_eval (C H : List (List Bool)) (regs : Regs) :
    ∃ n ≤ 100 * ((Encoding.encodeList id H).length + 1) *
        ((Encoding.encodeList id C).length + 1), ∃ rf : Regs,
      Eval command n (state regs (Encoding.encodeList id C) [] [] [] (Encoding.encodeList id H))
        (state rf (Encoding.encodeList id (result C H)) [] [] [] (Encoding.encodeList id H)) := by
  obtain ⟨n, hn, rf, hs⟩ := scan_eval C H [] (Function.update regs 0 false)
  simp only [List.append_nil] at hs
  obtain ⟨m, hm, final, hr⟩ := reverse_eval (result C H).reverse []
    (Function.update rf 0 false) (Encoding.encodeList id H)
  simp only [List.reverse_reverse, List.append_nil] at hr
  rw [ExecLiteralDedupProgram.encoded_reverse_length] at hm
  have hlen : (Encoding.encodeList id (result C H)).length ≤
      (Encoding.encodeList id C).length := result_encoded_length_le id C H
  refine ⟨2 + (n + (2 + m)), ?_, final, ?_⟩
  · nlinarith
  · exact (pushOutput_eval regs (Encoding.encodeList id C) [] (Encoding.encodeList id H)).seq
      (hs.seq ((pushSource_eval rf [] (Encoding.encodeList id (result C H).reverse)
        (Encoding.encodeList id H)).seq hr))

theorem program_runsIn (C H : List (List Bool)) (regs : Regs) :
    ∃ rf : Regs, RunsIn program
      (101 * ((Encoding.encodeList id H).length + 1) * ((Encoding.encodeList id C).length + 1))
      ((state regs (Encoding.encodeList id C) [] [] [] (Encoding.encodeList id H)).withPC
        (some program.entry))
      ((state rf (Encoding.encodeList id (result C H)) [] [] [] (Encoding.encodeList id H)).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval C H regs
  exact ⟨rf, n + 1, by nlinarith, compiled_halt_trace he 0 0⟩

end SubexponentialSAT.ExecPetalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalFamilyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ExecPetalFamilyProgram
open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)

theorem bankReg_injective : Function.Injective bankReg := Fin.castAdd_injective 10 3
theorem bankStack_injective : Function.Injective bankStack := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [bankStack, Fin.val_natAdd] at this
  omega

theorem petalCall_eval (C H : Clause) (regs : Regs) (source payload output : List Bool) :
    ∃ n ≤ 101 * ((encodeClause H).length + 1) * ((encodeClause C).length + 1),
      ∃ rf : Regs, Eval petalCall n
        (state regs source payload output (encodeClause C) (encodeClause H))
        (state rf source payload output (encodeClause (ExecPetalProgram.result C H)) (encodeClause H)) := by
  let d := state regs source payload output (encodeClause C) (encodeClause H)
  obtain ⟨rf, n, hn, ht⟩ := ExecPetalProgram.program_runsIn C H (regs ∘ bankReg)
  let a := ExecPetalProgram.state (regs ∘ bankReg) (encodeClause C) [] [] [] (encodeClause H)
  let b := ExecPetalProgram.state rf (encodeClause (ExecPetalProgram.result C H)) [] [] [] (encodeClause H)
  have hstart : embedState bankReg bankStack d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ bankReg_injective bankStack_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have he := eval_call_lifted ExecPetalProgram.program bankReg bankStack d
    bankReg_injective bankStack_injective ht
  change Eval petalCall n (embedState bankReg bankStack d a) (embedState bankReg bankStack d b) at he
  rw [hstart] at he
  let e := embedState bankReg bankStack d b
  have hs (i : Fin 9) : e.stacks (bankStack i) = b.stacks i :=
    embedState_stack _ _ _ _ bankStack_injective i
  have h0 : e.stacks 0 = source := embedState_stack_frame _ _ _ _ _ (by decide)
  have h1 : e.stacks 1 = payload := embedState_stack_frame _ _ _ _ _ (by decide)
  have h2 : e.stacks 2 = output := embedState_stack_frame _ _ _ _ _ (by decide)
  have heq : e = state e.regs source payload output
      (encodeClause (ExecPetalProgram.result C H)) (encodeClause H) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hs 4
    · exact hs 5
    · exact hs 6
    · exact hs 7
    · exact hs 8
  exact ⟨n, hn, e.regs, heq ▸ he⟩

theorem transfer_in (regs : Regs) (source output bits core : List Bool) :
    Eval (transfer 1 3) (3 * bits.length + 3)
      (state regs source bits.reverse output [] core)
      (state (readRegs regs 0 1 none) source [] output bits core) := by
  have h := ListRegisterProgram.transfer_run (r := 13) (s := 12) 1 3 0 1
    (by decide) (by decide) regs (state regs source bits.reverse output [] core).stacks
  have hs : StackRoutines.transferStacks 1 3 (state regs source bits.reverse output [] core).stacks =
      (state (readRegs regs 0 1 none) source [] output bits core).stacks := by
    funext i
    fin_cases i <;> simp [state, StackRoutines.transferStacks]
  have hlen : ((state regs source bits.reverse output [] core).stacks 1).length = bits.length := by
    simp [state]
  rw [hs] at h
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, state, hlen] using h

theorem transfer_out (regs : Regs) (source output bits core : List Bool) :
    Eval (transfer 3 1) (3 * bits.length + 3)
      (state regs source [] output bits core)
      (state (readRegs regs 0 1 none) source bits.reverse output [] core) := by
  have h := ListRegisterProgram.transfer_run (r := 13) (s := 12) 3 1 0 1
    (by decide) (by decide) regs (state regs source [] output bits core).stacks
  have hs : StackRoutines.transferStacks 3 1 (state regs source [] output bits core).stacks =
      (state (readRegs regs 0 1 none) source bits.reverse output [] core).stacks := by
    funext i
    fin_cases i <;> simp [state, StackRoutines.transferStacks]
  have hlen : ((state regs source [] output bits core).stacks 3).length = bits.length := by
    simp [state]
  rw [hs] at h
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, state, hlen] using h

theorem emitReg_injective : Function.Injective emitReg := by decide
theorem emitStack_injective : Function.Injective emitStack := by decide

private theorem embed_emit (regs : Regs) (v p f : Bool)
    (source₀ payload₀ output₀ source payload output work core : List Bool) :
    embedState emitReg emitStack (state regs source₀ payload₀ output₀ [] core)
      (SubexpNormalizeProgram.filterState v p f source work output payload) =
      state (flags regs v p f) source payload output work core := by
  apply embedState_eq_of_ports _ _ _ _ _ emitReg_injective emitStack_injective
  · intro i; fin_cases i <;> simp [emitReg, flags, state, SubexpNormalizeProgram.filterState]
  · intro i hi
    have h10 : i ≠ 10 := fun h => hi ⟨0, h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨1, h.symm⟩
    have h12 : i ≠ 12 := fun h => hi ⟨2, h.symm⟩
    simp [state, flags, h10, h11, h12]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    have h2 : i ≠ 2 := fun h => hi ⟨2, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨3, h.symm⟩
    fin_cases i <;> simp_all [state]

theorem emit_eval (regs : Regs) (bits source output core : List Bool) (hsel : regs 12 = true) :
    Eval emit (5 * bits.length + 12)
      (state regs source bits.reverse output [] core)
      (state (flags regs false true false) source []
        (true :: (Encoding.frame bits ++ output)) [] core) := by
  have h := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram emitReg emitStack
    (state regs source bits.reverse output [] core) emitReg_injective emitStack_injective
    (SubexpNormalizeProgram.emitIfSelected_trace true bits source [] output (regs 10) (regs 11))
  rw [embed_emit, embed_emit] at h
  have hflags : flags regs (regs 10) (regs 11) true = regs := by
    simpa only [hsel] using flags_self regs
  simpa [hflags, SubexpNormalizeProgram.emitIfSelectedSteps] using h

theorem callback_eval (C H : Clause) (regs : Regs) (source output : List Bool) :
    ∃ n ≤ cost H (encodeClause C), ∃ rf : Regs,
      rf 10 = false ∧ rf 11 = true ∧ rf 12 = false ∧
      Eval callback n (state regs source (encodeClause C).reverse output [] (encodeClause H))
        (state rf source []
          (true :: (Encoding.frame (encodeClause (ExecPetalProgram.result C H)) ++ output))
          [] (encodeClause H)) := by
  obtain ⟨n, hn, rf, he⟩ := petalCall_eval C H (readRegs regs 0 1 none) source [] output
  let restored := readRegs rf 0 1 none
  let selected := Function.update restored 12 true
  have hset : Eval (RecordPrograms.atom (.set 12 true)) 1
      (state restored source (encodeClause (ExecPetalProgram.result C H)).reverse output [] (encodeClause H))
      (state selected source (encodeClause (ExecPetalProgram.result C H)).reverse output [] (encodeClause H)) :=
    .base (.atom _ _)
  have hfull := (transfer_in regs source output (encodeClause C) (encodeClause H)).seq
    (he.seq ((transfer_out rf source output (encodeClause (ExecPetalProgram.result C H))
      (encodeClause H)).seq (hset.seq (emit_eval selected _ _ _ _ (by simp [selected])))))
  have hlen := ExecPetalProgram.result_encoded_length_le id C H
  change (encodeClause (ExecPetalProgram.result C H)).length ≤ (encodeClause C).length at hlen
  refine ⟨_, ?_, flags selected false true false, ?_, ?_, ?_, hfull⟩
  · dsimp [cost]
    nlinarith
  · simp [flags]
  · simp [flags]
  · simp [flags]

theorem record_state (regs : Regs) (source payload output clause core tail bits : List Bool)
    (v p f : Bool) :
    RecordPrograms.state ports (state regs source payload output clause core) v p f tail bits =
      state (flags regs v p f) tail bits output clause core := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ ports, state]

theorem callback_contract (H : Clause) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false) (cost H)
      (invariant H) (Effect H) ExecClauseFiltersProgram.ClausePayload := by
  intro bits tail base hbits hbase
  obtain ⟨C, rfl⟩ := hbits
  obtain ⟨regs, source, output, payload, rfl⟩ := hbase
  obtain ⟨n, hn, rf, h10, h11, h12, he⟩ :=
    callback_eval C H (flags regs false true false) tail output
  let out := true :: (Encoding.frame (encodeClause (ExecPetalProgram.result C H)) ++ output)
  let next := state rf [] [] out [] (encodeClause H)
  have hflags : flags rf false true false = rf := by
    simpa only [h10, h11, h12] using flags_self rf
  refine ⟨n, next, hn, ⟨rf, [], out, [], rfl⟩, ?_, ?_⟩
  · simp [Effect, next, state, out]
  · simpa only [next, record_state, hflags] using he

theorem visits_result (H : Clause) {records : List (List Bool)} {before after : Data}
    (h : RecordPrograms.Visits (fun _ => false) (Effect H) records before after)
    (acc : List (List Bool)) (hacc : before.stacks 2 = Encoding.encodeList id acc) :
    after.stacks 2 = Encoding.encodeList id ((records.map (mapPayload H)).reverse ++ acc) := by
  induction h generalizing acc with
  | nil base => simpa using hacc
  | hit ht _ => cases ht
  | @miss bits records before middle after _ he _ ih =>
    have hm : middle.stacks 2 = Encoding.encodeList id (mapPayload H bits :: acc) := by
      simpa [Effect, hacc, Encoding.encodeList] using he
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ih _ hm

theorem records_map (F : Formula) (H : Clause) :
    (ExecClauseFiltersProgram.formulaRecords F).map (mapPayload H) =
      ExecClauseFiltersProgram.formulaRecords (petals F H) := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    simp [ExecClauseFiltersProgram.formulaRecords, petals] at ih ⊢

theorem budget_le (H : Clause) (records : List (List Bool)) :
    3 + RecordPrograms.budget (cost H) records ≤
      160 * ((encodeClause H).length + 1) * ((Encoding.encodeList id records).length + 1) := by
  induction records with
  | nil => simp [RecordPrograms.budget, Encoding.encodeList]; omega
  | cons x xs ih =>
    simp only [RecordPrograms.budget, cost, Encoding.length_encodeList_cons, id_eq]
    nlinarith

theorem scan_eval (F : Formula) (H : Clause) (acc : List (List Bool)) (regs : Regs) :
    ∃ n ≤ 160 * ((encodeClause H).length + 1) * ((encodeFormula F).length + 1),
      ∃ rf : Regs, Eval scan n
        (state regs (encodeFormula F) [] (Encoding.encodeList id acc) [] (encodeClause H))
        (state rf [] [] (Encoding.encodeList id
          ((ExecClauseFiltersProgram.formulaRecords (petals F H)).reverse ++ acc)) [] (encodeClause H)) := by
  let d := state regs (encodeFormula F) [] (Encoding.encodeList id acc) [] (encodeClause H)
  obtain ⟨n, next, hn, hnext, hhistory, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (cost H) (invariant H) (Effect H)
    ExecClauseFiltersProgram.ClausePayload (callback_contract H)
    (ExecClauseFiltersProgram.formulaRecords F) [] d
    (ExecClauseFiltersProgram.valid_formulaRecords F) ⟨regs, _, _, [], rfl⟩
    (regs 10) (regs 11) (regs 12)
  have hout := visits_result H hhistory acc (show d.stacks 2 = _ from rfl)
  obtain ⟨rf, source, output, payload, rfl⟩ := hnext
  have hout' : output = Encoding.encodeList id
      ((ExecClauseFiltersProgram.formulaRecords (petals F H)).reverse ++ acc) := by
    simpa [state, records_map] using hout
  have hany : (ExecClauseFiltersProgram.formulaRecords F).any (fun _ => false) = false := by simp
  refine ⟨n, hn.trans ?_, flags rf false true false, ?_⟩
  · simpa only [← ExecClauseFiltersProgram.encodeFormula_records] using
      budget_le H (ExecClauseFiltersProgram.formulaRecords F)
  · simpa only [d, List.append_nil, record_state, flags_self,
      ← ExecClauseFiltersProgram.encodeFormula_records, hany,
      SubexpNormalizeProgram.unread_false, hout'] using he

theorem pushOutput_eval (regs : Regs) (source output core : List Bool) :
    Eval pushOutput 2 (state regs source [] output [] core)
      (state (Function.update regs 0 false) source [] (false :: output) [] core) := by
  have h := Eval.seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 13) (s := 12) 0 false)
      (state regs source [] output [] core)))
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 13) (s := 12) 2 0)
      ((StructuredProgram.Atom.set 0 false).eval (state regs source [] output [] core))))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [state, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
 StructuredProgram.State.ofCfg, execInstr]

theorem command_eval (F : Formula) (H : Clause) (regs : Regs) :
    ∃ n ≤ 160 * ((encodeClause H).length + 1) * ((encodeFormula F).length + 1) + 2,
      ∃ rf : Regs, Eval command n
        (state regs (encodeFormula F) [] [] [] (encodeClause H))
        (state rf [] [] (Encoding.encodeList id
          (ExecClauseFiltersProgram.formulaRecords (petals F H)).reverse) [] (encodeClause H)) := by
  obtain ⟨n, hn, rf, he⟩ := scan_eval F H [] (Function.update regs 0 false)
  simp only [List.append_nil] at he
  exact ⟨2 + n, by omega, rf, (pushOutput_eval regs _ [] _).seq he⟩

theorem program_runsIn (F : Formula) (H : Clause) (regs : Regs) :
    ∃ rf : Regs, RunsIn program
      (170 * ((encodeClause H).length + 1) * ((encodeFormula F).length + 1))
      ((state regs (encodeFormula F) [] [] [] (encodeClause H)).withPC (some program.entry))
      ((state rf [] [] (Encoding.encodeList id
        (ExecClauseFiltersProgram.formulaRecords (petals F H)).reverse) [] (encodeClause H)).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval F H regs
  exact ⟨rf, n + 1, by nlinarith, compiled_halt_trace he 0 2⟩

end SubexponentialSAT.ExecPetalFamilyProgram

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

theorem familyReg_injective : Function.Injective familyReg := Fin.castAdd_injective 13 2
theorem familyStack_injective : Function.Injective familyStack := by decide

theorem familyCall_eval_oai (selected : Formula) (H : Clause) (regs : Regs)
    (master parent : List Bool) :
    ∃ n ≤ 170 * ((encodeClause H).length + 1) * ((encodeFormula selected).length + 1),
      ∃ rf : Regs, Eval familyCall n
        (frame regs (encodeFormula selected) (encodeClause H) master parent [])
        (frame rf [] (encodeClause H) master parent
          (Encoding.encodeList id (formulaRecords (ExecPetalFamilyProgram.petals selected H)).reverse)) := by
  let d := frame regs (encodeFormula selected) (encodeClause H) master parent []
  obtain ⟨rf, n, hn, ht⟩ := ExecPetalFamilyProgram.program_runsIn selected H (regs ∘ familyReg)
  let a := ExecPetalFamilyProgram.state (regs ∘ familyReg) (encodeFormula selected) [] [] [] (encodeClause H)
  let b := ExecPetalFamilyProgram.state rf [] []
    (Encoding.encodeList id (formulaRecords (ExecPetalFamilyProgram.petals selected H)).reverse) [] (encodeClause H)
  have hstart : embedState familyReg familyStack d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ familyReg_injective familyStack_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have he := eval_call_lifted ExecPetalFamilyProgram.program familyReg familyStack d
    familyReg_injective familyStack_injective ht
  change Eval familyCall n (embedState familyReg familyStack d a)
    (embedState familyReg familyStack d b) at he
  rw [hstart] at he
  let e := embedState familyReg familyStack d b
  have hs (i : Fin 12) : e.stacks (familyStack i) = b.stacks i :=
    embedState_stack _ _ _ _ familyStack_injective i
  have h10 : e.stacks 10 = [] := embedState_stack_frame _ _ _ _ _ (by decide)
  have h11 : e.stacks 11 = [] := embedState_stack_frame _ _ _ _ _ (by decide)
  have h12 : e.stacks 12 = master := embedState_stack_frame _ _ _ _ _ (by decide)
  have h13 : e.stacks 13 = parent := embedState_stack_frame _ _ _ _ _ (by decide)
  have heq : e = frame e.regs [] (encodeClause H) master parent
      (Encoding.encodeList id (formulaRecords (ExecPetalFamilyProgram.petals selected H)).reverse) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i
    · exact hs 0
    · exact hs 3
    · exact hs 4
    · exact hs 5
    · exact hs 6
    · exact hs 7
    · exact hs 8
    · exact hs 9
    · exact hs 10
    · exact hs 11
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact hs 2
    · exact hs 1
  exact ⟨n, hn, e.regs, heq ▸ he⟩

end SubexponentialSAT.ExecPetalChildProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.familyCall_eval_oai := @OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.familyCall_eval_oai
