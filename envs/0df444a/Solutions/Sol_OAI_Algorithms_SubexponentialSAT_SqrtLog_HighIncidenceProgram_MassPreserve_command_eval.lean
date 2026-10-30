-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:25:17.846637+00:00
-- url     : https://prove2.me/submissions/3feb0911-2007-4715-9abd-b6cfddd2b036

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S060
import Definitions.Def_OAIQ081S061
import Definitions.Def_OAIQ081S076
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S085

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem encodeList_injective {α : Type*} {enc : α → List Bool}
    (hinj : Function.Injective enc) : Function.Injective (encodeList enc) := by
  intro as
  induction as with
  | nil =>
      intro bs h
      cases bs <;> simp_all [encodeList]
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => simp [encodeList] at h
      | cons b bs =>
          have ht : frame (enc a) ++ encodeList enc as =
              frame (enc b) ++ encodeList enc bs := by
            simpa only [encodeList, List.cons.injEq, true_and] using h
          obtain ⟨hab, htail⟩ := frame_append_injective ht
          exact congrArg₂ List.cons (hinj hab) (ih htail)

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramRecords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured physical folds over sparse-hash records

This module specializes the audited framed-record iterator to an accumulator
fold which visits every record. The callback is an actual finite `Cmd`; its
local execution contract remains explicit. `foldProgram_run` concerns primitive
Boolean-register/stack transitions, not an operation counter or semantic oracle.
The same program shape handles clause-literal products, sparse weighted sums,
coefficient-array maps, and support-key dictionary scans.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {r s : ℕ} {A : Type*}

theorem visits_fold (read : State r s → A) (step : List Bool → A → A)
    {records : List (List Bool)} {before after : State r s}
    (h : Visits (fun _ => false) (foldEffect read step) records before after) :
    read after = records.foldl (fun a bits => step bits a) (read before) := by
  induction h with
  | nil base => rfl
  | hit ht _ => cases ht
  | miss _ he _ ih =>
      simpa only [List.foldl_cons, foldEffect] using ih.trans (congrArg
        (fun a => List.foldl (fun a bits => step bits a) a _) he)

theorem foldCommand_run (ports : Ports r s) (callback : Cmd r s)
    (read : State r s → A) (step : List Bool → A → A)
    (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (validPayload : List Bool → Prop)
    (contract : FoldContract ports callback read step cost invariant validPayload)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (hrecords : ∀ bits ∈ records, validPayload bits) (hbase : invariant base)
    (v pr f : Bool) :
    ∃ n next, n ≤ 3 + budget cost records ∧ invariant next ∧
      read next = records.foldl (fun a bits => step bits a) (read base) ∧
      Eval (foldCommand ports callback) n
        (state ports base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state ports next false true false suffix []) := by
  obtain ⟨n, next, hn, hnext, hhistory, hrun⟩ :=
    iterate_run_with_on ports callback (fun _ => false) cost invariant
      (foldEffect read step) validPayload contract records suffix base hrecords hbase v pr f
  refine ⟨n, next, hn, hnext, visits_fold read step hhistory, ?_⟩
  simpa [foldCommand] using hrun

/-- The program has a fixed finite instruction table. Its actual trace bound
includes parsing and the final halt; the callback bounds remain explicit. -/
theorem foldProgram_run (ports : Ports r s) (callback : Cmd r s)
    (read : State r s → A) (step : List Bool → A → A)
    (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (validPayload : List Bool → Prop)
    (contract : FoldContract ports callback read step cost invariant validPayload)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (hrecords : ∀ bits ∈ records, validPayload bits) (hbase : invariant base)
    (v pr f : Bool) :
    ∃ next, invariant next ∧
      read next = records.foldl (fun a bits => step bits a) (read base) ∧
      RunsIn (foldProgram ports callback) (4 + budget cost records)
        ((state ports base v pr f (Encoding.encodeList id records ++ suffix) []).withPC
          (some (foldProgram ports callback).entry))
        ((state ports next false true false suffix []).withPC none) := by
  obtain ⟨n, next, hn, hnext, hvalue, hrun⟩ :=
    foldCommand_run ports callback read step cost invariant validPayload contract
      records suffix base hrecords hbase v pr f
  exact ⟨next, hnext, hvalue, n + 1, by omega,
    compiled_halt_trace hrun ports.source ports.source⟩

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual two-level record scan counting explicit scope entries. The ghost
payload decoder occurs only in the loop specification; the executable callback
uses the existing physical record counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem parser_state (regs : Fin 5 → Bool) (s p a w src pay : List Bool) (t pr f : Bool) :
    RecordPrograms.state ports (state regs s p a w) t pr f src pay =
      state (parserRegs regs t pr f) src pay a w := by
  apply congrArg (StructuredProgram.State.mk _)
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _
theorem counterPorts_injective : Function.Injective counterPorts := by decide

theorem counter_eval (regs : Fin 5 → Bool) (records : List (List Bool)) (source acc : List Bool) :
    ∃ rf, Eval counter (SubexpSunflowerProgram.CountRecords.loopSteps records)
      (state regs source [] acc (encode records))
      (state rf source [] (List.replicate records.length true ++ acc) []) ∧
      (∀ i : Fin 5, 2 ≤ i.val → rf i = regs i) := by
  let a := state regs source [] acc (encode records)
  let out : State 2 2 := ⟨ParserProgram.pair false false,
    ParserProgram.pair [] (List.replicate records.length true ++ acc)⟩
  have ht := SubexpSunflowerProgram.CountRecords.loop_trace records [] acc (regs 0) (regs 1)
  simp only [List.append_nil] at ht
  have hp : projectState registers counterPorts a =
      (⟨ParserProgram.pair (regs 0) (regs 1), ParserProgram.pair (encode records) acc⟩ : State 2 2) := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have ht' : Trace SubexpScopeCountSetup.counterProgram (SubexpSunflowerProgram.CountRecords.loopSteps records)
      ((projectState registers counterPorts a).withPC (some SubexpScopeCountSetup.counterProgram.entry))
      (out.withPC none) := by
    rw [hp]
    exact ht
  let b := embedState registers counterPorts a out
  have he := eval_call_from_state SubexpScopeCountSetup.counterProgram registers counterPorts a
    registers_injective counterPorts_injective ht'
  have hs (i : Fin 2) : b.stacks (counterPorts i) = out.stacks i :=
    embedState_stack _ _ _ _ counterPorts_injective i
  have hb : b = state b.regs source [] (List.replicate records.length true ++ acc) [] := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i
    fin_cases i
    · exact embedState_stack_frame registers counterPorts a out 0 (by decide)
    · exact embedState_stack_frame registers counterPorts a out 1 (by decide)
    · exact hs 1
    · exact hs 0
  refine ⟨b.regs, ?_, ?_⟩
  · change Eval counter _ a b at he
    rw [hb] at he
    exact he
  · intro i hi
    exact embedState_register_frame registers counterPorts a out i (by
      rintro ⟨j, hj⟩
      fin_cases j <;> subst i <;> simp [registers] at hi)

theorem callback_eval (regs : Fin 5 → Bool) (records : List (List Bool)) (source acc : List Bool) :
    ∃ rf, Eval callback
      (3 * (encode records).length + 3 + SubexpSunflowerProgram.CountRecords.loopSteps records)
      (state regs source (encode records).reverse acc [])
      (state rf source [] (List.replicate records.length true ++ acc) []) ∧
      (∀ i : Fin 5, 2 ≤ i.val → rf i = regs i) := by
  let r := readRegs regs 0 1 none
  have htransfer : Eval transfer (3 * (encode records).length + 3)
      (state regs source (encode records).reverse acc [])
      (state r source [] acc (encode records)) := by
    have h := ListRegisterProgram.transfer_run (1 : Fin 4) 3 (0 : Fin 5) 1
      (by decide) (by decide) regs (state regs source (encode records).reverse acc []).stacks
    have hs : StackRoutines.transferStacks 1 3
        (state regs source (encode records).reverse acc []).stacks =
        (state r source [] acc (encode records)).stacks := by
      funext i
      fin_cases i <;> simp [state, StackRoutines.transferStacks]
    apply Eval.call
    change Trace (StackRoutines.transferProgram 1 3 0 1) _
      ((state regs source (encode records).reverse acc []).withPC
        (some (StackRoutines.transferProgram 1 3 0 1).entry))
      ((⟨r, StackRoutines.transferStacks 1 3
        (state regs source (encode records).reverse acc []).stacks⟩ : Data).withPC none) at h
    rw [hs] at h
    simpa [state] using h
  obtain ⟨rf, hc, hr⟩ := counter_eval r records source acc
  refine ⟨rf, htransfer.seq hc, ?_⟩
  intro i hi
  rw [hr i hi]
  have h0 : i ≠ 0 := by intro h; subst i; contradiction
  have h1 : i ≠ 1 := by intro h; subst i; contradiction
  first | (simp [r, readRegs, h0, h1, -OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status_read]) | (simp [r, readRegs, h0, h1])

theorem payloadCount_encode (records : List (List Bool)) :
    payloadCount (encode records) = records.length := by
  classical
  unfold payloadCount
  split
  · rename_i h
    exact congrArg List.length (Encoding.encodeList_injective Function.injective_id
      (Classical.choose_spec h))
  · rename_i h
    exact (h ⟨records, rfl⟩).elim

theorem callback_contract : LeafProgram.FoldContract ports callback read update
    (fun bits => 6 * bits.length + 5) invariant (fun bits => ∃ rs, encode rs = bits) := by
  rintro bits tail base ⟨records, rfl⟩ ⟨regs, acc, rfl⟩
  obtain ⟨rf, he, hr⟩ := callback_eval (parserRegs regs false true false) records tail acc
  have h2 : rf 2 = false := by simpa [parserRegs] using hr 2 (by decide)
  have h3 : rf 3 = true := by simpa [parserRegs] using hr 3 (by decide)
  have h4 : rf 4 = false := by simpa [parserRegs] using hr 4 (by decide)
  have hreset : parserRegs rf false true false = rf := by
    funext i
    fin_cases i <;> simp [parserRegs, h2, h3, h4]
  refine ⟨3 * (encode records).length + 3 + SubexpSunflowerProgram.CountRecords.loopSteps records,
    state rf [] [] (List.replicate records.length true ++ acc) [], ?_,
    ⟨rf, _, rfl⟩, ?_, ?_⟩
  · have h := SubexpSunflowerProgram.CountRecords.steps_le_encoded records
    dsimp [SubexpSunflowerProgram.CountRecords.steps] at h
    change 3 * (Encoding.encodeList id records).length + 3 +
      SubexpSunflowerProgram.CountRecords.loopSteps records ≤
      6 * (Encoding.encodeList id records).length + 5
    omega
  · simp [LeafProgram.foldEffect, read, update, payloadCount_encode, state]
  · rw [parser_state, parser_state, hreset]
    exact he

theorem fold_update (records : List (List (List Bool))) (acc : List Bool) :
    (records.map encode).foldl (fun a bits => update bits a) acc =
      List.replicate ((records.map List.length).sum) true ++ acc := by
  induction records generalizing acc with
  | nil => simp
  | cons rs rss ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [ih]
      simp only [update, payloadCount_encode, List.sum_cons]
      rw [Nat.add_comm rs.length, List.replicate_add, List.append_assoc]

theorem program_runsIn (regs : Fin 5 → Bool) (records : List (List (List Bool))) :
    ∃ rf, RunsIn program
      (4 + RecordPrograms.budget (fun bits => 6 * bits.length + 5) (records.map encode))
      ((RecordPrograms.state ports (state regs [] [] [] []) false true false
        (encode (records.map encode)) []).withPC (some program.entry))
      ((state rf [] [] (List.replicate ((records.map List.length).sum) true) []).withPC none) := by
  obtain ⟨next, hn, hv, he⟩ := LeafProgram.foldProgram_run ports callback read update
    (fun bits => 6 * bits.length + 5) invariant (fun bits => ∃ rs, encode rs = bits)
    callback_contract (records.map encode) [] (state regs [] [] [] [])
    (by intro bits hb; obtain ⟨rs, _, rfl⟩ := List.mem_map.mp hb; exact ⟨rs, rfl⟩)
    ⟨regs, [], rfl⟩ false true false
  obtain ⟨rf, acc, rfl⟩ := hn
  have hacc : acc = List.replicate ((records.map List.length).sum) true := by
    simpa [read, state, fold_update] using hv
  subst acc
  refine ⟨parserRegs rf false true false, ?_⟩
  simpa only [List.append_nil, parser_state, program] using he

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMassBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Serialized scope adapter and complete bit cost for the nested counter.
The counter counts supplied entries; the caller's normalization invariant is
what identifies this with distinct factor-variable incidence mass. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem encode_map_nat (xs : List ℕ) :
    encode (xs.map Encoding.encodeNat) = Encoding.encodeList Encoding.encodeNat xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, encode, Encoding.encodeList, id_eq, ih]

theorem encoded_scopeRecords (scopes : List (List ℕ)) :
    encode ((scopeRecords scopes).map encode) = SubexpIncidenceSlotProgram.scopeBits scopes := by
  induction scopes with
  | nil => rfl
  | cons xs xss ih =>
      simpa only [scopeRecords, List.map_cons, encode, Encoding.encodeList,
        id_eq, encode_map_nat, SubexpIncidenceSlotProgram.scopeBits,
        SubexpIncidenceSlotProgram.scopeBytes, SubexpIncidencePlanScan.scopeBytes] using
        congrArg (fun tail => true :: (Encoding.frame
          (Encoding.encodeList Encoding.encodeNat xs) ++ tail)) ih

theorem scopeRecords_mass (scopes : List (List ℕ)) :
    ((scopeRecords scopes).map List.length).sum = (scopes.map List.length).sum := by
  simp [scopeRecords, List.map_map, Function.comp_def]

theorem budget_le_input (records : List (List (List Bool))) :
    4 + RecordPrograms.budget (fun bits => 6 * bits.length + 5) (records.map encode) ≤
      28 * ((encode (records.map encode)).length + 1) := by
  exact RecordPrograms.program_budget_le_input _ _ 6 5 (by intros; rfl)

/-- The supplied nested Nat scopes are scanned, including every empty scope.
No externally supplied mass occurs in either the program or its input. -/
theorem scopes_runsIn (regs : Fin 5 → Bool) (scopes : List (List ℕ)) :
    ∃ rf, RunsIn program
      (28 * ((SubexpIncidenceSlotProgram.scopeBits scopes).length + 1))
      ((RecordPrograms.state ports (state regs [] [] [] []) false true false
        (SubexpIncidenceSlotProgram.scopeBits scopes) []).withPC (some program.entry))
      ((state rf [] [] (List.replicate ((scopes.map List.length).sum) true) []).withPC none) := by
  obtain ⟨rf, hr⟩ := program_runsIn regs (scopeRecords scopes)
  refine ⟨rf, ?_⟩
  have hb := budget_le_input (scopeRecords scopes)
  simpa only [encoded_scopeRecords, scopeRecords_mass] using hr.mono hb

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMassPreserve
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving wrapper around the actual nested record counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem regs_injective : Function.Injective regs := Fin.castAdd_injective _ _
theorem stackPorts_injective : Function.Injective stackPorts := by decide

theorem reset_eval (d : Data) :
    Eval reset 3 d ⟨resetRegs d.regs, d.stacks⟩ :=
  (Eval.base (.atom _ _)).seq ((Eval.base (.atom _ _)).seq (Eval.base (.atom _ _)))

theorem command_eval_oai (r : Fin 8 → Bool) (scopes : List (List ℕ)) :
    ∃ time rf, Eval command time
      (state r (SubexpIncidenceSlotProgram.scopeBits scopes) [])
      (state rf (SubexpIncidenceSlotProgram.scopeBits scopes)
        (List.replicate ((scopes.map List.length).sum) true)) ∧
      time + 1 ≤ bound (SubexpIncidenceSlotProgram.scopeBits scopes) := by
  let source := SubexpIncidenceSlotProgram.scopeBits scopes
  let a := state r source []
  let copied := ArithmeticCalls.afterCopy 0 4 a
  let ready : Data := ⟨resetRegs copied.regs, copied.stacks⟩
  have hc := ArithmeticCalls.copyAt_eval (0 : Fin 5) 4 3 a
    (by decide) (by decide) (by decide) (by rfl) (by rfl)
  have hp : projectState regs stackPorts ready =
      RecordPrograms.state Mass.ports (Mass.state (ready.regs ∘ regs) [] [] [] [])
        false true false source [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨rf, time, ht, he⟩ := Mass.scopes_runsIn (ready.regs ∘ regs) scopes
  rw [← hp] at he
  let out := Mass.state rf [] [] (List.replicate ((scopes.map List.length).sum) true) []
  let b := embedState regs stackPorts ready out
  have hm := eval_call_from_state Mass.program regs stackPorts ready
    regs_injective stackPorts_injective he
  have hs (i : Fin 4) : b.stacks (stackPorts i) = out.stacks i :=
    embedState_stack _ _ _ _ stackPorts_injective i
  have hb : b = state b.regs source (List.replicate ((scopes.map List.length).sum) true) := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i
    fin_cases i
    · exact embedState_stack_frame regs stackPorts ready out 0 (by decide)
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hs 0
  change Eval _ _ ready b at hm
  rw [hb] at hm
  refine ⟨(7 * source.length + 5) + (3 + time), b.regs,
    hc.seq ((reset_eval copied).seq hm), ?_⟩
  dsimp [bound, source]
  omega

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve.command_eval_oai
