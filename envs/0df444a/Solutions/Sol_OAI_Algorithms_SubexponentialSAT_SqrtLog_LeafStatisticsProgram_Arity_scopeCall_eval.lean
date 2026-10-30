-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.scopeCall_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:56:26.079996+00:00
-- url     : https://prove2.me/submissions/cca1c6a3-498e-46a3-94b3-6946861ab94c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S110

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native bit lookup at a unary index. The mask source is preserved. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem popIndex_eval (r : Fin 4 → Bool) (mask index scan tmp saved : List Bool) :
    Eval popIndex 1 (state r mask index scan tmp saved)
      (popped r mask index scan tmp saved) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 5) 0 1)
    (state r mask index scan tmp saved))) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (StructuredProgram.State.mk _)
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem popScan_eval (r : Fin 4 → Bool) (mask index scan tmp saved : List Bool) :
    Eval popScan 1 (state r mask index scan tmp saved)
      (state (readRegs r 2 3 scan.head?) mask index scan.tail tmp saved) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 5) 2 3)
    (state r mask index scan tmp saved))) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (StructuredProgram.State.mk _)
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem loop_eval (r : Fin 4 → Bool) (mask before after tmp saved : List Bool) :
    ∃ rf, Eval loop (3 * before.length + 1)
      (popped r mask (unary before.length) (before ++ after) tmp saved)
      (state rf mask [] after tmp saved) := by
  induction before generalizing r with
  | nil =>
      exact ⟨readRegs r 0 1 none, Eval.while_false (by rfl)⟩
  | cons b before ih =>
      let r1 := readRegs r 0 1 (some true)
      let r2 := readRegs r1 2 3 (some b)
      obtain ⟨rf, he⟩ := ih r2
      refine ⟨rf, ?_⟩
      have hb : Eval body 2
          (popped r mask (unary (b::before).length) ((b::before) ++ after) tmp saved)
          (popped r2 mask (unary before.length) (before ++ after) tmp saved) := by
        exact (popScan_eval r1 mask (unary before.length) (b::(before++after)) tmp saved).seq
          (popIndex_eval r2 mask (unary before.length) (before++after) tmp saved)
      have hh := Eval.while_true (show
        (popped r mask (unary (b::before).length) ((b::before) ++ after) tmp saved).regs 1 = true by rfl) hb he
      convert hh using 1 ; simp [List.length_cons] ; omega

theorem skip_eval (r : Fin 4 → Bool) (mask before after tmp saved : List Bool) :
    ∃ rf, Eval skip (3 * before.length + 2)
      (state r mask (unary before.length) (before ++ after) tmp saved)
      (state rf mask [] after tmp saved) := by
  obtain ⟨rf, he⟩ := loop_eval r mask before after tmp saved
  refine ⟨rf, ?_⟩
  convert (popIndex_eval r mask (unary before.length) (before++after) tmp saved).seq he using 1 ; omega

theorem copy_eval (r : Fin 4 → Bool) (mask index saved : List Bool) :
    Eval copy (7 * mask.length + 5) (state r mask index [] [] saved)
      (state (readRegs r 0 1 none) mask index mask [] saved) := by
  apply Eval.call
  convert (ListRegisterProgram.copy_run (0 : Fin 5) 2 3 (0 : Fin 4) 1
    (by decide) (by decide) (by decide) (by decide) r
    (state r mask index [] [] saved).stacks (by rfl)) using 1
  · simp []
  · change Cfg.mk none _ _ = Cfg.mk none _ _
    congr 1
    funext i; fin_cases i <;> simp [ StackRoutines.copyStacks]

theorem clear_eval (r : Fin 4 → Bool) (mask scan saved : List Bool) :
    Eval clear (2 * scan.length + 3) (state r mask [] scan [] saved)
      (state (readRegs r 0 1 none) mask [] [] [] saved) := by
  have h := StackRoutines.clearProgram_trace (2 : Fin 5) (0 : Fin 4) 1 r
    (state r mask [] scan [] saved).stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  convert hh using 1
  · simp []
  · simp [ StackRoutines.clearResult,
      StackRoutines.clearStacks, StructuredProgram.State.withPC ]
    first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem command_eval (r : Fin 4 → Bool) (before after saved : List Bool) (bit : Bool) :
    ∃ rf, rf 2 = bit ∧ Eval command
      (7 * (before.length + 1 + after.length) + 3 * before.length + 2 * after.length + 11)
      (state r (before ++ bit::after) (unary before.length) [] [] saved)
      (state rf (before ++ bit::after) [] [] [] saved) := by
  let mask := before ++ bit::after
  let r1 := readRegs r 0 1 none
  obtain ⟨r2, hs⟩ := skip_eval r1 mask before (bit::after) [] saved
  let r3 := readRegs r2 2 3 (some bit)
  let rf := readRegs r3 0 1 none
  refine ⟨rf, by simp [rf,r3,readRegs], ?_⟩
  have h := (copy_eval r mask (unary before.length) saved).seq
    (hs.seq ((popScan_eval r2 mask [] (bit::after) [] saved).seq (clear_eval r3 mask after saved)))
  convert h using 1 ; simp [mask,List.length_append,List.length_cons] ; omega

theorem program_runsIn (r : Fin 4 → Bool) (before after saved : List Bool) (bit : Bool) :
    ∃ rf, rf 2 = bit ∧ RunsIn program
      (12 * (before.length + 1 + after.length) + 12)
      ((state r (before ++ bit::after) (unary before.length) [] [] saved).withPC (some program.entry))
      ((state rf (before ++ bit::after) [] [] [] saved).withPC none) := by
  obtain ⟨rf,hb,he⟩ := command_eval r before after saved bit
  exact ⟨rf,hb,_,by omega,compiled_halt_trace he 0 2⟩

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual preserving scope-record count and assignment-fuel setup.
The scope and base remain on stacks 1 and 0. The program returns unary arity,
binary exponent, and binary base^arity on stacks 2, 3, and 4. -/

namespace SubexponentialSAT.SubexpScopeCountSetup

open BitProgram StructuredCalls

/-- The scope representation used by the clause producer is exactly the
generic framed-record representation consumed by this program. -/
theorem encode_scope (scope : List ℕ) :
    Encoding.encodeList id (scope.map Encoding.encodeNat) =
      Encoding.encodeList Encoding.encodeNat scope := by
  induction scope with
  | nil => rfl
  | cons j scope ih => simp [Encoding.encodeList, ih]

end SubexponentialSAT.SubexpScopeCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count precisely the unpinned identifiers in an explicit scope. The mask is
in original coordinate order and the framed natural identifiers are read at
runtime. No arity or other statistic is supplied as an input. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem parser_state (r : Fin 7 → Bool) (mask acc source payload src pay : List Bool)
    (t p f : Bool) :
    RecordPrograms.state ports (state r mask [] [] [] acc source payload) t p f src pay =
      state (parserRegs r t p f) mask [] [] [] acc src pay := by
  apply congrArg (StructuredProgram.State.mk _)
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem lookupRegs_injective : Function.Injective lookupRegs := Fin.castAdd_injective _ _
theorem lookupStacks_injective : Function.Injective lookupStacks := Fin.castAdd_injective _ _

theorem lookup_eval (r : Fin 7 → Bool) (mask : List Bool) (v : ℕ) (hv : v < mask.length)
    (acc source : List Bool) :
    ∃ n rf, n ≤ 12*mask.length+12 ∧ rf 2 = mask[v] ∧
      (∀ i : Fin 7, 4 ≤ i.val → rf i = r i) ∧
      Eval lookup n (state r mask (unary v) [] [] acc source [])
        (state rf mask [] [] [] acc source []) := by
  let before := mask.take v
  let after := mask.drop (v+1)
  have hlen : before.length = v := by simp [before,Nat.min_eq_left hv.le]
  have hsplit : before ++ mask[v]::after = mask := by
    have h := List.take_append_drop v mask
    rw [List.drop_eq_getElem_cons hv] at h
    exact h
  obtain ⟨rs,hbit,n,hn,ht⟩ := Lookup.program_runsIn (r ∘ lookupRegs) before after acc mask[v]
  let a := state r mask (unary v) [] [] acc source []
  let b := Lookup.state rs mask [] [] [] acc
  have hp : projectState lookupRegs lookupStacks a =
      Lookup.state (r ∘ lookupRegs) (before ++ mask[v]::after) (unary before.length) [] [] acc := by
    rw [hsplit,hlen]
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [← hp,hsplit] at ht
  have he := eval_call_from_state Lookup.program lookupRegs lookupStacks a
    lookupRegs_injective lookupStacks_injective (b := b) ht
  let e := embedState lookupRegs lookupStacks a b
  have heq : e = state e.regs mask [] [] [] acc source [] := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i
    · exact embedState_stack lookupRegs lookupStacks a b lookupStacks_injective 0
    · exact embedState_stack lookupRegs lookupStacks a b lookupStacks_injective 1
    · exact embedState_stack lookupRegs lookupStacks a b lookupStacks_injective 2
    · exact embedState_stack lookupRegs lookupStacks a b lookupStacks_injective 3
    · exact embedState_stack lookupRegs lookupStacks a b lookupStacks_injective 4
    · exact embedState_stack_frame lookupRegs lookupStacks a b _ (by decide)
    · exact embedState_stack_frame lookupRegs lookupStacks a b _ (by decide)
  refine ⟨n,e.regs,?_,?_,?_,?_⟩
  · have hm : before.length + 1 + after.length = mask.length := by
      have := congrArg List.length hsplit
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using this
    simpa [hm] using hn
  · exact (embedState_register lookupRegs lookupStacks a b lookupRegs_injective 2).trans hbit
  · intro i hi
    exact embedState_register_frame lookupRegs lookupStacks a b i (by
      rintro ⟨j,hj⟩
      have he : j.val = i.val := congrArg Fin.val hj
      have hlt := j.isLt
      omega)
  · change Eval lookup n a e at he
    rw [heq] at he
    exact he

theorem callback_eval (r : Fin 7 → Bool) (mask : List Bool) (v : ℕ)
    (hv : v < mask.length) (acc source : List Bool) :
    ∃ n rf, n ≤ 16*(mask.length+1) ∧
      (∀ i : Fin 7, 4 ≤ i.val → rf i = r i) ∧
      Eval callback n (state r mask [] [] [] acc source (Encoding.encodeNat v).reverse)
        (state rf mask [] [] [] (if mask[v] then acc else true::acc) source []) := by
  let r1 := readRegs r 0 1 (some false)
  let r2 := readRegs r1 0 1 none
  have hdrop : Eval dropTag 1
      (state r mask [] [] [] acc source (Encoding.encodeNat v).reverse)
      (state r1 mask [] [] [] acc source (unary v)) := by
    have h := Eval.base (StructuredProgram.Eval.atom (.pop (6 : Fin 7) 0 1)
      (state r mask [] [] [] acc source (Encoding.encodeNat v).reverse))
    convert h using 1
    · rfl
    · apply congrArg₂ StructuredProgram.State.mk
      · funext i
        fin_cases i <;> simp [r1, state, Encoding.encodeNat, List.reverse_append,
          List.reverse_replicate,
          StructuredProgram.Atom.instr, execInstr]
      · funext i
        fin_cases i <;> simp [state, unary, Encoding.encodeNat, List.reverse_append,
          List.reverse_replicate, StructuredProgram.Atom.instr, execInstr]
  have htransfer : Eval transfer (3*v+3)
      (state r1 mask [] [] [] acc source (unary v))
      (state r2 mask (unary v) [] [] acc source []) := by
    apply Eval.call
    convert (ListRegisterProgram.transfer_run (6 : Fin 7) 1 (0 : Fin 7) 1
      (by decide) (by decide) r1 (state r1 mask [] [] [] acc source (unary v)).stacks) using 1 <;>
      simp [r2,state,unary,StackRoutines.transferStacks,List.reverse_replicate]
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨nl,rl,hnl,hbit,hframe,hl⟩ := lookup_eval r2 mask v hv acc source
  let a := state rl mask [] [] [] acc source []
  have hchoose : ∃ nc rf, nc ≤ 3 ∧ (∀ i : Fin 7, 4 ≤ i.val → rf i = rl i) ∧
      Eval choose nc a (state rf mask [] [] [] (if mask[v] then acc else true::acc) source []) := by
    cases hb : mask[v] with
    | true =>
      refine ⟨1,rl,by omega,fun i hi => rfl,?_⟩
      apply Eval.ite_true
      · change rl 2 = true
        simpa only [hb] using hbit
      · exact Eval.base (StructuredProgram.Eval.skip a)
    | false =>
      let rf := Function.update rl 0 true
      refine ⟨3,rf,by omega,?_,?_⟩
      · intro i hi
        have h0 : i ≠ 0 := by intro h; subst i; contradiction
        simp [rf,h0]
      · apply Eval.ite_false (by
          change rl 2 = false
          simpa only [hb] using hbit)
        have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 7) true) a)).seq
          (Eval.base (StructuredProgram.Eval.atom (.push (4 : Fin 7) 0) _))
        convert h using 1
        · rfl
        · apply congrArg (StructuredProgram.State.mk _)
          funext i
          fin_cases i <;>
            simp [a,state,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
              StructuredProgram.State.ofCfg,execInstr]
  obtain ⟨nc,rf,hnc,hrf,hc⟩ := hchoose
  refine ⟨1+(3*v+3)+(nl+nc),rf,by omega,?_,?_⟩
  · intro i hi
    rw [hrf i hi,hframe i hi]
    have h0 : i ≠ 0 := by intro h; subst i; contradiction
    have h1 : i ≠ 1 := by intro h; subst i; contradiction
    simp [r2,r1,readRegs,h0,h1]
  · have h := hdrop.seq (htransfer.seq (hl.seq hc))
    simpa only [callback, Nat.add_assoc] using h

theorem callback_contract (mask : List Bool) :
    LeafProgram.FoldContract ports callback read (update mask)
      (fun _ => 16*(mask.length+1)) (invariant mask)
      (fun bits => ∃ v, v < mask.length ∧ Encoding.encodeNat v = bits) := by
  rintro bits tail base ⟨v,hv,rfl⟩ ⟨r,acc,rfl⟩
  obtain ⟨n,rf,hn,hframe,he⟩ := callback_eval (parserRegs r false true false) mask v hv acc tail
  have h4 : rf 4 = false := by simpa [parserRegs] using hframe 4 (by decide)
  have h5 : rf 5 = true := by simpa [parserRegs] using hframe 5 (by decide)
  have h6 : rf 6 = false := by simpa [parserRegs] using hframe 6 (by decide)
  have hreset : parserRegs rf false true false = rf := by
    funext i; fin_cases i <;> simp [parserRegs,h4,h5,h6]
  refine ⟨n,state rf mask [] [] [] (if mask[v] then acc else true::acc) [] [],hn,
    ⟨rf,_,rfl⟩,?_,?_⟩
  · cases hb : mask[v] <;>
      simp [LeafProgram.foldEffect,read,update,low,List.getElem?_eq_getElem hv,state,hb]
  · rw [parser_state,parser_state,hreset]
    exact he

theorem fold_update (mask : List Bool) (scope : List ℕ) (acc : List Bool) :
    (scope.map Encoding.encodeNat).foldl (fun a b => update mask b a) acc =
      unary (scope.filter (low mask)).length ++ acc := by
  induction scope generalizing acc with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [ih]
    simp only [update,decoded_encode]
    by_cases h : low mask v = true
    · simp [h,unary,List.replicate_succ',List.append_assoc]
    · simp [h,unary]

theorem program_runsIn (r : Fin 7 → Bool) (mask : List Bool) (scope : List ℕ)
    (hv : ∀ v ∈ scope, v < mask.length) :
    ∃ rf, RunsIn program
      (4 + RecordPrograms.budget (fun _ => 16*(mask.length+1)) (scope.map Encoding.encodeNat))
      ((RecordPrograms.state ports (state r mask [] [] [] [] [] []) false true false
        (Encoding.encodeList Encoding.encodeNat scope) []).withPC (some program.entry))
      ((state rf mask [] [] [] (unary (scope.filter (low mask)).length) [] []).withPC none) := by
  obtain ⟨next,hn,hvout,he⟩ := LeafProgram.foldProgram_run ports callback read (update mask)
    (fun _ => 16*(mask.length+1)) (invariant mask)
    (fun bits => ∃ v, v < mask.length ∧ Encoding.encodeNat v = bits)
    (callback_contract mask) (scope.map Encoding.encodeNat) []
    (state r mask [] [] [] [] [] [])
    (by intro bits hb; obtain ⟨v,hv0,rfl⟩ := List.mem_map.mp hb; exact ⟨v,hv v hv0,rfl⟩)
    ⟨r,[],rfl⟩ false true false
  obtain ⟨rf,acc,rfl⟩ := hn
  have hacc : acc = unary (scope.filter (low mask)).length := by
    simpa [read,state,fold_update] using hvout
  subst acc
  refine ⟨parserRegs rf false true false,?_⟩
  simpa only [List.append_nil,parser_state,SubexpScopeCountSetup.encode_scope,program] using he

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime outer record fold computing the maximum masked scope length and
factor count, including empty scope records. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
theorem scopeRegs_injective : Function.Injective scopeRegs := Fin.castAdd_injective _ _
theorem scopeStacks_injective : Function.Injective scopeStacks := Fin.castAdd_injective _ _

theorem scopeCall_eval_oai (r : Fin 10 → Bool) (mask source : List Bool) (scope : List ℕ)
    (hv : ∀ v ∈ scope, v < mask.length) (a q : ℕ) :
    ∃ n rf, n ≤ 4+RecordPrograms.budget (fun _ => 16*(mask.length+1)) (scope.map Encoding.encodeNat) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = r i) ∧
      Eval scopeCall n (state (prepared r) mask (Encoding.encodeList Encoding.encodeNat scope) source [] a q)
        ⟨rf,Function.update (state r mask [] source [] a q).stacks 4
          (unary (scope.filter (Scope.low mask)).length)⟩ := by
  let d := state (prepared r) mask (Encoding.encodeList Encoding.encodeNat scope) source [] a q
  obtain ⟨rr,nt,hnt,ht⟩ := Scope.program_runsIn (r ∘ scopeRegs) mask scope hv
  let b := Scope.state rr mask [] [] [] (unary (scope.filter (Scope.low mask)).length) [] []
  have hp : projectState scopeRegs scopeStacks d =
      RecordPrograms.state Scope.ports (Scope.state (r ∘ scopeRegs) mask [] [] [] [] [] [])
        false true false (Encoding.encodeList Encoding.encodeNat scope) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [←hp] at ht
  have he := eval_call_from_state Scope.program scopeRegs scopeStacks d scopeRegs_injective scopeStacks_injective ht
  let e := embedState scopeRegs scopeStacks d b
  have heq : e = ⟨e.regs,Function.update (state r mask [] source [] a q).stacks 4
      (unary (scope.filter (Scope.low mask)).length)⟩ := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i
    all_goals first
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 0
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 1
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 2
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 3
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 4
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 5
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 6
      | exact embedState_stack_frame scopeRegs scopeStacks d b _ (by decide)
  refine ⟨nt,e.regs,hnt,?_,?_⟩
  · intro i hi
    have h := embedState_register_frame scopeRegs scopeStacks d b i (by
      rintro ⟨j,hj⟩
      have he : j.val = i.val := congrArg Fin.val hj
      have hlt := j.isLt
      omega)
    have h4 : i ≠ 4 := by intro he; subst i; contradiction
    have h5 : i ≠ 5 := by intro he; subst i; contradiction
    have h6 : i ≠ 6 := by intro he; subst i; contradiction
    simpa [e, d,state,prepared,h4,h5,h6] using h
  · change Eval scopeCall nt d e at he
    rw [heq] at he
    exact he

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.scopeCall_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.scopeCall_eval_oai
