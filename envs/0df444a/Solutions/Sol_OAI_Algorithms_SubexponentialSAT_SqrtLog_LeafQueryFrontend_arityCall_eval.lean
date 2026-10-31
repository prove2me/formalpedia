-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCall_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:18:15.716527+00:00
-- url     : https://prove2.me/submissions/b7d6aec2-7287-4ff5-bd8c-4471d57f7ad1

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S146
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafStatisticsProgram_Arity_scopeCall_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed disjoint work areas for the per-query native frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
theorem registers_injective (n : ℕ) (hn : n ≤ 40) : Function.Injective (registers n hn) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun z : Fin 40 => z.val) h
theorem block_injective (base n : ℕ) (hn : base+n ≤ 768) : Function.Injective (block base n hn) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [block] at this; omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramMax
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native unary maximum. Consumes the new value and leaves the maximum
on the accumulator stack, using a linear number of physical bit operations. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem popX_eval (r : Fin 3 → Bool) (x y z : List Bool) :
    Eval popX 1 (state r x y z) (popped r x y z) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 3) 0 1)
    (state r x y z))) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (StructuredProgram.State.mk _)
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem iteration (r : Fin 3 → Bool) (x y z : ℕ) :
    ∃ rf, Eval body 4 (popped r (unary (x+1)) (unary y) (unary z))
      (popped rf (unary x) (unary (y-1)) (unary (z+1))) := by
  let r1 := readRegs r 0 1 (some true)
  let r2 := readRegs r1 0 2 (unary y).head?
  let r3 := Function.update r2 0 true
  refine ⟨r3, ?_⟩
  have h1 : Eval takeY 1 (state r1 (unary x) (unary y) (unary z))
      (state r2 (unary x) (unary (y-1)) (unary z)) := by
    convert (Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 3) 0 2)
      (state r1 (unary x) (unary y) (unary z)))) using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;> simp [ unary, List.tail_replicate,
      StructuredProgram.Atom.instr,execInstr]
  have h2 : Eval pushZ 2 (state r2 (unary x) (unary (y-1)) (unary z))
      (state r3 (unary x) (unary (y-1)) (unary (z+1))) := by
    have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 3) true)
      (state r2 (unary x) (unary (y-1)) (unary z)))).seq
      (Eval.base (StructuredProgram.Eval.atom (.push (2 : Fin 3) 0) _))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;>
      simp [unary,List.replicate_succ,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
  exact h1.seq (h2.seq (popX_eval r3 (unary x) (unary (y-1)) (unary (z+1))))

theorem loop_eval (r : Fin 3 → Bool) (x y z : ℕ) :
    ∃ rf, Eval loop (5*x+1) (popped r (unary x) (unary y) (unary z))
      (state rf [] (unary (y-x)) (unary (z+x))) := by
  induction x generalizing r y z with
  | zero =>
      exact ⟨readRegs r 0 1 none, Eval.while_false (by rfl)⟩
  | succ x ih =>
      obtain ⟨ri,hi⟩ := iteration r x y z
      obtain ⟨rf,hr⟩ := ih ri (y-1) (z+1)
      refine ⟨rf, ?_⟩
      have h := Eval.while_true (show (popped r (unary (x+1)) (unary y) (unary z)).regs 1 = true by rfl) hi hr
      convert h using 1 <;> simp [Nat.sub_sub,Nat.add_comm,Nat.add_left_comm] ; omega

theorem command_eval (r : Fin 3 → Bool) (x y : ℕ) :
    ∃ rf, Eval command (8*x+5) (state r (unary x) (unary y) [])
      (state rf [] (unary (max x y)) []) := by
  obtain ⟨ri,hi⟩ := loop_eval r x y 0
  let rf := readRegs ri 0 1 none
  have ht : Eval transfer (3*x+3) (state ri [] (unary (y-x)) (unary x))
      (state rf [] (unary (max x y)) []) := by
    have h := SubexpScanPrimitives.transfer_eval
      (state ri [] (unary (y-x)) (unary x)) (2 : Fin 3) 1 (0 : Fin 3) 1
      (by decide) (by decide)
    convert h using 1
    · simp [ unary]
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; fin_cases i <;>
          simp [ StackRoutines.transferStacks, unary, List.reverse_replicate]
        omega
  refine ⟨rf, ?_⟩
  simp only [Nat.zero_add] at hi
  have h := (popX_eval r (unary x) (unary y) []).seq (hi.seq ht)
  convert h using 1 ; omega

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max

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

theorem parser_state (r : Fin 10 → Bool) (mask current source payload src pay : List Bool)
    (a q : ℕ) (t p f : Bool) :
    RecordPrograms.state ports (state r mask current source payload a q) t p f src pay =
      state (parserRegs r t p f) mask current src pay a q := by
  apply congrArg (StructuredProgram.State.mk _)
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem prepare_eval (d : Data) : Eval prepare 3 d ⟨prepared d.regs,d.stacks⟩ := by
  exact .base (SubexpParameterProgram.atoms_eval _ d)

theorem maxRegs_injective : Function.Injective maxRegs := Fin.castAdd_injective _ _
theorem maxStacks_injective : Function.Injective maxStacks := by decide

theorem maxCall_eval (r : Fin 10 → Bool) (mask source : List Bool) (x a q : ℕ) :
    ∃ rf, (∀ i : Fin 10, 3 ≤ i.val → rf i = r i) ∧
      Eval maxCall (8*x+6)
        ⟨r,Function.update (state r mask [] source [] a q).stacks 4 (unary x)⟩
        (state rf mask [] source [] (max x a) q) := by
  let d : Data := ⟨r,Function.update (state r mask [] source [] a q).stacks 4 (unary x)⟩
  obtain ⟨rr,hr⟩ := Max.command_eval (r ∘ maxRegs) x a
  let b := Max.state rr [] (unary (max x a)) []
  have hp : projectState maxRegs maxStacks d = Max.state (r ∘ maxRegs) (unary x) (unary a) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have ht := compiled_halt_trace hr 0 1
  rw [←hp] at ht
  have he := eval_call_from_state Max.program maxRegs maxStacks d maxRegs_injective maxStacks_injective ht
  let e := embedState maxRegs maxStacks d b
  have heq : e = state e.regs mask [] source [] (max x a) q := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i
    all_goals first
      | exact embedState_stack maxRegs maxStacks d b maxStacks_injective 0
      | exact embedState_stack maxRegs maxStacks d b maxStacks_injective 1
      | exact embedState_stack maxRegs maxStacks d b maxStacks_injective 2
      | exact embedState_stack_frame maxRegs maxStacks d b _ (by decide)
  refine ⟨e.regs,?_,?_⟩
  · intro i hi
    exact embedState_register_frame maxRegs maxStacks d b i (by
      rintro ⟨j,hj⟩
      have he : j.val = i.val := congrArg Fin.val hj
      have hlt := j.isLt
      omega)
  · change Eval maxCall (8*x+5+1) d e at he
    rw [heq] at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl

theorem callback_eval (r : Fin 10 → Bool) (mask source : List Bool) (scope : List ℕ)
    (hv : ∀ v ∈ scope, v < mask.length) (a q : ℕ) :
    ∃ n rf, n ≤ 3*(Encoding.encodeList Encoding.encodeNat scope).length+
        scopeBudget mask scope+8*scope.length+14 ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = r i) ∧
      Eval callback n
        (state r mask [] source (Encoding.encodeList Encoding.encodeNat scope).reverse a q)
        (state rf mask [] source [] (max (scope.filter (Scope.low mask)).length a) (q+1)) := by
  let bits := Encoding.encodeList Encoding.encodeNat scope
  let r1 := readRegs r 0 1 none
  have htransfer : Eval transfer (3*bits.length+3)
      (state r mask [] source bits.reverse a q)
      (state r1 mask bits source [] a q) := by
    apply Eval.call
    convert (ListRegisterProgram.transfer_run (8 : Fin 12) 5 (0 : Fin 10) 1
      (by decide) (by decide) r (state r mask [] source bits.reverse a q).stacks) using 1 <;>
      simp [r1,state,StackRoutines.transferStacks]
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have hp := prepare_eval (state r1 mask bits source [] a q)
  obtain ⟨ns,rs,hns,hrs,hs⟩ := scopeCall_eval r1 mask source scope hv a q
  obtain ⟨rm,hrm,hm⟩ := maxCall_eval rs mask source (scope.filter (Scope.low mask)).length a q
  let rf := Function.update rm 0 true
  have hi : Eval increment 2
      (state rm mask [] source [] (max (scope.filter (Scope.low mask)).length a) q)
      (state rf mask [] source [] (max (scope.filter (Scope.low mask)).length a) (q+1)) := by
    have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) true)
      (state rm mask [] source [] (max (scope.filter (Scope.low mask)).length a) q))).seq
      (Eval.base (StructuredProgram.Eval.atom (.push (11 : Fin 12) 0) _))
    convert h using 1
    · rfl
    · apply congrArg (StructuredProgram.State.mk _)
      funext i; fin_cases i <;>
        simp [state,unary,List.replicate_succ,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
execInstr]
  refine ⟨_,rf,?_,?_,htransfer.seq (hp.seq (hs.seq (hm.seq hi)))⟩
  · have hlen := List.length_filter_le (Scope.low mask) scope
    dsimp [scopeBudget,bits] at *
    omega
  · intro i hi
    have h0 : i ≠ 0 := by intro he; subst i; contradiction
    have h1 : i ≠ 1 := by intro he; subst i; contradiction
    simp only [rf,Function.update_of_ne h0]
    rw [hrm i (by omega),hrs i hi]
    simp [r1,readRegs,h0,h1]

@[simp] theorem decoded_encode (scope : List ℕ) :
    decoded (Encoding.encodeList Encoding.encodeNat scope) = scope := by
  classical
  unfold decoded
  split
  · rename_i h
    exact Encoding.encodeList_injective Encoding.encodeNat_injective (Classical.choose_spec h)
  · rename_i h
    exact (h ⟨scope,rfl⟩).elim

theorem callback_contract (mask : List Bool) :
    LeafProgram.FoldContract ports callback read (update mask) (cost mask) (invariant mask)
      (fun bits => ∃ scope, (∀ v ∈ scope, v < mask.length) ∧
        Encoding.encodeList Encoding.encodeNat scope = bits) := by
  rintro bits tail base ⟨scope,hv,rfl⟩ ⟨r,a,q,rfl⟩
  obtain ⟨n,rf,hn,hr,he⟩ := callback_eval (parserRegs r false true false) mask tail scope hv a q
  have h7 : rf 7 = false := by simpa [parserRegs] using hr 7 (by decide)
  have h8 : rf 8 = true := by simpa [parserRegs] using hr 8 (by decide)
  have h9 : rf 9 = false := by simpa [parserRegs] using hr 9 (by decide)
  have hreset : parserRegs rf false true false = rf := by
    funext i; fin_cases i <;> simp [parserRegs,h7,h8,h9]
  refine ⟨n,state rf mask [] [] [] (max (scope.filter (Scope.low mask)).length a) (q+1),?_,
    ⟨rf,_,_,rfl⟩,?_,?_⟩
  · simpa [cost] using hn
  · simp [LeafProgram.foldEffect,read,update,state,unary]
  · rw [parser_state,parser_state,hreset]
    exact he

theorem fold_update (mask : List Bool) (scopes : List (List ℕ)) (a q : ℕ) :
    (scopes.map (Encoding.encodeList Encoding.encodeNat)).foldl (fun t bits => update mask bits t) (a,q) =
      (arity mask scopes a,q+scopes.length) := by
  induction scopes generalizing a q with
  | nil => simp [arity]
  | cons scope scopes ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [show update mask (Encoding.encodeList Encoding.encodeNat scope) (a,q) =
      (max (scope.filter (Scope.low mask)).length a,q+1) by simp [update]]
    rw [ih]
    simp [arity,Nat.add_comm,Nat.add_left_comm]

theorem program_runsIn (r : Fin 10 → Bool) (mask : List Bool) (scopes : List (List ℕ))
    (hv : ∀ scope ∈ scopes, ∀ v ∈ scope, v < mask.length) :
    ∃ rf, RunsIn program
      (4+RecordPrograms.budget (cost mask) (scopes.map (Encoding.encodeList Encoding.encodeNat)))
      ((RecordPrograms.state ports (state r mask [] [] [] 0 0) false true false
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) scopes) []).withPC (some program.entry))
      ((state rf mask [] [] [] (arity mask scopes 0) scopes.length).withPC none) := by
  obtain ⟨next,hn,hvalue,he⟩ := LeafProgram.foldProgram_run ports callback read (update mask)
    (cost mask) (invariant mask)
    (fun bits => ∃ scope, (∀ v ∈ scope, v < mask.length) ∧ Encoding.encodeList Encoding.encodeNat scope = bits)
    (callback_contract mask) (scopes.map (Encoding.encodeList Encoding.encodeNat)) []
    (state r mask [] [] [] 0 0)
    (by intro bits hb; obtain ⟨scope,hm,rfl⟩ := List.mem_map.mp hb; exact ⟨scope,hv scope hm,rfl⟩)
    ⟨r,0,0,rfl⟩ false true false
  obtain ⟨rf,a,q,rfl⟩ := hn
  have hread (rr : Fin 10 → Bool) (aa qq : ℕ) :
      read (state rr mask [] [] [] aa qq) = (aa,qq) := by
    simp [read,state,unary]
  have hvv : (a,q) = (arity mask scopes 0,scopes.length) := by
    rw [hread,hread,fold_update] at hvalue
    simpa only [Nat.zero_add] using hvalue
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj hvv
  refine ⟨parserRegs rf false true false,?_⟩
  have hencode : ∀ xs : List (List ℕ), Encoding.encodeList id (xs.map (Encoding.encodeList Encoding.encodeNat)) =
      Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons scope scopes ih => simp [Encoding.encodeList,ih]
  simpa only [List.append_nil,parser_state,hencode,program] using he

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The frontend calls only concrete finite machines. All state embeddings
below are specifications of actual calls, never free data transformations. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem call_run {r s l : ℕ} (p : Program r s l) (rr : Fin r → Fin 40)
    (ss : Fin s → Fin 768) (hr : Function.Injective rr) (hs : Function.Injective ss)
    (a : Data) (b : State r s) (B : ℕ)
    (h : RunsIn p B ((projectState rr ss a).withPC (some p.entry)) (b.withPC none)) :
    ∃ n ≤ B, Eval (.call (ProgramLinking.liftProgram p rr ss)) n a (embedState rr ss a b) := by
  obtain ⟨n,hn,ht⟩ := h
  exact ⟨n,hn,eval_call_from_state p rr ss a hr hs ht⟩

theorem arityCall_eval_oai (a : Data) (rows : List (List ℕ)) (forward : List Bool)
    (hv : ∀ row ∈ rows, ∀ v ∈ row, v < forward.length)
    (hp : projectState r10 arity a = RecordPrograms.state LeafStatisticsProgram.Arity.ports
      (LeafStatisticsProgram.Arity.state (a.regs ∘ r10) forward [] [] [] 0 0)
      false true false (LeafStatisticsProgram.scopeBits rows) []) :
    ∃ n ≤ 4+RecordPrograms.budget (LeafStatisticsProgram.Arity.cost forward)
        (rows.map (Encoding.encodeList Encoding.encodeNat)), ∃ rf,
      Eval arityCall n a (embedState r10 arity a
        (LeafStatisticsProgram.Arity.state rf forward [] [] []
          (LeafStatisticsProgram.Arity.arity forward rows 0) rows.length)) := by
  obtain ⟨rf,he⟩ := LeafStatisticsProgram.Arity.program_runsIn (a.regs ∘ r10) forward rows hv
  change projectState r10 arity a = RecordPrograms.state LeafStatisticsProgram.Arity.ports
    (LeafStatisticsProgram.Arity.state (a.regs ∘ r10) forward [] [] [] 0 0) false true false
    (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) rows) [] at hp
  rw [←hp] at he
  obtain ⟨n,hn,he⟩ := call_run _ r10 arity (registers_injective ..) (block_injective ..) a _ _ he
  exact ⟨n,hn,rf,he⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCall_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCall_eval_oai
