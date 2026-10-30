-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.optional_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:47:09.327385+00:00
-- url     : https://prove2.me/submissions/9c046a84-8f06-4375-9770-be80098b7963

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S088
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S102
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashScopeProgram_Marked_fetch_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpScopeProducer_command_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.MarkedFrame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram

theorem emit_eval (a : Data) : Eval emit (5*(a.stacks 47).length+7) a (emitted a) := by
  have h := (pushConst_eval (48 : Fin 80) (8 : Fin 11) false a).seq
    ((escape_eval_state ports (pushedState 48 8 false a)).seq
      (pushConst_eval (48 : Fin 80) (8 : Fin 11) true (escapedState ports (pushedState 48 8 false a))))
  convert h using 1 <;> simp [emitted,ports,pushedState] ; omega

theorem fix_eval (a : Data) : Eval fix 3 a (fixed a) := by
  exact (Eval.base (.atom _ a)).seq ((Eval.base (.atom _ _)).seq (Eval.base (.atom _ _)))

theorem command_eval (a : Data) (bits : List Bool) (h : a.stacks 47=bits.reverse) :
    ∃ b : Data, Eval command (5*bits.length+10) a b ∧
      b.stacks 47=[] ∧ b.stacks 48=prependRecord bits (a.stacks 48) ∧
      b.regs 8=false ∧ b.regs 9=true ∧ b.regs 10=false ∧
      ∀ i, i ≠ 47 → i ≠ 48 → b.stacks i=a.stacks i := by
  refine ⟨fixed (emitted a),?_,?_,?_,?_,?_,?_,?_⟩
  · convert (emit_eval a).seq (fix_eval (emitted a)) using 1 ; simp [h]
  · simp [fixed,emitted,ports,pushedState]
  · simp [fixed,emitted,ports,pushedState,h,prependRecord,frame_eq_escaped,List.append_assoc]
  · simp [fixed]
  · simp [fixed]
  · simp [fixed]
  · intro i hi47 hi48
    simp [fixed,emitted,ports,pushedState,hi47,hi48]

end SubexponentialSAT.SqrtLog.HashScopeProgram.MarkedFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramReset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Reset
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_eval {r s : ℕ} (is : List (Fin r)) (a : State r s) :
    Eval (command is) is.length a (result is a) := by
  induction is generalizing a with
  | nil => exact .base (.skip _)
  | cons i is ih =>
      let b : State r s := ⟨Function.update a.regs i false,a.stacks⟩
      have hs : Eval (.base (.atom (.set i false))) 1 a b := .base (.atom _ _)
      have he : result is b = result (i::is) a := by
        apply congrArg₂ StructuredProgram.State.mk
        · funext j
          by_cases hji : j=i <;> by_cases hj : j ∈ is <;>
            simp [b,hji,hj,Function.update]
        · rfl
      have h := hs.seq (ih b)
      rw [he] at h
      simpa [command,Nat.add_comm] using h

theorem all_eval {r s : ℕ} (a : State r s) :
    Eval (all : Cmd r s) r a ⟨fun _ => false,a.stacks⟩ := by
  simpa [all,result] using command_eval (List.finRange r) a

end SubexponentialSAT.SqrtLog.HashScopeProgram.Reset

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeProducer
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Construct a clause's local chunk scope from its encoded literals

This fixed program maps actual literal records to chunk records, restores the
record order, and invokes the checked stable deduplicator. Its output order is
the last-occurrence order used by the materializer and incidence-plan producer.
-/

namespace SubexponentialSAT.SubexpScopeProducer

open BitProgram StructuredCalls SubexpChunkRecordMap

theorem program_runsIn (ell : List Bool) (codes : List ℕ)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    ∃ rf, RunsIn program (budget ell codes + 1)
      ((data false false false ell (Encoding.encodeList Encoding.encodeNat codes) [] []).withPC
        (some program.entry))
      ((⟨rf, tapes ell (Encoding.encodeList Encoding.encodeNat (scope ell codes)) [] []⟩ : Data).withPC none) := by
  obtain ⟨t, ht, rf, he⟩ := command_eval ell codes hell
  exact ⟨rf, t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 19 19⟩

end SubexponentialSAT.SubexpScopeProducer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native lookup of the optional original marked clause. Local ports49/50
stage original masters705/706; source14 stages original formula700. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Marked
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

theorem scopeStacks_injective : Function.Injective scopeStacks := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [scopeStacks] at hh
  omega

theorem prepareScope_eval (rf : Fin 11 → Bool) (width modulus master shape out clause : List Bool) :
    Eval prepareScope 13 (data rf width modulus master shape out [] [] clause [] [])
      (data (fun _ => false) width modulus master shape out [] [] clause [true] []) := by
  have h1 := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (72 : Fin 80) (8 : Fin 11) true
    (data rf width modulus master shape out [] [] clause [] [])
  have h2 := Reset.all_eval (SubexponentialSAT.Subexp.TupleProgram.pushedState 72 8 true
    (data rf width modulus master shape out [] [] clause [] []))
  convert h1.seq h2 using 1
  all_goals try with_reducible_and_instances rfl
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext j; fin_cases j <;> simp [data,tapes]

theorem extract_eval (codes : List ℕ) (width modulus master shape out : List Bool) :
    ∃ n ≤ SubexpScopeProducer.budget [true] codes+1, ∃ rf,
      Eval extract n
        (data (fun _ => false) width modulus master shape out [] []
          (Encoding.encodeList Encoding.encodeNat codes) [true] [])
        (data rf width modulus master shape out [] []
          (Encoding.encodeList Encoding.encodeNat (SubexpScopeProducer.scope [true] codes)) [true] []) := by
  obtain ⟨rf,ht⟩ := SubexpScopeProducer.program_runsIn [true] codes (by decide)
  let a := data (fun _ => false) width modulus master shape out [] []
    (Encoding.encodeList Encoding.encodeNat codes) [true] []
  let z : State 11 22 := ⟨rf,SubexponentialSAT.SubexpChunkRecordMap.tapes [true]
    (Encoding.encodeList Encoding.encodeNat (SubexpScopeProducer.scope [true] codes)) [] []⟩
  have ha : restrictState id scopeStacks a=SubexponentialSAT.SubexpChunkRecordMap.data false false false [true]
      (Encoding.encodeList Encoding.encodeNat codes) [] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
  obtain ⟨n,hn,he⟩ := lifted_call SubexpScopeProducer.program id scopeStacks Function.injective_id
    scopeStacks_injective a z (SubexpScopeProducer.budget [true] codes+1) (by simpa [ha,z] using ht)
  have hz : embedState id scopeStacks a z=data rf width modulus master shape out [] []
      (Encoding.encodeList Encoding.encodeNat (SubexpScopeProducer.scope [true] codes)) [true] [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id scopeStacks_injective
    · intro j; rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro j; fin_cases j <;> rfl
    · intro j hj
      have h73 : j≠73 := fun h => hj ⟨19,h.symm⟩
      simp [a,data,tapes,h73]
  exact ⟨n,hn,rf,by simpa [extract,hz] using he⟩

end SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked branch appends one scope even when that scope is empty. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Marked
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls


theorem clearEll_eval (rf : Fin 11 → Bool) (width modulus master shape out clause : List Bool) :
    Eval clearEll 5 (data rf width modulus master shape out [] [] clause [true] [])
      (data (readRegs rf 8 9 none) width modulus master shape out [] [] clause [] []) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (72 : Fin 80) (8 : Fin 11) 9
    (data rf width modulus master shape out [] [] clause [true] [])
  convert h using 1
  · simp [data, tapes]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext j; fin_cases j <;> simp [data,tapes,StackRoutines.clearStacks]

theorem moveScope_eval (rf : Fin 11 → Bool) (width modulus master shape out clause : List Bool) :
    Eval moveScope (3*clause.length+3) (data rf width modulus master shape out [] [] clause [] [])
      (data (readRegs rf 8 9 none) width modulus master shape out [] [] [] [] clause.reverse) := by
  have h := SubexponentialSAT.SubexpScanPrimitives.transfer_eval
    (data rf width modulus master shape out [] [] clause [] []) 73 47 8 9 (by decide) (by decide)
  convert h using 1
  · simp [data, tapes]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext j; fin_cases j <;> simp [data,tapes,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks]

theorem process_eval (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i)) (i : Fin clauses.length)
    (rf : Fin 11 → Bool) (width modulus shape out : List Bool) :
    ∃ n ≤ processCost clauses codes i, ∃ rf', rf' 8=false ∧ rf' 9=true ∧ rf' 10=false ∧
      Eval process n
        (data rf width modulus (Encoding.encodeList id clauses) shape out (Encoding.encodeNat i.val) [] [] [] [])
        (data rf' width modulus (Encoding.encodeList id clauses) shape
          (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBits (codes i)) out) [] [] [] [] []) := by
  obtain ⟨nf,hnf,r1,hf⟩ := fetch_eval clauses i rf width modulus shape out
  rw [hc] at hf
  have hp := prepareScope_eval r1 width modulus (Encoding.encodeList id clauses) shape out
    (Encoding.encodeList Encoding.encodeNat (codes i))
  obtain ⟨ns,hns,r2,hs⟩ := extract_eval (codes i) width modulus (Encoding.encodeList id clauses) shape out
  have he := clearEll_eval r2 width modulus (Encoding.encodeList id clauses) shape out (scopeBits (codes i))
  have hm := moveScope_eval (readRegs r2 8 9 none) width modulus (Encoding.encodeList id clauses) shape out (scopeBits (codes i))
  let a := data (readRegs (readRegs r2 8 9 none) 8 9 none) width modulus (Encoding.encodeList id clauses) shape out [] [] [] []
    (scopeBits (codes i)).reverse
  obtain ⟨z,hz,h47,h48,h8,h9,h10,hframe⟩ := MarkedFrame.command_eval a (scopeBits (codes i)) (by simp [a,data,tapes])
  have hz' : z=data z.regs width modulus (Encoding.encodeList id clauses) shape
      (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBits (codes i)) out) [] [] [] [] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext j
      by_cases hj47 : j=47
      · subst j; simpa [data,tapes] using h47
      by_cases hj48 : j=48
      · subst j; simpa [a,data,tapes] using h48
      rw [hframe j hj47 hj48]
      simp [a,data,tapes,hj47,hj48]
  rw [hz'] at hz
  refine ⟨_,?_,z.regs,h8,h9,h10,hf.seq (hp.seq (hs.seq (he.seq (hm.seq hz))))⟩
  unfold processCost
  omega

theorem clearIndex_eval (rf : Fin 11 → Bool) (width modulus master shape out index : List Bool) :
    Eval clearIndex (2*index.length+3)
      (data rf width modulus master shape out index [] [] [] [])
      (data (readRegs rf 8 9 none) width modulus master shape out [] [] [] [] []) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (49 : Fin 80) (8 : Fin 11) 9
    (data rf width modulus master shape out index [] [] [] [])
  convert h using 1
  · simp [data, tapes]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext j; fin_cases j <;> simp [data,tapes,StackRoutines.clearStacks]

theorem popFlag_eval (rf : Fin 11 → Bool) (width modulus master shape out index : List Bool) (flag : Bool) :
    Eval popFlag 1 (data rf width modulus master shape out index [flag] [] [] [])
      (data (readRegs rf 8 9 (some flag)) width modulus master shape out index [] [] [] []) := by
  have h := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (50 : Fin 80) (8 : Fin 11) 9)
    (data rf width modulus master shape out index [flag] [] [] []))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext j; fin_cases j <;> simp [data,tapes,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr]

theorem optional_eval_oai (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (mark : Option (Fin clauses.length)) (index : List Bool)
    (hindex : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (rf : Fin 11 → Bool) (width modulus shape out : List Bool) :
    ∃ n ≤ optionalCost clauses codes mark index, ∃ rf', rf' 8=false ∧ rf' 9=true ∧ rf' 10=false ∧
      Eval optional n
        (data rf width modulus (Encoding.encodeList id clauses) shape out index [mark.isSome] [] [] [])
        (data rf' width modulus (Encoding.encodeList id clauses) shape (appended (clauses := clauses) codes mark out) [] [] [] [] []) := by
  cases mark with
  | none =>
      have hp := popFlag_eval rf width modulus (Encoding.encodeList id clauses) shape out index false
      let r := readRegs rf 8 9 (some false)
      have hc := clearIndex_eval r width modulus (Encoding.encodeList id clauses) shape out index
      let a := data (readRegs r 8 9 none) width modulus (Encoding.encodeList id clauses) shape out [] [] [] [] []
      have hf := MarkedFrame.fix_eval a
      refine ⟨1+((2*index.length+3)+3)+1,by simp [optionalCost]; omega,(MarkedFrame.fixed a).regs,?_,?_,?_,?_⟩
      · simp [MarkedFrame.fixed]
      · simp [MarkedFrame.fixed]
      · simp [MarkedFrame.fixed]
      · exact hp.seq (Eval.ite_false (by simp [data,readRegs]) (hc.seq hf))
  | some i =>
      have hi := hindex i rfl
      subst index
      have hp := popFlag_eval rf width modulus (Encoding.encodeList id clauses) shape out (Encoding.encodeNat i.val) true
      obtain ⟨n,hn,r,h8,h9,h10,he⟩ := process_eval clauses codes hc i (readRegs rf 8 9 (some true)) width modulus shape out
      refine ⟨1+n+1,?_,r,h8,h9,h10,?_⟩
      · simp [optionalCost]; omega
      · exact hp.seq (Eval.ite_true (by simp [data,readRegs]) he)

end SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.optional_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.optional_eval_oai
