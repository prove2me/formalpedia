-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral_from_state
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:21:14.277989+00:00
-- url     : https://prove2.me/submissions/a44f2c63-fa70-447c-b819-463d692006ef

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S089
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_literalDictionary_hit

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native conversion from the audited unary literal code `2*v+polarity` to
variable-key/polarity syntax. The source is a reversed parsed `encodeNat` record.
The loop consumes two unary marks per variable mark and records an odd tail as
positive polarity. Its instruction table is independent of the variable index. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

namespace Decode

private theorem pop_cons (v pr p b : Bool) (xs acc : List Bool) :
    Eval (atom (.pop 0 0 1)) 1 (data v pr p (b::xs) acc) (data b true p xs acc) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 2) (0 : Fin 4) 1)
    (data v pr p (b::xs) acc))) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.instr,execInstr,readRegs]
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.instr,execInstr]

private theorem pop_nil (v pr p : Bool) (acc : List Bool) :
    Eval (atom (.pop 0 0 1)) 1 (data v pr p [] acc) (data false false p [] acc) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 2) (0 : Fin 4) 1)
    (data v pr p [] acc))) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.instr,execInstr,readRegs]
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.instr,execInstr]

private theorem push_acc (v pr p : Bool) (xs acc : List Bool) :
    Eval (atom (.push 1 2)) 1 (data v pr p xs acc) (data v pr p xs (true::acc)) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.push (1 : Fin 2) (2 : Fin 4))
    (data v pr p xs acc))) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.instr,execInstr]

private theorem set_positive (v pr p : Bool) (xs acc : List Bool) :
    Eval (atom (.set 3 true)) 1 (data v pr p xs acc) (data v pr true xs acc) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.set (3 : Fin 4) true)
    (data v pr p xs acc))) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.instr,execInstr]
  · rfl

private theorem body_pair (m : ℕ) (acc : List Bool) :
    Eval pairBody 4 (data true true false (true :: List.replicate m true) acc)
      (ready m (true::acc)) := by
  have h1 := pop_cons true true false true (List.replicate m true) acc
  have h2 := push_acc true true false (List.replicate m true) acc
  have h3 : Eval (atom (.pop 0 0 1)) 1
      (data true true false (List.replicate m true) (true::acc)) (ready m (true::acc)) := by
    cases m with
    | zero => exact pop_nil true true false _
    | succ m => simpa only [List.replicate_succ,ready] using
        (pop_cons true true false true (List.replicate m true) (true::acc))
  exact h1.seq (Eval.ite_true rfl (h2.seq h3))

private theorem body_odd (acc : List Bool) :
    Eval pairBody 3 (data true true false [] acc) (data false false true [] acc) := by
  exact (pop_nil true true false acc).seq (Eval.ite_false rfl (set_positive false false false [] acc))

theorem pairLoop_eval (v : ℕ) (positive : Bool) (acc : List Bool) :
    Eval pairLoop (5*v + 4*(if positive then 1 else 0) + 1)
      (ready (2*v + (if positive then 1 else 0)) acc)
      (data false false positive [] (List.replicate v true ++ acc)) := by
  induction v generalizing acc with
  | zero =>
    cases positive with
    | false => exact Eval.while_false rfl
    | true =>
      have ht : Eval pairLoop (3+1+1) (data true true false [] acc)
          (data false false true [] acc) :=
        Eval.while_true rfl (body_odd acc) (Eval.while_false rfl)
      simpa [ready] using ht
  | succ v ih =>
    have hh := Eval.while_true (test := (1 : Fin 4)) (body := pairBody) rfl
      (body_pair (2*v + (if positive then 1 else 0)) acc) (ih (true::acc))
    convert hh using 1
    · omega
    · rw [show 2*(v+1)+(if positive then 1 else 0) =
        (2*v+(if positive then 1 else 0))+2 by omega]
      simp [ready,List.replicate_succ]
    · simp only [List.replicate_succ]
      congr 1
      have h := List.replicate_add v 1 true
      simpa [List.replicate_succ, Nat.add_comm, List.append_assoc] using congrArg (· ++ acc) h

theorem prepare_eval (regs : Fin 4 → Bool) (m : ℕ) :
    Eval prepare 4 (input regs m) (ready m []) := by
  let a := (StructuredProgram.Atom.pop (0 : Fin 2) (0 : Fin 4) 1).eval (input regs m)
  let b := (StructuredProgram.Atom.set (2 : Fin 4) true).eval a
  let c := (StructuredProgram.Atom.set (3 : Fin 4) false).eval b
  have h1 : Eval (atom (.pop 0 0 1)) 1 (input regs m) a := .base (.atom _ _)
  have h2 : Eval (atom (.set 2 true)) 1 a b := .base (.atom _ _)
  have h3 : Eval (atom (.set 3 false)) 1 b c := .base (.atom _ _)
  have hc : c = data false true false (List.replicate m true) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [b,a,input,Encoding.encodeNat,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr,readRegs]
    · funext i; fin_cases i <;> simp [b,a,input,Encoding.encodeNat,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr]
  have h4 : Eval (atom (.pop 0 0 1)) 1 c (ready m []) := by
    rw [hc]
    cases m with
    | zero => exact pop_nil false true false []
    | succ m => simpa only [List.replicate_succ,ready] using
        (pop_cons false true false true (List.replicate m true) [])
  exact h1.seq (h2.seq (h3.seq h4))

theorem emit_eval (positive : Bool) (v : ℕ) :
    Eval emit (3*v+6)
      (data false false positive [] (List.replicate v true)) (output positive v) := by
  let d := data false false positive [] (List.replicate v true)
  have h := StackRoutines.transferProgram_trace (1 : Fin 2) 0 (0 : Fin 4) 1
    (by decide) (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  have ht : Eval (.call (StackRoutines.transferProgram (1 : Fin 2) 0 (0 : Fin 4) 1))
      (3*v+3) d (data false false positive (List.replicate v true) []) := by
    apply Eval.call
    have hr : readRegs d.regs 0 1 none = (data false false positive (List.replicate v true) []).regs := by
      funext i; fin_cases i <;> simp [d,data,readRegs]
    have hs : StackRoutines.transferStacks (1 : Fin 2) 0 d.stacks =
        (data false false positive (List.replicate v true) []).stacks := by
      funext i; fin_cases i <;> simp [d,data,StackRoutines.transferStacks]
    simp only [StackRoutines.transferResult] at hh
    rw [hr,hs] at hh
    simpa [StackRoutines.transferProgram,StructuredProgram.State.withPC,
      d,data,Nat.add_assoc] using hh
  let a := (StructuredProgram.Atom.set (0 : Fin 4) false).eval
    (data false false positive (List.replicate v true) [])
  let b := (StructuredProgram.Atom.push (0 : Fin 2) (0 : Fin 4)).eval a
  let c := (StructuredProgram.Atom.push (0 : Fin 2) (3 : Fin 4)).eval b
  have h1 : Eval (atom (.set 0 false)) 1 (data false false positive (List.replicate v true) []) a :=
    .base (.atom _ _)
  have h2 : Eval (atom (.push 0 0)) 1 a b := .base (.atom _ _)
  have h3 : Eval (atom (.push 0 3)) 1 b c := .base (.atom _ _)
  have hc : c = output positive v := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [b,a,data,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
    · funext i; fin_cases i <;> simp [b,a,data,Encoding.encodeNat,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
  rw [hc] at h3
  simpa [Nat.add_assoc] using ht.seq (h1.seq (h2.seq h3))

theorem command_eval (regs : Fin 4 → Bool) (v : ℕ) (positive : Bool) :
    Eval programCommand (8*v + 4*(if positive then 1 else 0) + 11)
      (input regs (2*v + (if positive then 1 else 0))) (output positive v) := by
  have hp := prepare_eval regs (2*v + (if positive then 1 else 0))
  have hl := pairLoop_eval v positive []
  simp only [List.append_nil] at hl
  have he := emit_eval positive v
  convert hp.seq (hl.seq he) using 1 ; omega

end Decode
end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramCanonical
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct native incidence evaluation from original unary CNF literal records.
This module composes the paid literal decoder with the paid dictionary lookup;
no preprocessing assumption converts literal numbers into variable keys. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem decodeRegisters_injective : Function.Injective decodeRegisters := by decide
theorem decodeStacks_injective : Function.Injective decodeStacks := by decide

private theorem embed_decode_input (regs : Fin 5 → Bool) (old : Bool)
    (m : ℕ) (table : List Bool) :
    embedState decodeRegisters decodeStacks
      (data regs old [] (Encoding.encodeNat m).reverse [] table)
      (Decode.input ![regs 0,regs 1,regs 2,old] m) =
        data regs old [] (Encoding.encodeNat m).reverse [] table := by
  apply embedState_eq_of_ports _ _ _ _ _ decodeRegisters_injective decodeStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [decodeRegisters,Fin.exists_fin_succ]
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [decodeStacks,Fin.exists_fin_succ]

private theorem embed_decode_output (regs : Fin 5 → Bool) (old positive : Bool)
    (m v : ℕ) (table : List Bool) :
    embedState decodeRegisters decodeStacks
      (data regs old [] (Encoding.encodeNat m).reverse [] table)
      (Decode.output positive v) =
        data (canonicalRegs regs) positive []
          (Encoding.encodeNat v ++ [positive]).reverse [] table := by
  apply embedState_eq_of_ports _ _ _ _ _ decodeRegisters_injective decodeStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;>
      simp_all [decodeRegisters,canonicalRegs,Fin.exists_fin_succ]
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;>
      simp_all [decodeStacks,Fin.exists_fin_succ]

theorem canonicalDecode_eval (regs : Fin 5 → Bool) (old positive : Bool)
    (v : ℕ) (table : List Bool) :
    Eval canonicalDecode (8*v + 4*(if positive then 1 else 0)+12)
      (data regs old [] (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse [] table)
      (data (canonicalRegs regs) positive []
        (Encoding.encodeNat v ++ [positive]).reverse [] table) := by
  have h := Decode.command_eval ![regs 0,regs 1,regs 2,old] v positive
  have hh := eval_liftCommand h 0 0 decodeRegisters decodeStacks
    (data regs old [] (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse [] table)
    decodeRegisters_injective decodeStacks_injective
  simpa only [embed_decode_input,embed_decode_output,Nat.add_assoc] using hh

theorem canonicalLiteral_hit (regs : Fin 5 → Bool) (old positive : Bool)
    (v : ℕ) (payload : List Bool) (entries : List (List Bool × List Bool))
    (hlookup : entries.lookup (Encoding.encodeNat v) = some payload) :
    ∃ n ≤ 8*v+16 + literalFetchBudget (Encoding.encodeNat v) entries + 9*payload.length+9,
      ∃ regs', Eval canonicalLiteral n
        (data regs old [] (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse []
          (Squarefree.Program.lookupRecords entries))
        (data regs' positive [] [] payload (Squarefree.Program.lookupRecords entries)) ∧
      regs' 4 = true := by
  have hd := canonicalDecode_eval regs old positive v (Squarefree.Program.lookupRecords entries)
  obtain ⟨n,hn,rr,he,hf⟩ := literalDictionary_hit (canonicalRegs regs) positive positive
    (Encoding.encodeNat v) payload entries hlookup
  refine ⟨(8*v+4*(if positive then 1 else 0)+12)+n,?_,rr,hd.seq he,hf⟩
  cases positive <;> simp only [Bool.false_eq_true,↓reduceIte] at * <;> omega

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed caller framing for the native sparse-hash interpreter. Low ports
0--55 are reserved for arithmetic. Literal lookup uses 56--62, leaving the
clause, row and constant accumulators physically untouched. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem literalRegisters_injective : Function.Injective literalRegisters :=
  Fin.castAdd_injective _ _
theorem literalStacks_injective : Function.Injective literalStacks := by
  intro i j h
  have h' := congrArg Fin.val h
  apply Fin.ext
  simp only [literalStacks] at h'
  omega

@[simp] theorem literalFrame_result (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) :
    (literalFrame base regs positive scan query result table).stacks 61 = result := by
  exact embedState_stack literalRegisters literalStacks base _ literalStacks_injective 5

@[simp] theorem literalFrame_table (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) :
    (literalFrame base regs positive scan query result table).stacks 62 = table := by
  exact embedState_stack literalRegisters literalStacks base _ literalStacks_injective 6

@[simp] theorem literalFrame_sign (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) :
    (literalFrame base regs positive scan query result table).regs 5 = positive := by
  exact embedState_register literalRegisters literalStacks base _ literalRegisters_injective 5

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramLiteralState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct-call interface from the actual caller state. This avoids preparing
an extra machine-state embedding between the record parser and literal lookup. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem fetchLiteral_from_state_oai (d : Machine) (regs : Fin 5 → Bool) (old positive : Bool)
    (v : ℕ) (payload : List Bool) (entries : List (List Bool × List Bool))
    (hlookup : entries.lookup (Encoding.encodeNat v) = some payload)
    (hports : projectState literalRegisters literalStacks d =
      data regs old [] (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse []
        (Squarefree.Program.lookupRecords entries)) :
    ∃ n ≤ 8*v+16 + literalFetchBudget (Encoding.encodeNat v) entries + 9*payload.length+10,
      ∃ regs', Eval fetchLiteral n d
        (literalFrame d regs' positive [] [] payload (Squarefree.Program.lookupRecords entries)) ∧
        regs' 4 = true := by
  obtain ⟨n,hn,rr,he,hf⟩ := canonicalLiteral_hit regs old positive v payload entries hlookup
  rw [← hports] at he
  exact ⟨n+1,by omega,rr,
    eval_liftCommand_from_state canonicalLiteral 2 5 literalRegisters literalStacks d
      literalRegisters_injective literalStacks_injective he,hf⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral_from_state_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral_from_state_oai
