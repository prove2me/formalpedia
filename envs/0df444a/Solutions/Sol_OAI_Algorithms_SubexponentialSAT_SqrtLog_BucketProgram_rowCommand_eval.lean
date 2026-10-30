-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.rowCommand_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:59:23.881811+00:00
-- url     : https://prove2.me/submissions/c5e35a98-a0c7-420a-b45a-f30602acb221

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S065
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S074
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S083

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

open BitProgram

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clearBankStacks_cons {S : Type u} [DecidableEq S]
    (dst : S) (ports : List S) (stk : Stacks S) :
    clearBankStacks ports (clearStacks dst stk) =
      clearBankStacks (dst :: ports) stk := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [clearBankStacks]
  · simp [clearBankStacks, clearStacks, hj]

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed binary conditional-add kernel for exact offset signatures. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls
open scoped BigOperators

/-- Port0 is the common offset W, port1 is W+A, port2 is the accumulator,
port3 receives the sum. The selected assignment bit is register0. All input
and scratch stacks are preserved; the returned word is genuine binary data. -/
theorem choiceAdd_eval (d : AddData) (hd : addReady d) :
    ∃ t ≤ 100*(addInputLength d+1)^2+1, ∃ rf word,
      Eval choiceAdd t d ⟨rf, Function.update d.stacks 3 word⟩ ∧
      SubexponentialSAT.BinaryArithmetic.toNat word = SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 2) +
        (if d.regs 0 then SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 1)
         else SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 0)) ∧
      word.length ≤ addInputLength d+1 := by
  have hv (b : Bool) : Valid (choicePorts b) d := hd
  cases hb : d.regs 0 with
  | false =>
      obtain ⟨t, rf, word, he, hw, hl, ht⟩ := addAt_eval (choicePorts false) d (hv false)
      refine ⟨t+1, ?_, rf, word, Eval.ite_false hb he, ?_, ?_⟩
      · have hs : (d.stacks (choicePorts false).left).length +
            (d.stacks (choicePorts false).right).length+1 ≤ addInputLength d+1 := by
          simp [choicePorts, addInputLength]; omega
        exact Nat.add_le_add_right (ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _))) 1
      · simpa [choicePorts, hb] using hw
      · exact hl.trans (by simp [choicePorts, addInputLength]; omega)
  | true =>
      obtain ⟨t, rf, word, he, hw, hl, ht⟩ := addAt_eval (choicePorts true) d (hv true)
      refine ⟨t+1, ?_, rf, word, Eval.ite_true hb he, ?_, ?_⟩
      · have hs : (d.stacks (choicePorts true).left).length +
            (d.stacks (choicePorts true).right).length+1 ≤ addInputLength d+1 := by
          simp [choicePorts, addInputLength]; omega
        exact Nat.add_le_add_right (ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _))) 1
      · simpa [choicePorts, hb] using hw
      · exact hl.trans (by simp [choicePorts, addInputLength]; omega)

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_WorkspaceCleanupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual fixed workspace cleanup

The selected ports are part of the finite program. Their initial contents
and lengths are arbitrary. Every clear is an existing measured instruction
loop, and all unselected stacks and non-scratch registers are preserved.
-/

namespace SubexponentialSAT.WorkspaceCleanupProgram

open BitProgram StackRoutines StructuredCalls

theorem finalRegs_after_reset {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (regs : Fin r → Bool) :
    finalRegs value present ports (readRegs regs value present none) =
      readRegs regs value present none := by
  cases ports <;> simp [finalRegs, readRegs_reset]

theorem command_eval {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (hnodup : ports.Nodup) (d : State r s) :
    Eval (command value present ports) (cost ports d) d (finish value present ports d) := by
  rcases d with ⟨regs, stk⟩
  induction ports generalizing regs stk with
  | nil =>
      simpa [command, cost, finish, finalRegs] using
        (Eval.base (StructuredProgram.Eval.skip (⟨regs, stk⟩ : State r s)))
  | cons port rest ih =>
      have hn := List.nodup_cons.mp hnodup
      have hmap : rest.map (fun i => (clearStacks port stk i).length) =
          rest.map (fun i => (stk i).length) := by
        apply List.map_congr_left
        intro i hi
        have hne : i ≠ port := by
          intro h
          subst i
          exact hn.1 hi
        rw [clearStacks_frame port i stk hne]
      have hfirst := BankRoutines.clear_call_eval port value present regs stk
      have hrest := ih hn.2 (readRegs regs value present none) (clearStacks port stk)
      have hrun := Eval.seq hfirst hrest
      simpa only [command, cost, finish, finalRegs_after_reset, finalRegs_cons,
        List.map_cons, List.sum_cons, List.length_cons, hmap,
        BankRoutines.clearBankStacks_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrun

end SubexponentialSAT.WorkspaceCleanupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramDot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual row-entry parsing, assignment-bit scanning, binary addition and
workspace recycling for one exact offset-signature row. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

theorem choicePort_injective : Function.Injective choicePort := Fin.castAdd_injective _ _

theorem choiceCall_eval (d : DotData) (hd : addReady (addView d)) :
    ∃ t ≤ 100*(addInputLength (addView d)+1)^2+2, ∃ rf word,
      Eval choiceCall t d ⟨rf, Function.update d.stacks 3 word⟩ ∧
      SubexponentialSAT.BinaryArithmetic.toNat word = SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 2) +
        (if d.regs 0 then SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 1)
         else SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 0)) ∧
      word.length ≤ addInputLength (addView d)+1 := by
  obtain ⟨t, ht, rf, word, he, hv, hl⟩ := choiceAdd_eval (addView d) hd
  have hp : projectState id choicePort d = addView d := rfl
  have he' := eval_call_from_state choiceAddProgram id choicePort d
    Function.injective_id choicePort_injective (compiled_halt_trace he 0 3)
  have hend : embedState id choicePort d ⟨rf, Function.update (addView d).stacks 3 word⟩ =
      (⟨rf, Function.update d.stacks 3 word⟩ : DotData) := by
    apply embedState_eq_of_ports id choicePort d _ _ Function.injective_id choicePort_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨3, h.symm⟩
      simp [h3]
  rw [hend] at he'
  exact ⟨t+1, by omega, rf, word, he', hv, hl⟩

theorem dotStep_eval (regs : Fin 8 → Bool) (W coeff : List Bool)
    (coeffs : List (List Bool)) (bit : Bool) (bits acc : List Bool) :
    ∃ t ≤ dotStepBound W coeff acc, ∃ rf out,
      Eval dotStep t (dotState regs W (coeff::coeffs) (bit::bits) acc)
        (dotState rf W coeffs bits out) ∧
      SubexponentialSAT.BinaryArithmetic.toNat out = SubexponentialSAT.BinaryArithmetic.toNat acc +
        (if bit then SubexponentialSAT.BinaryArithmetic.toNat coeff else SubexponentialSAT.BinaryArithmetic.toNat W) ∧
      out.length ≤ W.length+coeff.length+acc.length+1 := by
  let d := dotState regs W (coeff::coeffs) (bit::bits) acc
  obtain ⟨a, hea, hsa⟩ := readWord_eval (9 : Fin 12) 1 11
    (by decide) (by decide) (by decide) d coeff (words coeffs) rfl rfl rfl
  let b : DotData := ⟨readRegs a.regs 0 1 (some bit), Function.update a.stacks 10 bits⟩
  have hpop : Eval popAssignment 1 a b := by
    have ha10 : a.stacks 10 = bit::bits := by rw [hsa]; rfl
    have he := Eval.base (StructuredProgram.Eval.atom
      (StructuredProgram.Atom.pop (10 : Fin 12) (0 : Fin 8) 1) a)
    simpa [popAssignment, b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, ha10] using he
  have hb (i : Fin 12) : b.stacks i =
      (Function.update (Function.update (Function.update d.stacks 9 (words coeffs)) 1 coeff) 10 bits) i := by
    simp [b, hsa]
  have hready : addReady (addView b) := by
    constructor
    · rw [show (addView b).stacks 3 = b.stacks 3 from rfl, hb]; rfl
    · intro i; fin_cases i <;> simp [addView, projectState, choicePort, addWork, b, hsa, d, dotState] <;> rfl
  obtain ⟨tc, htc, rc, out, hec, hvc, hlc⟩ := choiceCall_eval b hready
  let c : DotData := ⟨rc, Function.update b.stacks 3 out⟩
  let e := WorkspaceCleanupProgram.finish (0 : Fin 8) 1 ([1,2] : List (Fin 12)) c
  have heclean := WorkspaceCleanupProgram.command_eval (0 : Fin 8) 1
    ([1,2] : List (Fin 12)) (by decide) c
  obtain ⟨f, hef, hsf⟩ := move_eval (3 : Fin 12) 2 11
    (by decide) (by decide) (by decide) e (by simp [e]) (by simp [e,c,hb,d,dotState])
  have hf : f = dotState f.regs W coeffs bits out := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    rw [hsf]
    funext i
    fin_cases i <;> simp [e, c, hb, d, dotState]
  have hlen : addInputLength (addView b) = W.length+coeff.length+acc.length := by
    simp [addInputLength, addView, projectState, choicePort, hb, d, dotState]
  have hvalue : SubexponentialSAT.BinaryArithmetic.toNat out = SubexponentialSAT.BinaryArithmetic.toNat acc +
      (if bit then SubexponentialSAT.BinaryArithmetic.toNat coeff else SubexponentialSAT.BinaryArithmetic.toNat W) := by
    simpa [b, hsa, d, dotState, readRegs] using hvc
  have he3 : e.stacks 3 = out := by simp [e,c]
  have hcleanCost : WorkspaceCleanupProgram.cost ([1,2] : List (Fin 12)) c =
      2*(coeff.length+acc.length)+6 := by
    simp [WorkspaceCleanupProgram.cost, c, hb, d, dotState]
  have he := hea.seq (hpop.seq (hec.seq (heclean.seq hef)))
  rw [hf] at he
  refine ⟨_, ?_, f.regs, out, he, hvalue, ?_⟩
  · rw [hcleanCost, he3]
    rw [hlen] at htc hlc
    dsimp [dotStepBound]
    nlinarith [Nat.zero_le W.length, Nat.zero_le coeff.length, Nat.zero_le acc.length]
  · simpa [hlen] using hlc

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete measured coefficient scan for one integer signature row.
Runtime EOF controls the loop; no instruction count depends on row length. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

theorem dotPeek_eval (regs : Fin 8 → Bool) (W : List Bool) (coeffs : List (List Bool))
    (bits acc : List Bool) :
    Eval dotPeek 1 (dotState regs W coeffs bits acc) (rowReady regs W coeffs bits acc) := by
  exact Eval.base (StructuredProgram.Eval.atom _ _)

theorem rowReady_nil (regs : Fin 8 → Bool) (W bits acc : List Bool) :
    (rowReady regs W [] bits acc).regs 1 = false := by
  simp [rowReady, dotState, words, readRegs]

theorem rowReady_cons (regs : Fin 8 → Bool) (W c : List Bool)
    (cs : List (List Bool)) (bits acc : List Bool) :
    (rowReady regs W (c::cs) bits acc).regs 1 = true := by
  cases c <;> simp [rowReady, dotState, words, readRegs, Encoding.frame]

theorem dotLoop_eval (regs : Fin 8 → Bool) (W : List Bool) (coeffs : List (List Bool))
    (bits acc : List Bool) (hlen : coeffs.length = bits.length) :
    ∃ t ≤ rowBudget W coeffs acc, ∃ rf out,
      Eval dotLoop t (rowReady regs W coeffs bits acc) (dotState rf W [] [] out) ∧
      SubexponentialSAT.BinaryArithmetic.toNat out = SubexponentialSAT.BinaryArithmetic.toNat acc + rowValue W coeffs bits ∧
      out.length ≤ rowWidth W coeffs acc := by
  induction coeffs generalizing regs bits acc with
  | nil =>
      have hb : bits=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst bits
      refine ⟨1, ?_, (rowReady regs W [] [] acc).regs, acc, ?_, ?_, ?_⟩
      · simp [rowBudget, rowWidth]
      · exact Eval.while_false (rowReady_nil regs W [] acc)
      · simp [rowValue]
      · simp [rowWidth]
  | cons c cs ih =>
      cases bits with
      | nil => simp at hlen
      | cons bit bits =>
          have htail : cs.length=bits.length := by simpa using hlen
          obtain ⟨ts, hts, rs, mid, hes, hvs, hls⟩ := dotStep_eval
            (rowReady regs W (c::cs) (bit::bits) acc).regs W c cs bit bits acc
          obtain ⟨tt, htt, rt, out, het, hvt, hlt⟩ := ih rs bits mid htail
          have hs : Eval dotStep ts (rowReady regs W (c::cs) (bit::bits) acc)
              (dotState rs W cs bits mid) := hes
          have hbody : Eval dotBody (ts+1)
              (rowReady regs W (c::cs) (bit::bits) acc) (rowReady rs W cs bits mid) :=
            hs.seq (dotPeek_eval rs W cs bits mid)
          have he := Eval.while_true (rowReady_cons regs W c cs (bit::bits) acc) hbody het
          have hwidth : rowWidth W cs mid ≤ rowWidth W (c::cs) acc := by
            simp only [rowWidth, List.length_cons, List.map_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
            omega
          have hstart : W.length+c.length+acc.length+2 ≤ rowWidth W (c::cs) acc+2 := by
            simp only [rowWidth, List.length_cons, List.map_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
            omega
          have hstep : ts ≤ 200*(rowWidth W (c::cs) acc+2)^2+30 :=
            hts.trans (Nat.add_le_add_right
              (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left hstart 2)) 30)
          have htailCost : tt ≤ (cs.length+1)*(200*(rowWidth W (c::cs) acc+2)^2+34) := by
            exact htt.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right
              (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (Nat.add_le_add_right hwidth 2) 2)) 34))
          refine ⟨(ts+1)+tt+1, ?_, rt, out, he, ?_, hlt.trans hwidth⟩
          · simp only [rowBudget, List.length_cons]
            nlinarith
          · rw [hvt, hvs]
            simp only [rowValue, List.zipWith_cons_cons, List.sum_cons]
            omega

theorem rowCommand_eval_oai (regs : Fin 8 → Bool) (W : List Bool) (coeffs : List (List Bool))
    (bits acc : List Bool) (hlen : coeffs.length=bits.length) :
    ∃ t ≤ rowBudget W coeffs acc+1, ∃ rf out,
      Eval rowCommand t (dotState regs W coeffs bits acc) (dotState rf W [] [] out) ∧
      SubexponentialSAT.BinaryArithmetic.toNat out = SubexponentialSAT.BinaryArithmetic.toNat acc+rowValue W coeffs bits ∧
      out.length ≤ rowWidth W coeffs acc := by
  obtain ⟨t,ht,rf,out,he,hv,hl⟩ := dotLoop_eval regs W coeffs bits acc hlen
  exact ⟨1+t, by omega, rf,out,(dotPeek_eval regs W coeffs bits acc).seq he,hv,hl⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.rowCommand_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.rowCommand_eval_oai
