-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:44:45.314362+00:00
-- url     : https://prove2.me/submissions/8daed4e5-a014-4067-b7ba-a15c0c57f0e2

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S114
import Definitions.Def_OAIQ081S120
import Definitions.Def_OAIQ081S132

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArithmeticExpressionSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ArithmeticExpressionSupport

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem copy_eval {S : ℕ} (src dst tmp : Fin S) (d : Data S)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hd : d.stacks dst = []) (ht : d.stacks tmp = []) :
    Eval (copyCmd src dst tmp) (7 * (d.stacks src).length + 5) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks dst (d.stacks src)⟩ := by
  have h := ListRegisterProgram.copy_run src dst tmp (0 : Fin 8) 1
    hsd hst htd (by decide) d.regs d.stacks ht
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, hd] using h

end SubexponentialSAT.ArithmeticExpressionSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpBlockParameterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual block-size and block-threshold arithmetic

The three input words contain `s`, `delta`, and `Q`.  The width `k` is part
of the fixed code.  Seven high stacks are a reusable empty work bank; the
fifteen low stacks retain inputs, constants, and computed intermediate words.
Every arithmetic operation below invokes a proved finite Boolean program.
-/

namespace SubexponentialSAT.SubexpBlockParameterProgram

open BitProgram StructuredCalls BinaryArithmetic

theorem add_eval (r : Regs) (w : Words) (a b o : Fin 15)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (addCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) + BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      simpa only [arithmeticPorts] using
        (state_work r w (work 5 (by decide) i) (by change 15 ≤ 15 + i.val; omega))
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.addAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [addCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

theorem multiply_eval (r : Regs) (w : Words) (a b o : Fin 15)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (multiplyCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) * BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      simpa only [arithmeticPorts] using
        (state_work r w (work 5 (by decide) i) (by change 15 ≤ 15 + i.val; omega))
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.multiplyAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [multiplyCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

end SubexponentialSAT.SubexpBlockParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashParametersProgramLog
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native logarithmic component of the hash-parameter setup. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram

open BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram

theorem logCommand_eval (xs : List Bool) (d : State 3 3)
    (hs : d.stacks = (Setup.io xs).stacks) :
    ∃ output t, BinaryArithmetic.toNat output = SparseCode.logSize (BinaryArithmetic.toNat xs) ∧
      output.length ≤ xs.length+1 ∧ t ≤ 35*(xs.length+1)^2 ∧
      Eval logCommand t d (Setup.io output) := by
  have hr := SubexpParameterProgram.atoms_eval
    ([.set 0 false, .set 1 false, .set 2 false] : List (StructuredProgram.Atom 3 3)) d
  have hh : SubexpParameterProgram.runAtoms
      [.set 0 false, .set 1 false, .set 2 false] d = Setup.io xs := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · exact hs
  obtain ⟨output,t,hv,hl,ht,he⟩ := Setup.logSucc_eval xs
  refine ⟨output,3+t,?_,hl,by nlinarith,.seq (.base (hh ▸ hr)) he⟩
  simpa only [SubexpParameterProgram.value_eq_toNat, SparseCode.logSize, Nat.log2_eq_log_two] using hv

theorem logCall_eval (r : Regs) (w : Words) :
    ∃ t rf output,
      Eval logCall t (state r w) (state rf (Function.update w 3 output)) ∧
      BinaryArithmetic.toNat output = SparseCode.logSize (BinaryArithmetic.toNat (w 3)) ∧
      output.length ≤ (w 3).length+1 ∧ t ≤ 36*((w 3).length+1)^2 := by
  have hi : Function.Injective logRegisters := Fin.castAdd_injective _ _
  have hj : Function.Injective logStacks := by decide
  let d := state r w
  have hs : (projectState logRegisters logStacks d).stacks = (Setup.io (w 3)).stacks := by
    funext i
    fin_cases i
    · change (state r w).stacks (port 3) = w 3
      exact state_port r w 3
    · change (state r w).stacks (15 : Fin 22) = []
      exact state_work r w 15 (by decide)
    · change (state r w).stacks (16 : Fin 22) = []
      exact state_work r w 16 (by decide)
  obtain ⟨output,t,hv,hl,ht,he⟩ := logCommand_eval (w 3)
    (projectState logRegisters logStacks d) hs
  let e := embedState logRegisters logStacks d (Setup.io output)
  have hr : Eval logCall (t+1) d e :=
    eval_liftCommand_from_state logCommand 0 0 logRegisters logStacks d hi hj he
  have hw : (Setup.io output).stacks =
      Function.update (projectState logRegisters logStacks d).stacks 0 output := by
    rw [hs]; funext i; fin_cases i <;> simp []
  have hse : e.stacks = Function.update d.stacks 3 output := by
    change Function.extend logStacks (Setup.io output).stacks d.stacks = _
    rw [hw,ProgramLinking.extend_update hj]
    have hx := congrArg StructuredProgram.State.stacks (embedState_project logRegisters logStacks d hi hj)
    change Function.extend logStacks (projectState logRegisters logStacks d).stacks d.stacks = d.stacks at hx
    rw [hx]; rfl
  have heq : e = state e.regs (Function.update w 3 output) := by
    rw [← state_update r e.regs w 3 output]
    exact CounterForPrograms.data_ext rfl hse
  refine ⟨t+1,e.regs,output,?_,hv,hl,by nlinarith⟩
  rw [← heq]
  exact hr

theorem copyClause_eval (r : Regs) (w : Words) (h3 : w 3 = []) :
    Eval copyClause (7*(w 1).length+5) (state r w)
      (state (readRegs r 0 1 none) (Function.update w 3 (w 1))) := by
  have h := ArithmeticExpressionSupport.copy_eval (port 1) (port 3) 21 (state r w)
    (by decide) (by decide) (by decide)
    (by simpa only [state_port] using h3) (state_work r w 21 (by decide))
  simp only [state_port] at h
  rw [state_update] at h
  exact h

end SubexponentialSAT.SqrtLog.HashParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical storage operations for the closed parameter setup

All copies, clears, and register resets are fixed instruction sequences or
calls to proved bit programs. Their state transformations below are assertion
notation only. The setup program uses them to isolate dirty arithmetic
subroutines from the persistent parameter words.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem finish_empty {S : ℕ} (ports : List (Fin S)) (outputs : List (Fin S × Fin S))
    (a : Data S) (i : Fin S) (hi : i ∈ ports) :
    (finishState ports outputs a).stacks i = [] := by
  rw [finishState, resetMany_stacks, clearMany_stacks, ite_eq_left hi]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and value rules for the actual setup copy/cleanup routines. -/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem prepare_frame {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (ht : i ≠ tmp) (hp : i ∉ ports) (hi : ∀ p ∈ inputs, i ≠ p.2) :
    (prepareState tmp ports inputs a).stacks i = a.stacks i := by
  unfold prepareState beforeCopies
  rw [copyMany_frame _ _ _ hi, resetMany_stacks, clearMany_stacks,
    ite_eq_right hp, clearMany_stacks]
  simp [ht]

theorem finish_frame {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (hp : i ∉ ports) (ho : ∀ p ∈ outputs, i ≠ p.2) :
    (finishState ports outputs a).stacks i = a.stacks i := by
  have hmem : i ∉ outputs.map Prod.snd := by
    intro hi
    obtain ⟨p, hm, he⟩ := List.mem_map.mp hi
    exact ho p hm he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hp,
    copyMany_frame _ _ _ ho, clearMany_stacks, ite_eq_right hmem]

theorem finish_value {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S)
    (hdup : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (p : Fin S × Fin S) (hp : p ∈ outputs) (hport : p.2 ∉ ports) :
    (finishState ports outputs a).stacks p.2 = a.stacks p.1 := by
  have hc : ∀ q ∈ outputs, (clearManyState (outputs.map Prod.snd) a).stacks q.2 = [] := by
    intro q hq
    rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩)]
  have hs : p.1 ∉ outputs.map Prod.snd := by
    intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    exact hsep p hp q hq he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hport,
    copyMany_value _ _ hdup hc hsep p hp, clearMany_stacks, ite_eq_right hs]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorageCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cost of the concrete setup storage instructions

Copying and cleanup are charged by the lengths of the words physically read.
The final stage bound is linear in a common word bound; its coefficients depend
only on the statically allocated ports and copy lists.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem resetMany_wordBound {S : ℕ} (rs : List (Fin 16)) (a : Data S) (B : ℕ)
    (ha : WordBound B a) : WordBound B (resetManyState rs a) := by
  intro i
  simpa only [resetMany_stacks] using ha i

theorem beforeCopies_wordBound {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (a : Data S) (B : ℕ) (ha : WordBound B a) :
    WordBound B (beforeCopies tmp ports a) :=
  resetMany_wordBound _ _ B
    (clearMany_wordBound ports _ B (clearMany_wordBound [tmp] a B ha))

theorem prepare_wordBound {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (inputs.map Prod.snd).Nodup)
    (hp : ∀ p ∈ inputs, p.2 ∈ ports)
    (hsep : ∀ p ∈ inputs, ∀ q ∈ inputs, p.1 ≠ q.2)
    (ha : WordBound B a) : WordBound B (prepareState tmp ports inputs a) := by
  apply copyMany_wordBound inputs _ B hd _ hsep (beforeCopies_wordBound tmp ports a B ha)
  intro p hm
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks, ite_eq_left (hp p hm)]

theorem prepareCost_le {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hsep : ∀ p ∈ inputs, ∀ q ∈ inputs, p.1 ≠ q.2)
    (ha : WordBound B a) :
    prepareCost tmp ports inputs a ≤
      (2 * B + 3) + (ports.length * (2 * B + 3) + (9 + inputs.length * (7 * B + 5))) := by
  have htmp := clearManyCost_le [tmp] a B ha
  have hports := clearManyCost_le ports (clearManyState [tmp] a) B
    (clearMany_wordBound [tmp] a B ha)
  have hcopy := copyManyCost_le inputs (beforeCopies tmp ports a) B hsep
    (fun p _ => beforeCopies_wordBound tmp ports a B ha p.1)
  simpa only [prepareCost, List.length_singleton, one_mul] using
    Nat.add_le_add htmp (Nat.add_le_add hports (Nat.add_le_add_left hcopy 9))

theorem finishCopies_wordBound {S : ℕ} (outputs : List (Fin S × Fin S))
    (a : Data S) (B : ℕ) (hd : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (ha : WordBound B a) :
    WordBound B (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)) := by
  apply copyMany_wordBound outputs _ B hd _ hsep
    (clearMany_wordBound (outputs.map Prod.snd) a B ha)
  intro p hp
  rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨p, hp, rfl⟩)]

theorem finishCost_le {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (ha : WordBound B a) :
    finishCost ports outputs a ≤ outputs.length * (2 * B + 3) +
      (outputs.length * (7 * B + 5) + (ports.length * (2 * B + 3) + 9)) := by
  have hout := clearManyCost_le (outputs.map Prod.snd) a B ha
  have hcopy := copyManyCost_le outputs (clearManyState (outputs.map Prod.snd) a) B hsep
    (fun p _ => clearMany_wordBound (outputs.map Prod.snd) a B ha p.1)
  have hports := clearManyCost_le ports
    (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)) B
    (finishCopies_wordBound outputs a B hd hsep ha)
  simpa only [finishCost, List.length_map] using
    Nat.add_le_add hout (Nat.add_le_add hcopy (Nat.add_le_add_right hports 9))

theorem embedState_wordBound {r s S : ℕ} (register : Fin r → Fin 16)
    (stack : Fin s → Fin S) (frame : Data S) (out : State r s) (B : ℕ)
    (hs : Function.Injective stack) (hf : WordBound B frame) (ho : WordBound B out) :
    WordBound B (embedState register stack frame out) := by
  intro i
  by_cases hm : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hm
    rw [embedState_stack register stack frame out hs j]
    exact ho j
  · rw [embedState_stack_frame register stack frame out i hm]
    exact hf i

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashParametersProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production hash-parameter program. The arithmetic, ABI, and cost proofs
are checked together; the former split module paths remain compatibility
imports of this file. -/

/-! Fixed native arithmetic for alphabet size, sparse-code distance parameter,
and selector round cap. Every operation is a proved finite Boolean program. -/

namespace SubexponentialSAT.SqrtLog.HashParametersProgram

open BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram

private theorem time_bound {t a W : ℕ} (ht : t ≤ 100*a^2)
    (ha : a ≤ 100*W) : t ≤ 1000000*W^2 := by
  calc
    t ≤ 100*a^2 := ht
    _ ≤ 100*(100*W)^2 := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left ha 2)
    _ = 1000000*W^2 := by ring

theorem command_eval (regs : Regs) (n m B : List Bool) (hm : BinaryArithmetic.toNat m ≠ 0) :
    ∃ t rf output, Eval command t (state regs (inputWords n m B)) (state rf output) ∧
      BinaryArithmetic.toNat (output 14) = 3 * BinaryArithmetic.toNat m ∧
      BinaryArithmetic.toNat (output 9) = SparseCode.distanceDenom (BinaryArithmetic.toNat m) (BinaryArithmetic.toNat B) ∧
      BinaryArithmetic.toNat (output 13) = HashSelect.loopCap (BinaryArithmetic.toNat n) (BinaryArithmetic.toNat m) ∧
      (∀ i, (output i).length ≤ 100 * width n m B) ∧
      t ≤ 100000000 * (width n m B)^2 := by
  have len3 : ([true,true] : List Bool).length = 2 := by decide
  have len20000 : ([false,false,false,false,false,true,false,false,false,true,true,true,false,false,true] : List Bool).length = 15 := by decide
  have len1 : ([true] : List Bool).length = 1 := by decide
  have val20000 : BinaryArithmetic.toNat ([false,false,false,false,false,true,false,false,false,true,true,true,false,false,true] : List Bool) = 20000 := by decide
  have val3 : BinaryArithmetic.toNat ([true,true] : List Bool) = 3 := by decide
  have val1 : BinaryArithmetic.toNat ([true] : List Bool) = 1 := by decide
  let w0 := inputWords n m B
  have h0 := copyClause_eval regs w0 (by simp [w0,inputWords])
  let r0 := readRegs regs 0 1 none
  let w1 := Function.update w0 3 (w0 1)
  obtain ⟨tl,rl,vl,hl,hvl,hll,htl⟩ := logCall_eval r0 w1
  let w2 := Function.update w1 3 vl
  obtain ⟨r3,h3⟩ := load_eval rl w2 4 ([true,true] : List Bool) (by simp [w0,w1,w2,inputWords])
  let w3 := Function.update w2 4 ([true,true] : List Bool)
  obtain ⟨r4,h4⟩ := load_eval r3 w3 5 ([false,false,false,false,false,true,false,false,false,true,true,true,false,false,true] : List Bool) (by simp [w0,w1,w2,w3,inputWords])
  let w4 := Function.update w3 5 ([false,false,false,false,false,true,false,false,false,true,true,true,false,false,true] : List Bool)
  obtain ⟨r5,h5⟩ := load_eval r4 w4 11 ([true] : List Bool) (by simp [w0,w1,w2,w3,w4,inputWords])
  let w5 := Function.update w4 11 ([true] : List Bool)
  obtain ⟨t6,r6,v6,h6,hv6,hl6,ht6⟩ := multiply_eval r5 w5 2 2 6
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,inputWords])
  let w6 := Function.update w5 6 v6
  obtain ⟨t7,r7,v7,h7,hv7,hl7,ht7⟩ := multiply_eval r6 w6 3 3 7
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,inputWords])
  let w7 := Function.update w6 7 v7
  obtain ⟨t8,r8,v8,h8,hv8,hl8,ht8⟩ := multiply_eval r7 w7 6 7 8
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,w7,inputWords])
  let w8 := Function.update w7 8 v8
  obtain ⟨t9,r9,v9,h9,hv9,hl9,ht9⟩ := multiply_eval r8 w8 5 8 9
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,inputWords])
  let w9 := Function.update w8 9 v9
  obtain ⟨t10,r10,v10,h10,hv10,hl10,ht10⟩ := add_eval r9 w9 0 3 10
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,inputWords])
  let w10 := Function.update w9 10 v10
  obtain ⟨t11,r11,v11,h11,hv11,hl11,ht11⟩ := add_eval r10 w10 10 11 12
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,inputWords])
  let w11 := Function.update w10 12 v11
  obtain ⟨t12,r12,v12,h12,hv12,hl12,ht12⟩ := add_eval r11 w11 12 12 13
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,inputWords])
  let w12 := Function.update w11 13 v12
  obtain ⟨t13,r13,v13,h13,hv13,hl13,ht13⟩ := multiply_eval r12 w12 1 4 14
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords])
  let w13 := Function.update w12 14 v13
  refine ⟨(7*(w0 1).length+5)+((tl)+((2*([true,true] : List Bool).length)+((2*([false,false,false,false,false,true,false,false,false,true,true,true,false,false,true] : List Bool).length)+((2*([true] : List Bool).length)+((t6)+((t7)+((t8)+((t9)+((t10)+((t11)+((t12)+(t13)))))))))))),r13,w13,?_,?_,?_,?_,?_,?_⟩
  · exact h0.seq (hl.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13))))))))))))
  · simp only [w13,Function.update_self]
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,val1,val3,val20000] at hvl hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13
    rw [hv13]
    omega
  · simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,inputWords]
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,val1,val3,val20000] at hvl hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13
    rw [hv9,hv8,hv7,hv6,hvl]
    dsimp [SparseCode.distanceDenom]
    ring
  · simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,inputWords]
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,val1,val3,val20000] at hvl hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13
    rw [hv12,hv11,hv10,hvl]
    rw [HashSelect.loopCap,LeafParametersProgram.size_eq_log2_add_one hm]
    simp only [SparseCode.logSize,Nat.log2_eq_log_two]
    omega
  · intro i
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,len3,len20000,len1] at hll hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 htl ht6 ht7 ht8 ht9 ht10 ht11 ht12 ht13
    fin_cases i <;> simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,inputWords,len3,len20000,len1] <;> dsimp [width] <;> omega
  ·
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,len3,len20000,len1] at hll hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 htl ht6 ht7 ht8 ht9 ht10 ht11 ht12 ht13
    let W := width n m B
    have hW : 1 ≤ W := by dsimp [W,width]; omega
    have hb6 : (w5 2).length + (w5 2).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,inputWords]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,inputWords] at hb6
    have hc6 := time_bound ht6 hb6
    have hb7 : (w6 3).length + (w6 3).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,inputWords]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,inputWords] at hb7
    have hc7 := time_bound ht7 hb7
    have hb8 : (w7 6).length + (w7 7).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,w7,inputWords]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,w7,inputWords] at hb8
    have hc8 := time_bound ht8 hb8
    have hb9 : (w8 5).length + (w8 8).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,inputWords,len20000]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,inputWords,len20000] at hb9
    have hc9 := time_bound ht9 hb9
    have hb10 : (w9 0).length + (w9 3).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,inputWords]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,inputWords] at hb10
    have hc10 := time_bound ht10 hb10
    have hb11 : (w10 10).length + (w10 11).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,inputWords,len1]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,inputWords,len1] at hb11
    have hc11 := time_bound ht11 hb11
    have hb12 : (w11 12).length + (w11 12).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,inputWords]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,inputWords] at hb12
    have hc12 := time_bound ht12 hb12
    have hb13 : (w12 1).length + (w12 4).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,len3]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,len3] at hb13
    have hc13 := time_bound ht13 hb13
    have hlog : (m.length+1)^2 ≤ W^2 := by
      apply Nat.pow_le_pow_left
      dsimp [W,width]
      omega
    have hcl : tl ≤ 36*W^2 := htl.trans (Nat.mul_le_mul_left 36 hlog)
    have hml : m.length ≤ W := by dsimp [W,width]; omega
    have hcopy : 7*m.length+41 ≤ 100*W^2 := by
      nlinarith only [hml,hW]
    change _ ≤ 100000000*W^2
    simp only [len3,len20000,len1]
    change 7*m.length+5 + (tl + (2*2 + (2*15 + (2*1 +
      (t6 + (t7 + (t8 + (t9 + (t10 + (t11 + (t12 + t13))))))))))) ≤ _
    omega

end SubexponentialSAT.SqrtLog.HashParametersProgram


/-! Exact metadata loading and selector-port installation. Metadata is outside
all fourteen selector ports. The fixed scratch bank is physically cleared. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open BitProgram StructuredCalls SubexpSetupStorage

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _
theorem stackMap_injective : Function.Injective stackMap := by
  intro i j h; apply Fin.ext
  have := congrArg Fin.val h
  dsimp [stackMap] at this
  omega

theorem work_mem (i : Fin 44) : i ∈ work ↔ 17 ≤ i.val ∧ i.val < 39 := by
  simp only [work,List.mem_ofFn]
  constructor
  · rintro ⟨j,rfl⟩; dsimp [stackMap]; have := j.isLt; omega
  · intro hi; exact ⟨⟨i.val-17,by omega⟩,Fin.ext (by dsimp [stackMap]; omega)⟩

theorem inputs_good : ∀ p ∈ inputs,
    p.1 ≠ p.2 ∧ p.1 ≠ (39 : Fin 44) ∧ 39 ≠ p.2 := by
  intro p hp; simp only [inputs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl|rfl <;> decide

theorem outputs_good : ∀ p ∈ outputs,
    p.1 ≠ p.2 ∧ p.1 ≠ (39 : Fin 44) ∧ 39 ≠ p.2 := by
  intro p hp; simp only [outputs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl|rfl <;> decide

theorem prepared_project (a : Data) :
    project registers stackMap (prepared a) =
      SubexpBlockParameterProgram.state ((prepared a).regs ∘ registers)
        (HashParametersProgram.inputWords (a.stacks 14) (a.stacks 15) (a.stacks 16)) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;>
      simp +decide [prepared,prepareState,beforeCopies,copyManyState,inputs,copyState,
        StackRoutines.copyStacks,resetMany_stacks,clearMany_stacks,stackMap,HashParametersProgram.inputWords,Fin.reduceFinMk]

theorem returned_frame (a : Data) (out : State 8 22) (i : Fin 44)
    (hw : i ∉ work) (ht : i ≠ 39)
    (h0 : i ≠ 0) (h5 : i ≠ 5) (h6 : i ≠ 6) :
    (returned a out).stacks i = a.stacks i := by
  rw [returned,finish_frame]
  · rw [embedState_stack_frame]
    · apply prepare_frame _ _ _ _ _ ht hw
      intro p hp
      simp only [inputs,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl|rfl|rfl
      all_goals intro he; apply hw; rw [he]; rw [work_mem]; decide
    · rintro ⟨j,hj⟩
      apply hw
      rw [← hj]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · exact hw
  · intro p hp
    simp only [outputs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · exact h0
    · exact h5
    · exact h6

theorem returned_value (a : Data) (out : State 8 22)
    (p : Fin 44 × Fin 44) (hp : p ∈ outputs) :
    (returned a out).stacks p.2 = (embedState registers stackMap (prepared a) out).stacks p.1 := by
  refine finish_value work outputs _ (by decide) ?_ p hp ?_
  · intro q hq z hz
    simp only [outputs,List.mem_cons,List.mem_nil_iff,or_false] at hq hz
    rcases hq with rfl|rfl|rfl <;> rcases hz with rfl|rfl|rfl <;> decide
  · simp only [outputs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl <;> (rw [work_mem]; decide)

theorem returned_values (a : Data) (out : State 8 22) :
    (returned a out).stacks 0 = out.stacks 14 ∧
    (returned a out).stacks 5 = out.stacks 9 ∧
    (returned a out).stacks 6 = out.stacks 13 := by
  have h0 := returned_value a out (31,0) (by simp [outputs])
  have h5 := returned_value a out (26,5) (by simp [outputs])
  have h6 := returned_value a out (30,6) (by simp [outputs])
  have e0 := embedState_stack registers stackMap (prepared a) out stackMap_injective 14
  have e5 := embedState_stack registers stackMap (prepared a) out stackMap_injective 9
  have e6 := embedState_stack registers stackMap (prepared a) out stackMap_injective 13
  exact ⟨h0.trans e0,h5.trans e5,h6.trans e6⟩

/-- No generic semantic callback is used: the only invoked program is the
fixed HashParametersProgram.command defined in the preceding module. -/
theorem command_eval (a : Data) (hm : BinaryArithmetic.toNat (a.stacks 15) ≠ 0) :
    ∃ t rf output,
      let out := SubexpBlockParameterProgram.state rf output
      Eval command (prepareCost 39 work inputs a +
        (t+1+finishCost work outputs (embedState registers stackMap (prepared a) out)))
        a (returned a out) ∧
      BinaryArithmetic.toNat ((returned a out).stacks 0) = 3*BinaryArithmetic.toNat (a.stacks 15) ∧
      BinaryArithmetic.toNat ((returned a out).stacks 5) =
        SparseCode.distanceDenom (BinaryArithmetic.toNat (a.stacks 15)) (BinaryArithmetic.toNat (a.stacks 16)) ∧
      BinaryArithmetic.toNat ((returned a out).stacks 6) =
        HashSelect.loopCap (BinaryArithmetic.toNat (a.stacks 14)) (BinaryArithmetic.toNat (a.stacks 15)) ∧
      (∀ i, (output i).length ≤ 100*HashParametersProgram.width (a.stacks 14) (a.stacks 15) (a.stacks 16)) ∧
      t ≤ 100000000*(HashParametersProgram.width (a.stacks 14) (a.stacks 15) (a.stacks 16))^2 := by
  obtain ⟨t,rf,output,he,h0,h5,h6,hl,ht⟩ := HashParametersProgram.command_eval
    ((prepared a).regs ∘ registers) (a.stacks 14) (a.stacks 15) (a.stacks 16) hm
  let out := SubexpBlockParameterProgram.state rf output
  have tr := compiled_halt_trace he 0 14
  have tr' : Trace coreProgram (t+1)
      ((project registers stackMap (prepared a)).withPC (some coreProgram.entry))
      (out.withPC none) := by
    rw [prepared_project]
    exact tr
  have run := isolated_eval coreProgram registers stackMap registers_injective stackMap_injective
    39 work inputs outputs a out inputs_good outputs_good
    (by rintro ⟨j,hj⟩; have := congrArg Fin.val hj; have := j.isLt; dsimp [stackMap] at *; omega)
    tr'
  have hv := returned_values a out
  refine ⟨t,rf,output,run,?_,?_,?_,hl,ht⟩
  · rw [hv.1]; exact h0
  · rw [hv.2.1]; exact h5
  · rw [hv.2.2]; exact h6

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI


/-! Polynomial step budget for the complete physical parameter setup. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open BitProgram StructuredCalls SubexpSetupStorage

theorem inputs_separated : ∀ p ∈ inputs, ∀ q ∈ inputs, p.1 ≠ q.2 := by
  intro p hp q hq
  simp only [inputs,List.mem_cons,List.mem_nil_iff,or_false] at hp hq
  rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;> decide

theorem outputs_separated : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2 := by
  intro p hp q hq
  simp only [outputs,List.mem_cons,List.mem_nil_iff,or_false] at hp hq
  rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;> decide

theorem prepared_wordBound (a : Data) (L : ℕ) (ha : WordBound L a) :
    WordBound L (prepared a) := by
  apply prepare_wordBound 39 work inputs a L (by decide) _ inputs_separated ha
  intro p hp
  simp only [inputs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl|rfl <;> (rw [work_mem]; decide)

theorem command_bounded (a : Data) (L : ℕ) (ha : WordBound L a)
    (hm : BinaryArithmetic.toNat (a.stacks 15) ≠ 0) :
    ∃ cost b, Eval command cost a b ∧ cost ≤ 10000000000*(L+1)^2 ∧
      BinaryArithmetic.toNat (b.stacks 0) = 3*BinaryArithmetic.toNat (a.stacks 15) ∧
      BinaryArithmetic.toNat (b.stacks 5) =
        SparseCode.distanceDenom (BinaryArithmetic.toNat (a.stacks 15)) (BinaryArithmetic.toNat (a.stacks 16)) ∧
      BinaryArithmetic.toNat (b.stacks 6) =
        HashSelect.loopCap (BinaryArithmetic.toNat (a.stacks 14)) (BinaryArithmetic.toNat (a.stacks 15)) ∧
      (∀ i, i ∉ work → i ≠ 39 → i ≠ 0 → i ≠ 5 → i ≠ 6 → b.stacks i = a.stacks i) ∧
      (∀ i ∈ work, b.stacks i = []) := by
  obtain ⟨t,rf,output,he,h0,h5,h6,hl,ht⟩ := command_eval a hm
  let out := SubexpBlockParameterProgram.state rf output
  let mid := embedState registers stackMap (prepared a) out
  let W := HashParametersProgram.width (a.stacks 14) (a.stacks 15) (a.stacks 16)
  have hW : W ≤ 4*(L+1) := by
    have h14 := ha 14
    have h15 := ha 15
    have h16 := ha 16
    dsimp [W,HashParametersProgram.width]
    omega
  have hLC : L ≤ 400*(L+1) := by omega
  have hp : WordBound (400*(L+1)) (prepared a) :=
    fun i => (prepared_wordBound a L ha i).trans hLC
  have ho : WordBound (400*(L+1)) out := by
    intro i
    dsimp [out,SubexpBlockParameterProgram.state]
    split
    · exact (hl _).trans (by change 100*W ≤ _; omega)
    · simp
  have hmid : WordBound (400*(L+1)) mid :=
    embedState_wordBound registers stackMap (prepared a) out _ stackMap_injective hp ho
  have hprep := prepareCost_le 39 work inputs a L inputs_separated ha
  have hfinish := finishCost_le work outputs mid (400*(L+1))
    (by decide) outputs_separated hmid
  have hpow := Nat.pow_le_pow_left hW 2
  have hcost : prepareCost 39 work inputs a + (t+1+finishCost work outputs mid)
      ≤ 10000000000*(L+1)^2 := by
    simp only [work,List.length_ofFn,inputs,outputs,List.length_cons,List.length_nil] at hprep hfinish
    change t ≤ 100000000*W^2 at ht
    simp only [work,inputs,outputs]
    nlinarith
  refine ⟨_,returned a out,he,hcost,h0,h5,h6,?_,?_⟩
  · exact returned_frame a out
  · intro i hi
    exact finish_empty work outputs mid i hi

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI


/-! Exported fixed program and the selector's actual fourteen-port interface. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open BitProgram StructuredCalls SubexpSetupStorage

theorem command_ready_eval (a : Data) (L : ℕ) (ha : WordBound L a) (hr : ReadyInput a)
    (hm : BinaryArithmetic.toNat (a.stacks 15) ≠ 0) :
    ∃ t ≤ 10000000000*(L+1)^2, ∃ b, Eval command t a b ∧
      Execution.HashInputs.Ready (selectorState b) ∧
      BinaryArithmetic.toNat (b.stacks 0) = 3*BinaryArithmetic.toNat (a.stacks 15) ∧
      BinaryArithmetic.toNat (b.stacks 5) =
        SparseCode.distanceDenom (BinaryArithmetic.toNat (a.stacks 15)) (BinaryArithmetic.toNat (a.stacks 16)) ∧
      BinaryArithmetic.toNat (b.stacks 6) =
        HashSelect.loopCap (BinaryArithmetic.toNat (a.stacks 14)) (BinaryArithmetic.toNat (a.stacks 15)) ∧
      b.stacks 9 = a.stacks 9 ∧
      (∀ i, i ∉ work → i ≠ 39 → i ≠ 0 → i ≠ 5 → i ≠ 6 → b.stacks i = a.stacks i) := by
  obtain ⟨t,b,he,ht,h0,h5,h6,hframe,hclean⟩ := command_bounded a L ha hm
  refine ⟨t,ht,b,he,?_,h0,h5,h6,?_,hframe⟩
  · intro i hi0 hi5 hi6 hi9
    have hw : selectorStacks i ∉ work := by
      rw [work_mem]
      have := i.isLt
      change ¬ (17 ≤ i.val ∧ i.val < 39)
      omega
    have hh := hframe (selectorStacks i) hw (by
        intro h
        have hv := congrArg (fun x : Fin 44 => x.val) h
        change i.val=39 at hv
        have := i.isLt
        omega)
      (by intro h; apply hi0; exact Fin.ext (show i.val=0 from congrArg (fun x : Fin 44 => x.val) h))
      (by intro h; apply hi5; exact Fin.ext (show i.val=5 from congrArg (fun x : Fin 44 => x.val) h))
      (by intro h; apply hi6; exact Fin.ext (show i.val=6 from congrArg (fun x : Fin 44 => x.val) h))
    change b.stacks (selectorStacks i) = []
    rw [hh]
    exact hr i hi0 hi5 hi6 hi9
  · exact hframe 9 (by rw [work_mem]; decide) (by decide) (by decide) (by decide) (by decide)

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ExecutionHashParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the actual metadata arithmetic into a caller which also
holds the formula and ring context. Only binary n, m and B are supplied;
3m, the tuple depth and the number of hash rounds are computed by the fixed
parameter program. The empty-formula branch is handled by the leaf caller. -/

namespace SubexponentialSAT.SqrtLog.Execution.HashParameters

open BitProgram StructuredCalls

theorem command_eval_oai {R S : ℕ} (p : Ports R S) (a : State R S) (L : ℕ)
    (hword : SubexpSetupStorage.WordBound L (projectState p.register p.stack a))
    (hready : HashInputs.Ready (projectState p.hash.register p.hash.stack a))
    (hm : BinaryArithmetic.toNat (a.stacks (p.stack 15)) ≠ 0) :
    ∃ t ≤ 10000000000*(L+1)^2+1, ∃ b : State R S,
      Eval (command p) t a b ∧
      HashInputs.Ready (projectState p.hash.register p.hash.stack b) ∧
      BinaryArithmetic.toNat (b.stacks (p.hash.stack 0)) =
        3*BinaryArithmetic.toNat (a.stacks (p.stack 15)) ∧
      BinaryArithmetic.toNat (b.stacks (p.hash.stack 5)) =
        SparseCode.distanceDenom (BinaryArithmetic.toNat (a.stacks (p.stack 15)))
          (BinaryArithmetic.toNat (a.stacks (p.stack 16))) ∧
      BinaryArithmetic.toNat (b.stacks (p.hash.stack 6)) =
        HashSelect.loopCap (BinaryArithmetic.toNat (a.stacks (p.stack 14)))
          (BinaryArithmetic.toNat (a.stacks (p.stack 15))) ∧
      b.stacks (p.hash.stack 9) = a.stacks (p.hash.stack 9) ∧
      (∀ i, i ∉ HashParametersProgram.ABI.work → i ≠ 39 → i ≠ 0 → i ≠ 5 → i ≠ 6 →
        b.stacks (p.stack i) = a.stacks (p.stack i)) ∧
      (∀ i, (∀ j, p.stack j ≠ i) → b.stacks i = a.stacks i) ∧
      (∀ i, (∀ j, p.register j ≠ i) → b.regs i = a.regs i) := by
  obtain ⟨t,ht,c,hc,hr,h0,h5,h6,h9,hframe⟩ :=
    HashParametersProgram.ABI.command_ready_eval
      (projectState p.register p.stack a) L hword hready hm
  let b := embedState p.register p.stack a c
  have hs (i : Fin 44) : b.stacks (p.stack i) = c.stacks i :=
    embedState_stack p.register p.stack a c p.stack_injective i
  refine ⟨t+1,Nat.add_le_add_right ht 1,b,
    eval_liftCommand_from_state _ _ _ _ _ _ p.register_injective p.stack_injective hc,
    ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi0 hi5 hi6 hi9
    change b.stacks (p.stack (HashParametersProgram.ABI.selectorStacks i)) = []
    rw [hs]
    exact hr i hi0 hi5 hi6 hi9
  · change BinaryArithmetic.toNat (b.stacks (p.stack 0)) = _
    rw [hs]
    exact h0
  · change BinaryArithmetic.toNat (b.stacks (p.stack 5)) = _
    rw [hs]
    exact h5
  · change BinaryArithmetic.toNat (b.stacks (p.stack 6)) = _
    rw [hs]
    exact h6
  · change b.stacks (p.stack 9) = a.stacks (p.stack 9)
    exact (hs 9).trans h9
  · intro i hi h39 h0 h5 h6
    exact (hs i).trans (hframe i hi h39 h0 h5 h6)
  · intro i hi
    exact embedState_stack_frame _ _ _ _ i (by rintro ⟨j,hj⟩; exact hi j hj)
  · intro i hi
    exact embedState_register_frame _ _ _ _ i (by rintro ⟨j,hj⟩; exact hi j hj)

end SubexponentialSAT.SqrtLog.Execution.HashParameters

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command_eval_oai
