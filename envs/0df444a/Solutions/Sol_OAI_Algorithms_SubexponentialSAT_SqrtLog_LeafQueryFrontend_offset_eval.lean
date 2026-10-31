-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offset_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:17:07.644587+00:00
-- url     : https://prove2.me/submissions/d3c7d516-3122-4904-aaf3-bd69c402e13d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S159

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOffsetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native producer of the signed-bucket offset 2*B*(8*Q)^(2*R).
All arithmetic acts on runtime binary words. This offset is unrelated to
the unary scalar-row width 1+2*A*R+Q. -/
namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic
open SubexpBlockParameterProgram

theorem width_pos (B Q R : List Bool) : 1 ≤ width B Q R := by
  unfold width
  exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))

theorem sourceWidth_le_width (B Q R : List Bool) : sourceWidth B Q R+1 ≤ width B Q R := by
  unfold width
  exact Nat.le_mul_of_pos_left _ (by omega)

/-- This bound uses the actual base and exponent word lengths, including
any zero padding. The numerical exponent is an explicit parameter. -/
theorem power_cost_le (a e : List Bool) (L E : ℕ)
    (ha : a.length ≤ L) (he : e.length ≤ L) (hv : BinaryArithmetic.toNat e=E) :
    PowerPrograms.runtimeBound a e+9*e.length+8 ≤ 200*((E+1)*(L+1))^2 := by
  let H := (E+1)*(L+1)
  have hH : 1 ≤ H := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  have hL : L ≤ H := by
    have := Nat.le_mul_of_pos_left (L+1) (by omega : 0 < E+1)
    dsimp [H]
    omega
  have hEL : E*(L+1) ≤ H := Nat.mul_le_mul_right _ (Nat.le_succ E)
  have hLE : (E+1)*L ≤ H := Nat.mul_le_mul_left _ (Nat.le_succ L)
  have hsq : H ≤ H^2 := by nlinarith
  have hfirst : E*(50*(L+1)*(2+(E+1)*L)) ≤ 150*H^2 := by
    calc
      _ = 50*(E*(L+1))*(2+(E+1)*L) := by ring
      _ ≤ 50*H*(2+H) := by gcongr
      _ ≤ _ := by nlinarith
  have hsecond : (E+1)*(16*L+16)=16*H := by dsimp [H]; ring
  calc
    _ ≤ E*(50*(L+1)*(2+(E+1)*L))+(E+1)*(16*L+16)+3+9*L+8 := by
      unfold PowerPrograms.runtimeBound PowerPrograms.workBound PowerPrograms.callbackBound
      rw [hv]
      gcongr
    _ ≤ 200*H^2 := by rw [hsecond]; nlinarith

theorem arithmetic_cost_le (a b : List Bool) (H : ℕ)
    (ha : a.length ≤ H) (hb : b.length ≤ H) (hH : 1 ≤ H) :
    100*(a.length+b.length+1)^2 ≤ 900*H^2 := by
  calc
    _ ≤ 100*(3*H)^2 := by gcongr; omega
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOffsetProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram


/-- Native arithmetic produces actual words, with both value and physical
length guarantees. Internal powers are never supplied as advice. -/
theorem core_eval (regs : Regs) (B Q R : List Bool) :
    ∃ ticks rf a e p b out,
      Eval core ticks (bank regs (initial B Q R)) (bank rf (filled B Q R a e p b out)) ∧
      BinaryArithmetic.toNat out=2*BinaryArithmetic.toNat B*(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) ∧
      out.length ≤ outputLength B Q R ∧
      (∀ i : Fin 15, i ∈ [3,4,5,6,7,8] →
        (filled B Q R a e p b out i).length ≤ width B Q R) ∧
      ticks ≤ coreBudget B Q R := by
  let w0 := initial B Q R
  obtain ⟨r1,h1⟩ := load_eval regs w0 3 two rfl
  let w1 := Function.update w0 3 two
  obtain ⟨r2,h2⟩ := load_eval r1 w1 4 eight (by simp [w1,w0,initial,inputWords])
  let w2 := Function.update w1 4 eight
  obtain ⟨t3,r3,a,h3,hva,hla,hta⟩ :=
    multiply_eval r2 w2 4 1 5 (by decide) (by decide) (by simp [w2,w1,w0,initial,inputWords])
  let w3 := Function.update w2 5 a
  obtain ⟨t4,r4,e,h4,hve,hle,hte⟩ :=
    multiply_eval r3 w3 3 2 6 (by decide) (by decide) (by simp [w3,w2,w1,w0,initial,inputWords])
  let w4 := Function.update w3 6 e
  obtain ⟨t5,r5,p,h5,hvp,hlp,htp⟩ :=
    power_eval r4 w4 5 6 7 (by decide) (by decide) (by simp [w4,w3,w2,w1,w0,initial,inputWords])
  let w5 := Function.update w4 7 p
  obtain ⟨t6,r6,b,h6,hvb,hlb,htb⟩ :=
    multiply_eval r5 w5 3 0 8 (by decide) (by decide) (by simp [w5,w4,w3,w2,w1,w0,initial,inputWords])
  let w6 := Function.update w5 8 b
  obtain ⟨t7,r7,out,h7,hvo,hlo,hto⟩ :=
    multiply_eval r6 w6 8 7 9 (by decide) (by decide) (by simp [w6,w5,w4,w3,w2,w1,w0,initial,inputWords])
  have hva' : BinaryArithmetic.toNat a=8*BinaryArithmetic.toNat Q := by simpa [w2,w1,w0,initial,inputWords] using hva
  have hve' : BinaryArithmetic.toNat e=2*BinaryArithmetic.toNat R := by simpa [w3,w2,w1,w0,initial,inputWords] using hve
  have hvp' : BinaryArithmetic.toNat p=(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) := by simpa [w4,w3,hva',hve'] using hvp
  have hvb' : BinaryArithmetic.toNat b=2*BinaryArithmetic.toNat B := by simpa [w5,w4,w3,w2,w1,w0,initial,inputWords] using hvb
  have hvo' : BinaryArithmetic.toNat out=2*BinaryArithmetic.toNat B*(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) := by
    simpa [w6,w5,hvb',hvp'] using hvo
  have hla' : a.length ≤ Q.length+5 := by
    have h : a.length ≤ 4+Q.length+1 := by simpa [w2,w1,w0,initial,inputWords] using hla
    omega
  have hle' : e.length ≤ R.length+3 := by
    have h : e.length ≤ 2+R.length+1 := by simpa [w3,w2,w1,w0,initial,inputWords] using hle
    omega
  have hlp' : p.length ≤ 1+2*BinaryArithmetic.toNat R*a.length := by simpa [w4,w3,hve'] using hlp
  have hlb' : b.length ≤ B.length+3 := by
    have h : b.length ≤ 2+B.length+1 := by simpa [w5,w4,w3,w2,w1,w0,initial,inputWords] using hlb
    omega
  have hlo' : out.length ≤ b.length+p.length+1 := by simpa [w6,w5] using hlo
  have hlpQ : p.length ≤ 1+2*BinaryArithmetic.toNat R*(Q.length+5) :=
    hlp'.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hla') 1)
  have hlout : out.length ≤ outputLength B Q R := by unfold outputLength; omega
  let L := sourceWidth B Q R
  let E := 2*BinaryArithmetic.toNat R
  let H := width B Q R
  have hH : 1 ≤ H := width_pos B Q R
  have hLH : L+1 ≤ H := sourceWidth_le_width B Q R
  have hL : 10 ≤ L := by dsimp [L,sourceWidth]; omega
  have haL : a.length ≤ L := by dsimp [L,sourceWidth]; omega
  have heL : e.length ≤ L := by dsimp [L,sourceWidth]; omega
  have hbL : b.length ≤ L := by dsimp [L,sourceWidth]; omega
  have hQL : Q.length ≤ L := by dsimp [L,sourceWidth]; omega
  have hRL : R.length ≤ L := by dsimp [L,sourceWidth]; omega
  have hBL : B.length ≤ L := by dsimp [L,sourceWidth]; omega
  have hpH : p.length ≤ H := by
    calc
      _ ≤ 1+E*L := hlp'.trans (Nat.add_le_add_left (Nat.mul_le_mul_left E haL) 1)
      _ ≤ H := by
        change 1+E*L ≤ (E+1)*(L+1)
        simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
        omega
  have haH : a.length ≤ H := by omega
  have heH : e.length ≤ H := by omega
  have hbH : b.length ≤ H := by omega
  have ta : t3 ≤ 900*H^2 := hta.trans (arithmetic_cost_le _ _ H
    (by simp [w2,w1]; omega) (by simp [w2,w1,w0,initial,inputWords]; omega) hH)
  have te : t4 ≤ 900*H^2 := hte.trans (arithmetic_cost_le _ _ H
    (by simp [w3,w2,w1]; omega) (by simp [w3,w2,w1,w0,initial,inputWords]; omega) hH)
  have tb : t6 ≤ 900*H^2 := htb.trans (arithmetic_cost_le _ _ H
    (by simp [w5,w4,w3,w2,w1]; omega) (by simp [w5,w4,w3,w2,w1,w0,initial,inputWords]; omega) hH)
  have tout : t7 ≤ 900*H^2 := hto.trans (arithmetic_cost_le _ _ H
    (by simpa [w6] using hbH) (by simpa [w6,w5] using hpH) hH)
  have tp : t5 ≤ 200*H^2 := by
    have ht : t5 ≤ PowerPrograms.runtimeBound a e+9*e.length+8 := by simpa [w4,w3] using htp
    exact ht.trans (power_cost_le a e L E haL heL hve')
  have hall := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))
  refine ⟨_,r7,a,e,p,b,out,hall,hvo',hlout,?_,?_⟩
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [filled,loaded] <;> omega
  · have hs : 1 ≤ H^2 := by nlinarith only [hH]
    change 2*two.length+(2*eight.length+(t3+(t4+(t5+(t6+t7))))) ≤ 4000*H^2
    simp only [two_length,eight_length]
    omega

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOffsetProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram

theorem clearOne_eval (regs : Regs) (w : Words) (i : Fin 15) :
    Eval (clearOne i) (2*(w i).length+3) (bank regs w)
      (bank (readRegs regs 0 1 none) (Function.update w i [])) := by
  have h := ArithmeticExpressionSupport.clear_eval (port i) (bank regs w)
  simpa only [clearOne, bank, state_port, state_update,
    SubexpBlockParameterProgram.state_regs] using h

theorem clearMany_eval (is : List (Fin 15)) (regs : Regs) (w : Words) (H : ℕ)
    (hw : ∀ i ∈ is,(w i).length ≤ H) :
    ∃ ticks rf, Eval (clearMany is) ticks (bank regs w) (bank rf (erased is w)) ∧
      ticks ≤ is.length*(2*H+3) := by
  induction is generalizing regs w with
  | nil => exact ⟨0,regs,.base (.skip _),by simp⟩
  | cons i is ih =>
      have hi := hw i (by simp)
      have ht : ∀ j ∈ is,((Function.update w i []) j).length ≤ H := by
        intro j hj
        by_cases he : j=i
        · subst j
          simpa only [Function.update_self,List.length_nil] using (Nat.zero_le H)
        · simpa [Function.update_apply,he] using hw j (by simp [hj])
      obtain ⟨t,rf,he,hle⟩ := ih (readRegs regs 0 1 none) (Function.update w i []) ht
      refine ⟨2*(w i).length+3+t,rf,(clearOne_eval regs w i).seq he,?_⟩
      simp only [List.length_cons,Nat.add_mul]
      omega

theorem erased_filled (B Q R a e p b out : List Bool) :
    erased scratch (filled B Q R a e p b out)=Function.update (initial B Q R) 9 out := by
  funext i
  fin_cases i <;> simp [erased,filled,loaded,initial,inputWords]

/-- A fixed command computes the offset and restores its local workspace. The
extra tick in the bound also pays for the standalone program's halt. -/
theorem command_eval (regs : Regs) (B Q R : List Bool) :
    ∃ ticks out, Eval command ticks (input regs B Q R) (result B Q R out) ∧
      BinaryArithmetic.toNat out=2*BinaryArithmetic.toNat B*(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) ∧
      out.length ≤ outputLength B Q R ∧ ticks+1 ≤ budget B Q R := by
  obtain ⟨tc,rc,a,e,p,b,out,hc,hval,hlen,hw,htc⟩ := core_eval regs B Q R
  obtain ⟨tz,rz,hz,htz⟩ := clearMany_eval scratch rc (filled B Q R a e p b out) (width B Q R) hw
  rw [erased_filled] at hz
  have hr := RegisterResetProgram.all_eval (bank rz (Function.update (initial B Q R) 9 out))
  have he := hc.seq (hz.seq hr)
  have hresult : RegisterResetProgram.zeroed (bank rz (Function.update (initial B Q R) 9 out))=
      result B Q R out := rfl
  rw [hresult] at he
  refine ⟨tc+(tz+8),out,he,hval,hlen,?_⟩
  have hH := width_pos B Q R
  have hs : width B Q R ≤ (width B Q R)^2 := by nlinarith only [hH]
  simp only [scratch,List.length_cons,List.length_nil] at htz
  unfold budget coreBudget at *
  nlinarith only [htc,htz,hH,hs]

/-- A single fixed binary-stack machine computes the offset, retains all three
source words, clears temporary data, and resets its eight Boolean registers. -/
theorem program_runsIn (regs : Regs) (B Q R : List Bool) :
    ∃ out, BinaryArithmetic.toNat out=2*BinaryArithmetic.toNat B*(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) ∧
      out.length ≤ outputLength B Q R ∧
      RunsIn program (budget B Q R)
        ((input regs B Q R).withPC (some program.entry)) ((result B Q R out).withPC none) := by
  obtain ⟨ticks,out,he,hval,hlen,ht⟩ := command_eval regs B Q R
  exact ⟨out,hval,hlen,ticks+1,ht,compiled_halt_trace he 0 9⟩

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

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

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

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

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native syntax from physical formula/row masters through the guarded
parameter bank. The only static input is the fixed formula-width bound k. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem offsetPorts_injective : Function.Injective offsetPorts := by decide

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendNumerics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem offsetCall_eval (a : Data) (B Q R : List Bool)
    (hp : projectState r8 offsetPorts a = LayoutOffsetProgram.input (a.regs ∘ r8) B Q R) :
    ∃ n ≤ LayoutOffsetProgram.budget B Q R, ∃ word,
      Eval offsetCall n a (embedState r8 offsetPorts a (LayoutOffsetProgram.result B Q R word)) ∧
      BinaryArithmetic.toNat word=2*BinaryArithmetic.toNat B*(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) ∧
      word.length ≤ LayoutOffsetProgram.outputLength B Q R := by
  obtain ⟨word,hv,hl,he⟩ := LayoutOffsetProgram.program_runsIn (a.regs ∘ r8) B Q R
  rw [←hp] at he
  obtain ⟨n,hn,he⟩ := call_run _ r8 offsetPorts (registers_injective ..) offsetPorts_injective a _ _ he
  exact ⟨n,hn,word,he,hv,hl⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem offset_eval_oai (a : Data) (he : emptyRange a 650 668) (ho : a.stacks 141=[]) :
    ∃ n ≤ LayoutOffsetProgram.budget (a.stacks 725) (a.stacks 720) (a.stacks 727), ∃ b,
      Eval offsetCall n a b ∧
      BinaryArithmetic.toNat (b.stacks 141)=2*BinaryArithmetic.toNat (a.stacks 725)*
        (8*BinaryArithmetic.toNat (a.stacks 720))^(2*BinaryArithmetic.toNat (a.stacks 727)) ∧
      (b.stacks 141).length ≤ LayoutOffsetProgram.outputLength (a.stacks 725) (a.stacks 720) (a.stacks 727) ∧
      (∀ i : Fin 768, i≠141 → b.stacks i=a.stacks i) ∧ b.regs 8=a.regs 8 := by
  have hz650 := he 650 (by decide) (by decide)
  have hz651 := he 651 (by decide) (by decide)
  have hz652 := he 652 (by decide) (by decide)
  have hz653 := he 653 (by decide) (by decide)
  have hz654 := he 654 (by decide) (by decide)
  have hz655 := he 655 (by decide) (by decide)
  have hz656 := he 656 (by decide) (by decide)
  have hz657 := he 657 (by decide) (by decide)
  have hz658 := he 658 (by decide) (by decide)
  have hz659 := he 659 (by decide) (by decide)
  have hz660 := he 660 (by decide) (by decide)
  have hz661 := he 661 (by decide) (by decide)
  have hz662 := he 662 (by decide) (by decide)
  have hz663 := he 663 (by decide) (by decide)
  have hz664 := he 664 (by decide) (by decide)
  have hz665 := he 665 (by decide) (by decide)
  have hz666 := he 666 (by decide) (by decide)
  have hz667 := he 667 (by decide) (by decide)
  have hp : projectState r8 offsetPorts a=LayoutOffsetProgram.input (a.regs ∘ r8)
      (a.stacks 725) (a.stacks 720) (a.stacks 727) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [offsetPorts,
          LayoutOffsetProgram.initial,SubexpBlockParameterProgram.inputWords,ho,hz650,hz651,hz652,hz653,hz654,hz655,hz656,hz657,hz658,hz659,hz660,hz661,hz662,hz663,hz664,hz665,hz666,hz667]
  obtain ⟨n,hn,word,hex,hval,hlen⟩ := offsetCall_eval a (a.stacks 725) (a.stacks 720) (a.stacks 727) hp
  let small := LayoutOffsetProgram.result (a.stacks 725) (a.stacks 720) (a.stacks 727) word
  let b := embedState r8 offsetPorts a small
  have h141 : b.stacks 141=word := embedState_stack r8 offsetPorts a small offsetPorts_injective 9
  refine ⟨n,hn,b,hex,by simpa [h141] using hval,by simpa [h141] using hlen,?_,?_⟩
  · intro i hi
    by_cases him : ∃ j, offsetPorts j=i
    · obtain ⟨j,rfl⟩ := him
      have hj := embedState_stack r8 offsetPorts a small offsetPorts_injective j
      rw [hj]
      fin_cases j <;> simp_all [small,offsetPorts,LayoutOffsetProgram.result,LayoutOffsetProgram.bank,
        LayoutOffsetProgram.initial,SubexpBlockParameterProgram.inputWords,SubexpBlockParameterProgram.state]
    · exact embedState_stack_frame r8 offsetPorts a small i him
  · exact embedState_register_frame r8 offsetPorts a small 8 (by decide)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offset_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offset_eval_oai
