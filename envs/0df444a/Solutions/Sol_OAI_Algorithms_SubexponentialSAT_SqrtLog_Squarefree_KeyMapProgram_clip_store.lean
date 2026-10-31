-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.clip_store
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:12:29.665679+00:00
-- url     : https://prove2.me/submissions/4960ff83-ab3c-407a-992e-15f578343dce

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S135

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ParserProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control parsers for the canonical formula encoding

These programs operate on two Boolean stacks and two Boolean registers.
Stack 0 is input; stack 1 accumulates output. Register 0 holds the last data
bit and register 1 records whether the last pop succeeded. Thus register 1
is true on successful delimiter termination and false on malformed input.
All stated running times count actual `BitProgram.step` transitions.
-/

namespace SubexponentialSAT.ParserProgram

open SubexponentialSAT.BitProgram

theorem nat_pop (b v p : Bool) (input output : List Bool) :
    step natProgram (cfg (some 0) v p (b :: input) output) =
      some (cfg (some 1) b true input output) := by
  simp [step, cfg, execInstr, readRegs]

theorem nat_present (v : Bool) (input output : List Bool) :
    step natProgram (cfg (some 1) v true input output) =
      some (cfg (some 2) v true input output) := by
  simp [step, cfg, execInstr]

theorem nat_true (input output : List Bool) :
    step natProgram (cfg (some 2) true true input output) =
      some (cfg (some 3) true true input output) := by
  simp [step, cfg, execInstr]

theorem nat_push (input output : List Bool) :
    step natProgram (cfg (some 3) true true input output) =
      some (cfg (some 0) true true input (true :: output)) := by
  simp [step, cfg, execInstr]

theorem nat_false (input output : List Bool) :
    step natProgram (cfg (some 2) false true input output) =
      some (cfg (some 4) false true input output) := by
  simp [step, cfg, execInstr]

theorem nat_halt (v p : Bool) (input output : List Bool) :
    step natProgram (cfg (some 4) v p input output) =
      some (cfg none v p input output) := by
  simp [step, cfg, execInstr]

theorem nat_cycle (v p : Bool) (input output : List Bool) :
    Trace natProgram 4 (cfg (some 0) v p (true :: input) output)
      (cfg (some 0) true true input (true :: output)) :=
  .cons (nat_pop true v p input output)
    (.cons (nat_present true input output)
      (.cons (nat_true input output) (.cons (nat_push input output) (.refl _))))

theorem nat_finish (v p : Bool) (input output : List Bool) :
    Trace natProgram 4 (cfg (some 0) v p (false :: input) output)
      (cfg none false true input output) :=
  .cons (nat_pop false v p input output)
    (.cons (nat_present false input output)
      (.cons (nat_false input output) (.cons (nat_halt false true input output) (.refl _))))

/-- The count is data on stack 1, rather than an input-dependent control state. -/
theorem nat_trace (n : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace natProgram (4 * n + 4)
      (cfg (some 0) v p (Encoding.encodeNat n ++ rest) output)
      (cfg none false true rest (List.replicate n true ++ output)) := by
  induction n generalizing output v p with
  | zero => simpa [Encoding.encodeNat] using nat_finish v p rest output
  | succ n ih =>
      have h := (nat_cycle v p (Encoding.encodeNat n ++ rest) output).trans
        (ih (true :: output) true true)
      have ht : 4 + (4 * n + 4) = 4 * (n + 1) + 4 := by omega
      have hin : Encoding.encodeNat (n + 1) ++ rest =
          true :: (Encoding.encodeNat n ++ rest) := by
        simp [Encoding.encodeNat, List.replicate_succ]
      simpa only [ht, hin, List.replicate_succ', List.append_assoc,
        List.singleton_append] using h

/-! ## In-place removal of one escape frame -/

/-! The compiler turns the preceding actual instruction traces into actual
primitive tape executions. Each overhead below belongs to one fixed program. -/

end SubexponentialSAT.ParserProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An eight-label comparison of unary counts. Only stack presence is read;
the count values never occur in the finite instruction table. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram

theorem unaryLess_nil (regs : Fin 4 → Bool) (right : List Bool) :
    Trace unaryLessProgram 5 (unaryLessCfg (some 0) regs [] right)
      (unaryLessCfg none
        (Function.update (readRegs (readRegs regs 0 1 none) 0 2 right.head?)
          3 right.head?.isSome) [] right) := by
  cases right <;>
    apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, unaryLessProgram, unaryLessCfg,
      execInstr, readRegs, Function.update_apply]

theorem unaryLess_right_nil (regs : Fin 4 → Bool) (a : Bool) (left : List Bool) :
    Trace unaryLessProgram 6 (unaryLessCfg (some 0) regs (a :: left) [])
      (unaryLessCfg none
        (Function.update (readRegs (readRegs regs 0 1 (some a)) 0 2 none) 3 false)
        left []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, unaryLessProgram, unaryLessCfg,
    execInstr, readRegs, Function.update_apply]
  all_goals (funext i; fin_cases i <;> simp)

theorem unaryLess_round (regs : Fin 4 → Bool) (a b : Bool) (left right : List Bool) :
    Trace unaryLessProgram 4 (unaryLessCfg (some 0) regs (a :: left) (b :: right))
      (unaryLessCfg (some 0) (readRegs (readRegs regs 0 1 (some a)) 0 2 (some b))
        left right) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, unaryLessProgram, unaryLessCfg,
    execInstr, readRegs, Function.update_apply]
  all_goals (funext i; fin_cases i <;> simp)

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramNat
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed primitive unary-field reader used by encoded sparse-key joins.
The unary magnitude affects execution time, never the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem natRegs_injective : Function.Injective natRegs := Fin.castAdd_injective _ _
theorem natPorts_injective {s : ℕ} (src dst : Fin s) (h : src ≠ dst) :
    Function.Injective (natPorts src dst) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [natPorts, ParserProgram.pair]

theorem readNat_eval {s : ℕ} (d : State 5 s) (src dst : Fin s) (hsd : src ≠ dst)
    (n : ℕ) (rest : List Bool) (hin : d.stacks src = Encoding.encodeNat n ++ rest) :
    Eval (readNat src dst) (4 * n + 4) d (afterNat d src dst n rest) := by
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (Encoding.encodeNat n ++ rest) (d.stacks dst)⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (List.replicate n true ++ d.stacks dst)⟩
  have ha : embedState natRegs (natPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ natRegs_injective (natPorts_injective src dst hsd)
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
    · intros; rfl
  have hb : embedState natRegs (natPorts src dst) d b = afterNat d src dst n rest := by
    apply embedState_eq_of_ports _ _ _ _ _ natRegs_injective (natPorts_injective src dst hsd)
    · intro i; fin_cases i <;> simp [afterNat, natRegs, readRegs, b, ParserProgram.pair]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [natRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [natRegs] using h.symm⟩
      simp [afterNat, readRegs, h0, h1]
    · intro i; fin_cases i <;> simp [afterNat, natPorts, ParserProgram.pair, b, hsd]
    · intro j hj
      have hsrc : j ≠ src := fun h => hj ⟨0, by simpa [natPorts] using h.symm⟩
      have hdst : j ≠ dst := fun h => hj ⟨1, by simpa [natPorts] using h.symm⟩
      simp [afterNat, hsrc, hdst]
  have ht : Trace ParserProgram.natProgram (4 * n + 4)
      (a.withPC (some ParserProgram.natProgram.entry)) (b.withPC none) :=
    ParserProgram.nat_trace n rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have h := eval_call_lifted ParserProgram.natProgram natRegs
    (natPorts src dst) d natRegs_injective (natPorts_injective src dst hsd) ht
  simpa only [ha,hb,readNat] using h

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLess
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed unary comparison with explicit residual-length bounds and paid
cleanup. Register 4 is a caller-owned Boolean saved across this operation. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem unaryLess_trace_bounded (left right : List Bool) (regs : Fin 4 → Bool) :
    ∃ n rf l r, n ≤ 4 * left.length + 6 ∧
      Trace unaryLessProgram n (unaryLessCfg (some 0) regs left right)
        (unaryLessCfg none rf l r) ∧
      rf 3 = decide (left.length < right.length) ∧
      l.length ≤ left.length ∧ r.length ≤ right.length := by
  induction left generalizing right regs with
  | nil =>
      refine ⟨5, _, [], right, by simp, unaryLess_nil regs right, ?_, by simp, le_rfl⟩
      cases right <;> simp
  | cons a left ih =>
      cases right with
      | nil =>
          exact ⟨6, _, left, [], by simp, unaryLess_right_nil regs a left, by simp, by simp, by simp⟩
      | cons b right =>
          obtain ⟨n, rf, l, r, hn, ht, hf, hl, hr⟩ :=
            ih right (readRegs (readRegs regs 0 1 (some a)) 0 2 (some b))
          refine ⟨4 + n, rf, l, r, ?_, (unaryLess_round regs a b left right).trans ht, ?_, by simp; omega, by simp; omega⟩
          · simp only [List.length_cons]
            omega
          · simpa using hf

theorem lessRegs_injective : Function.Injective lessRegs := Fin.castAdd_injective _ _

theorem clearAt_eval {s : ℕ} (d : State 5 s) (src : Fin s) :
    Eval (clearAt src) (2*(d.stacks src).length+3) d (clearedAt d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 5) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [clearedAt,StackRoutines.clearResult,StackRoutines.clearStacks,
    StructuredProgram.State.withPC,StackRoutines.clearProgram,Nat.add_assoc] using hh

theorem lessAt_eval {s : ℕ} (d : State 5 s) (src dst : Fin s) (hsd : src ≠ dst) :
    ∃ time ≤ 4*(d.stacks src).length+6, ∃ rf l r,
      Eval (lessAt src dst) time d
        (⟨rf,Function.update (Function.update d.stacks src l) dst r⟩ : State 5 s) ∧
      rf 3 = decide ((d.stacks src).length < (d.stacks dst).length) ∧
      rf 4 = d.regs 4 ∧ l.length ≤ (d.stacks src).length ∧ r.length ≤ (d.stacks dst).length := by
  obtain ⟨time,rr,l,r,ht,h,hr,hl,hrlen⟩ :=
    unaryLess_trace_bounded (d.stacks src) (d.stacks dst) (d.regs ∘ lessRegs)
  let a : State 4 2 := ⟨d.regs ∘ lessRegs, ![d.stacks src,d.stacks dst]⟩
  let b : State 4 2 := ⟨rr,![l,r]⟩
  let rf := (embedState lessRegs (natPorts src dst) d b).regs
  have ha : embedState lessRegs (natPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ lessRegs_injective (natPorts_injective src dst hsd)
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState lessRegs (natPorts src dst) d b =
      (⟨rf,Function.update (Function.update d.stacks src l) dst r⟩ : State 5 s) := by
    apply embedState_eq_of_ports _ _ _ _ _ lessRegs_injective (natPorts_injective src dst hsd)
    · intro i; exact embedState_register lessRegs (natPorts src dst) d b lessRegs_injective i
    · intro i hi; exact embedState_register_frame lessRegs (natPorts src dst) d b i hi
    · intro i; fin_cases i <;> simp [natPorts,ParserProgram.pair,b,hsd]
    · intro i hi
      have hsrc : i ≠ src := fun he => hi ⟨0, by simpa [natPorts] using he.symm⟩
      have hdst : i ≠ dst := fun he => hi ⟨1, by simpa [natPorts] using he.symm⟩
      simp [hsrc,hdst]
  have htrace : Trace unaryLessProgram time (a.withPC (some unaryLessProgram.entry)) (b.withPC none) := h
  have he := eval_call_lifted unaryLessProgram lessRegs (natPorts src dst) d
    lessRegs_injective (natPorts_injective src dst hsd) htrace
  change Eval (lessAt src dst) time
    (embedState lessRegs (natPorts src dst) d a) (embedState lessRegs (natPorts src dst) d b) at he
  rw [ha,hb] at he
  refine ⟨time,ht,rf,l,r,he,?_,?_,hl,hrlen⟩
  · have hp := embedState_register lessRegs (natPorts src dst) d b lessRegs_injective 3
    simpa [rf,lessRegs,b,hr] using hp
  · apply embedState_register_frame
    rintro ⟨i,hi⟩
    fin_cases i <;> simp [lessRegs] at hi

theorem lessClear_eval {s : ℕ} (d : State 5 s) (src dst : Fin s) (hsd : src ≠ dst) :
    ∃ time ≤ 6*(d.stacks src).length+2*(d.stacks dst).length+12, ∃ rf,
      Eval (lessClear src dst) time d
        (⟨rf,Function.update (Function.update d.stacks src []) dst []⟩ : State 5 s) ∧
      rf 3 = decide ((d.stacks src).length < (d.stacks dst).length) ∧
      rf 4 = d.regs 4 := by
  obtain ⟨time,ht,rr,l,r,h,hf,h4,hl,hr⟩ := lessAt_eval d src dst hsd
  let b : State 5 s := ⟨rr,Function.update (Function.update d.stacks src l) dst r⟩
  have h1 := clearAt_eval b src
  have h2 := clearAt_eval (clearedAt b src) dst
  let rf := (clearedAt (clearedAt b src) dst).regs
  have hs : clearedAt (clearedAt b src) dst =
      (⟨rf,Function.update (Function.update d.stacks src []) dst []⟩ : State 5 s) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hsi : i = src
      · subst i; simp [clearedAt,b,hsd]
      · by_cases hdi : i = dst
        · subst i; simp [clearedAt,b]
        · simp [clearedAt,b,hsi,hdi]
  have he := h.seq (h1.seq h2)
  change Eval (lessClear src dst)
    (time+((2*(b.stacks src).length+3)+(2*((clearedAt b src).stacks dst).length+3))) d
    (clearedAt (clearedAt b src) dst) at he
  rw [hs] at he
  refine ⟨_,?_,rf,he,?_,?_⟩
  · simp only [b,clearedAt,Function.update_apply,hsd,Ne.symm hsd,ite_false,ite_true, if_true]
    omega
  · simpa [rf,clearedAt,b,readRegs] using hf
  · simpa [rf,clearedAt,b,readRegs] using h4

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramClip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed primitive clipping for sparse keys. The key and both unary limits
are disposable inputs; all four local stacks are empty on return. Callers may
keep master copies outside these ports. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem clipField_eval (d : State 5 4) (budget : Fin 4)
    (h0 : budget ≠ 0) (h3 : budget ≠ 3) (u : ℕ) (rest : List Bool)
    (hin : d.stacks 0 = Encoding.encodeNat u ++ rest) (hb : d.stacks 3 = []) :
    ∃ time ≤ 10*u+2*(d.stacks budget).length+16, ∃ rf,
      Eval (clipField budget) time d
        (⟨rf,Function.update (Function.update (Function.update d.stacks 0 rest) 3 []) budget []⟩ : State 5 4) ∧
      rf 3 = decide (u < (d.stacks budget).length) ∧ rf 4 = d.regs 4 := by
  have hp := readNat_eval d 0 3 (by decide) u rest hin
  let a := afterNat d 0 3 u rest
  have ha3 : a.stacks 3 = List.replicate u true := by simp [a,afterNat,hb]
  have hab : a.stacks budget = d.stacks budget := by simp [a,afterNat,h0,h3]
  obtain ⟨time,ht,rf,h,hf,h4⟩ := lessClear_eval a 3 budget (Ne.symm h3)
  have hs : (⟨rf,Function.update (Function.update a.stacks 3 []) budget []⟩ : State 5 4) =
      (⟨rf,Function.update (Function.update (Function.update d.stacks 0 rest) 3 []) budget []⟩ : State 5 4) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    by_cases hi : i = budget <;> by_cases hj : i = 3 <;>
      simp_all [a,afterNat]
  rw [hs] at h
  refine ⟨(4*u+4)+time,?_,rf,hp.seq h,?_,?_⟩
  · rw [ha3,hab,List.length_replicate] at ht
    omega
  · simpa [ha3,hab] using hf
  · simpa [a,afterNat,readRegs] using h4

theorem clipIndex_eval (regs : Fin 5 → Bool) (u z : ℕ) (mask t J : List Bool) :
    ∃ time ≤ 10*(u+z)+2*(t.length+J.length)+2*mask.length+37, ∃ rf,
      Eval clipIndex time
        (clipState regs (Encoding.encodeNat u ++ Encoding.encodeNat z ++ mask) t J [])
        (clipState rf [] [] [] []) ∧
      rf 4 = decide (u < t.length ∧ z < J.length) := by
  let source := Encoding.encodeNat z ++ mask
  obtain ⟨n1,hn1,r1,h1,hf1,h41⟩ := clipField_eval
    (clipState regs (Encoding.encodeNat u ++ source) t J []) 1 (by decide) (by decide)
    u source rfl rfl
  have h1' : Eval (clipField 1) n1
      (clipState regs (Encoding.encodeNat u ++ source) t J [])
      (clipState r1 source [] J []) := by
    convert h1 using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i; fin_cases i <;> simp []
  let r2 := Function.update r1 (4 : Fin 5) (r1 3)
  have hcopy : Eval (.base (.atom (.copy 4 3))) 1
      (clipState r1 source [] J []) (clipState r2 source [] J []) := by
    apply Eval.base
    convert StructuredProgram.Eval.atom (StructuredProgram.Atom.copy (4 : Fin 5) 3)
      (clipState r1 source [] J []) using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · rfl
  obtain ⟨n2,hn2,r3,h2,hf2,h42⟩ := clipField_eval
    (clipState r2 source [] J []) 2 (by decide) (by decide) z mask rfl rfl
  have h2' : Eval (clipField 2) n2
      (clipState r2 source [] J []) (clipState r3 mask [] [] []) := by
    convert h2 using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i; fin_cases i <;> simp []
  let r4 := Function.update r3 (4 : Fin 5) (r3 4 && r3 3)
  have hband : Eval (.base (.atom (.band 4 4 3))) 1
      (clipState r3 mask [] [] []) (clipState r4 mask [] [] []) := by
    apply Eval.base
    convert StructuredProgram.Eval.atom (StructuredProgram.Atom.band (4 : Fin 5) 4 3)
      (clipState r3 mask [] [] []) using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · rfl
  let rf := readRegs r4 (0 : Fin 5) 1 none
  have hc := clearAt_eval (clipState r4 mask [] [] []) 0
  have hc' : Eval (clearAt 0) (2*mask.length+3)
      (clipState r4 mask [] [] []) (clipState rf [] [] [] []) := by
    convert hc using 1
    · simp []
    · apply congrArg₂ StructuredProgram.State.mk rfl
      funext i; fin_cases i <;> simp []
  refine ⟨n1+(1+(n2+(1+(2*mask.length+3)))),?_,rf,?_,?_⟩
  · simp [] at hn1 hn2
    omega
  · simpa [clipIndex,source,List.append_assoc] using h1'.seq (hcopy.seq (h2'.seq (hband.seq hc')))
  · simp [] at hf1 hf2 h42
    by_cases hu : u < t.length <;> by_cases hz : z < J.length <;>
      first | (simp [rf,r4,r2,readRegs,h42,hf1,hf2,hu,hz, -OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status_read]) | (simp [rf,r4,r2,readRegs,h42,hf1,hf2,hu,hz])

/-- Actual machine clipping is exactly the semantic `Index.Kept` predicate. -/
theorem clipIndex_trace {n : ℕ} (a : Index (Fin n)) (t J : ℕ) (regs : Fin 5 → Bool) :
    ∃ time ≤ 10*(a.u+a.z)+2*(t+J)+2*n+38, ∃ rf,
      Trace clipIndexProgram time
        ((clipState regs (encodeIndex a) (List.replicate t true) (List.replicate J true) []).withPC
          (some clipIndexProgram.entry))
        ((clipState rf [] [] [] []).withPC none) ∧
      rf 4 = decide (a.Kept t J) := by
  obtain ⟨time,ht,rf,h,hf⟩ := clipIndex_eval regs a.u a.z (encodeMask a.vars)
    (List.replicate t true) (List.replicate J true)
  refine ⟨time+1,?_,rf,?_,?_⟩
  · simpa only [List.length_replicate,encodeMask_length] using (Nat.add_le_add_right ht 1)
  · simpa [clipIndexProgram,encodeIndex] using compiled_halt_trace h 0 0
  · simp only [List.length_replicate] at hf
    by_cases h : a.u < t ∧ a.z < J
    · simpa only [Index.Kept, h, decide_true] using hf
    · simpa only [Index.Kept, h, decide_false] using hf

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem regs5_inj : Function.Injective regs5 := Fin.castAdd_injective _ _
theorem clipPorts_inj : Function.Injective clipPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [clipPorts]

theorem clip_store_oai {n : ℕ} (regs : Fin 8 → Bool) (s : Store) (a : Index (Fin n)) (t J : ℕ)
    (hk : s.clipKey = encodeIndex a) (ht : s.tCopy = List.replicate t true)
    (hj : s.jCopy = List.replicate J true) (hz : s.clipTmp = []) :
    ∃ time ≤ 10*(a.u+a.z)+2*(t+J)+2*n+38, ∃ rr,
      Eval clip time (state regs s)
        (state rr {s with clipKey := [], tCopy := [], jCopy := [], clipTmp := []}) ∧
      rr 4 = decide (a.Kept t J) := by
  obtain ⟨time,hbound,rf,he,hflag⟩ := Program.clipIndex_trace a t J (regs ∘ regs5)
  let finish := Program.clipState rf [] [] [] []
  let rr := (embedState regs5 clipPorts (state regs s) finish).regs
  have hs : embedState regs5 clipPorts (state regs s)
      (Program.clipState (regs ∘ regs5) (encodeIndex a) (List.replicate t true)
        (List.replicate J true) []) = state regs s := by
    apply embedState_eq_of_ports _ _ _ _ _ regs5_inj clipPorts_inj
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [clipPorts,state,tapes,hk,ht,hj,hz]
    · intros; rfl
  have hf : embedState regs5 clipPorts (state regs s) finish =
      state rr {s with clipKey := [], tCopy := [], jCopy := [], clipTmp := []} := by
    apply embedState_eq_of_ports _ _ _ _ _ regs5_inj clipPorts_inj
    · intro i; exact embedState_register regs5 clipPorts (state regs s) finish regs5_inj i
    · intro i hi; exact embedState_register_frame regs5 clipPorts (state regs s) finish i hi
    · intro i; fin_cases i <;> simp [finish,clipPorts,state,tapes]
    · intro i hi
      fin_cases i <;> simp_all [clipPorts,state,tapes,Fin.exists_fin_succ]
  have he' := eval_call_lifted Program.clipIndexProgram regs5 clipPorts
    (state regs s) regs5_inj clipPorts_inj he
  dsimp only [finish] at hf
  refine ⟨time,hbound,rr,by simpa only [clip,hs,hf] using he',?_⟩
  have hreg := embedState_register regs5 clipPorts (state regs s) finish regs5_inj 4
  simpa [rr,regs5,finish,Program.clipState,hflag] using hreg

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.clip_store_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.clip_store_oai
