-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.join_store
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:13:51.846167+00:00
-- url     : https://prove2.me/submissions/9b5af823-5a61-4826-bc8b-78b40426e847

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeMask_union {n : ℕ} (s t : Finset (Fin n)) :
    List.zipWith (· || ·) (encodeMask s) (encodeMask t) = encodeMask (s ∪ t) := by
  apply List.ext_getElem
  · simp [encodeMask]
  · intro i hi hj
    simp [encodeMask]

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed primitive bit-mask union. Both runtime input words have the same
length. The output is prepended in reverse order; no list operation is atomic
and the instruction table does not depend on the word length. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

theorem maskBody_eval (regs : Fin 5 → Bool) (a b : Bool)
    (left right output : List Bool) :
    ∃ regs', Eval maskBody 5 (maskData regs (a :: left) (b :: right) output)
      (maskReady regs' left right ((a || b) :: output)) := by
  let d := maskData regs (a :: left) (b :: right) output
  let d1 := (Atom.pop (0 : Fin 3) (0 : Fin 5) 2).eval d
  let d2 := (Atom.pop (1 : Fin 3) (1 : Fin 5) 3).eval d1
  let d3 := (Atom.bor (4 : Fin 5) 0 1).eval d2
  let d4 := (Atom.push (2 : Fin 3) (4 : Fin 5)).eval d3
  refine ⟨d3.regs, ?_⟩
  have he := Eval.seq (Eval.atom (Atom.pop (0 : Fin 3) (0 : Fin 5) 2) d)
    (Eval.seq (Eval.atom (Atom.pop (1 : Fin 3) (1 : Fin 5) 3) d1)
      (Eval.seq (Eval.atom (Atom.bor (4 : Fin 5) 0 1) d2)
        (Eval.seq (Eval.atom (Atom.push (2 : Fin 3) (4 : Fin 5)) d3)
          (Eval.atom (Atom.peek (0 : Fin 3) (0 : Fin 5) 2) d4))))
  convert he using 1 ;
    simp [ maskReady, maskData, d, d1, d2, d3, d4, Atom.eval,
      Atom.instr, State.ofCfg, execInstr, readRegs, Function.update] ;
    try (first | done | (funext i; fin_cases i <;> rfl))

theorem maskLoop_eval (left right output : List Bool) (regs : Fin 5 → Bool)
    (hlen : left.length = right.length) :
    ∃ regs', Eval maskLoop (6 * left.length + 1) (maskReady regs left right output)
      (maskData regs' [] [] ((List.zipWith (· || ·) left right).reverse ++ output)) := by
  induction left generalizing right output regs with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp hlen.symm
    subst right
    refine ⟨(maskReady regs [] [] output).regs, ?_⟩
    simpa [maskLoop, maskReady, maskData] using
      (Eval.while_false (body := maskBody) (maskReady_guard regs [] [] output))
  | cons a left ih =>
    cases right with
    | nil => simp at hlen
    | cons b right =>
      have ht : left.length = right.length := by simpa using hlen
      obtain ⟨middle, hb⟩ := maskBody_eval (maskReady regs (a :: left) (b :: right) output).regs
        a b left right output
      obtain ⟨final, hf⟩ := ih right ((a || b) :: output) middle ht
      refine ⟨final, ?_⟩
      have hh := Eval.while_true (by simp : (maskReady regs (a :: left) (b :: right) output).regs 2 = true) hb hf
      have hc : 5 + (6 * left.length + 1) + 1 = 6 * (a :: left).length + 1 := by
        simp only [List.length_cons]; omega
      rw [hc] at hh
      simpa [maskLoop, maskReady, maskData, List.zipWith_cons_cons, List.reverse_cons,
        List.append_assoc] using hh

theorem maskUnion_eval (left right output : List Bool) (regs : Fin 5 → Bool)
    (hlen : left.length = right.length) :
    ∃ regs', Eval maskUnion (6 * left.length + 2) (maskData regs left right output)
      (maskData regs' [] [] ((List.zipWith (· || ·) left right).reverse ++ output)) := by
  obtain ⟨final, hf⟩ := maskLoop_eval left right output regs hlen
  refine ⟨final, ?_⟩
  have hp : Eval (.atom (.peek 0 0 2)) 1 (maskData regs left right output)
      (maskReady regs left right output) := Eval.atom _ _
  have hc : 1 + (6 * left.length + 1) = 6 * left.length + 2 := by omega
  have he := hp.seq hf
  rw [hc] at he
  exact he

theorem maskUnion_trace (left right output : List Bool) (regs : Fin 5 → Bool)
    (hlen : left.length = right.length) :
    ∃ regs', Trace maskUnionProgram (6 * left.length + 3)
      ((maskData regs left right output).withPC (some maskUnionProgram.entry))
      ((maskData regs' [] [] ((List.zipWith (· || ·) left right).reverse ++ output)).withPC none) := by
  obtain ⟨final, hf⟩ := maskUnion_eval left right output regs hlen
  exact ⟨final, by simpa [maskUnionProgram, Nat.add_assoc] using compiled_halt_trace hf 0 2⟩

/-- Semantic bridge: the exact bit program computes finite-set support union. -/
theorem supportUnion_trace {n : ℕ} (left right : Finset (Fin n))
    (output : List Bool) (regs : Fin 5 → Bool) :
    ∃ final, Trace maskUnionProgram (6 * n + 3)
      ((maskData regs (encodeMask left) (encodeMask right) output).withPC
        (some maskUnionProgram.entry))
      ((maskData final [] [] ((encodeMask (left ∪ right)).reverse ++ output)).withPC none) := by
  simpa only [encodeMask_length, encodeMask_union] using
    maskUnion_trace (encodeMask left) (encodeMask right) output regs
      (by simp only [encodeMask_length])

end SubexponentialSAT.SqrtLog.Squarefree.Program

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

theorem joinNat_eval (regs : Fin 5 → Bool) (a b : ℕ) (left right output : List Bool) :
    ∃ final, Eval joinNat (4 * (a + b) + 9)
      (maskData regs (Encoding.encodeNat a ++ left) (Encoding.encodeNat b ++ right) output)
      (maskData final left right ((Encoding.encodeNat (a+b)).reverse ++ output)) := by
  let r1 := readRegs regs (0 : Fin 5) 1 (some false)
  let r2 := readRegs r1 (0 : Fin 5) 1 (some false)
  have h1 := readNat_eval
    (maskData regs (Encoding.encodeNat a ++ left) (Encoding.encodeNat b ++ right) output)
    0 2 (by decide) a left rfl
  have h1' : Eval (readNat 0 2) (4*a+4)
      (maskData regs (Encoding.encodeNat a ++ left) (Encoding.encodeNat b ++ right) output)
      (maskData r1 left (Encoding.encodeNat b ++ right) (List.replicate a true ++ output)) := by
    convert h1 using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [maskData]
  have h2 := readNat_eval
    (maskData r1 left (Encoding.encodeNat b ++ right) (List.replicate a true ++ output))
    1 2 (by decide) b right rfl
  have h2' : Eval (readNat 1 2) (4*b+4)
      (maskData r1 left (Encoding.encodeNat b ++ right) (List.replicate a true ++ output))
      (maskData r2 left right (List.replicate b true ++ (List.replicate a true ++ output))) := by
    convert h2 using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [maskData]
  let d := maskData r2 left right (List.replicate b true ++ (List.replicate a true ++ output))
  have h3 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (2 : Fin 3) (0 : Fin 5)) d)
  have hu : (Encoding.encodeNat (a+b)).reverse ++ output =
      false :: (List.replicate b true ++ (List.replicate a true ++ output)) := by
    simp only [Encoding.encodeNat,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.reverse_replicate,List.singleton_append]
    rw [Nat.add_comm a b, List.replicate_add]
    simp only [List.cons_append,List.append_assoc]
  have h3' : Eval (.base (.atom (.push 2 0))) 1 d
      (maskData r2 left right ((Encoding.encodeNat (a+b)).reverse ++ output)) := by
    rw [hu]
    convert h3 using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [d,maskData,StructuredProgram.Atom.instr,execInstr,r2,readRegs
          ]
  refine ⟨r2,?_⟩
  have ht : (4*a+4)+((4*b+4)+1) = 4*(a+b)+9 := by omega
  have he := h1'.seq (h2'.seq h3')
  rw [ht] at he
  exact he

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramJoin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single finite primitive program joins encoded sparse indices. Unary
exponents are added by scanning their fields; support bits are unioned by the
fixed OR scanner. The complete output is reversed for direct record emission. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem indexJoin_eval {n : ℕ} (a b : Index (Fin n))
    (regs : Fin 5 → Bool) (output : List Bool) :
    ∃ final, Eval indexJoin (4*(a.u+b.u+a.z+b.z)+6*n+21)
      (maskData regs (encodeIndex a) (encodeIndex b) output)
      (maskData final [] [] ((encodeIndex (a.join b)).reverse ++ output)) := by
  obtain ⟨r1,h1⟩ := joinNat_eval regs a.u b.u
    (Encoding.encodeNat a.z ++ encodeMask a.vars)
    (Encoding.encodeNat b.z ++ encodeMask b.vars) output
  obtain ⟨r2,h2⟩ := joinNat_eval r1 a.z b.z (encodeMask a.vars) (encodeMask b.vars)
    ((Encoding.encodeNat (a.u+b.u)).reverse ++ output)
  obtain ⟨r3,h3⟩ := supportUnion_trace a.vars b.vars
    ((Encoding.encodeNat (a.z+b.z)).reverse ++
      ((Encoding.encodeNat (a.u+b.u)).reverse ++ output)) r2
  have h3' := Eval.call maskUnionProgram h3
  have he := h1.seq (h2.seq h3')
  have ht : (4*(a.u+b.u)+9)+((4*(a.z+b.z)+9)+(6*n+3)) =
      4*(a.u+b.u+a.z+b.z)+6*n+21 := by omega
  rw [ht] at he
  refine ⟨r3,?_⟩
  simpa [indexJoin,encodeIndex,Index.join,List.reverse_append,List.append_assoc] using he

/-- Actual primitive execution, with an exact count linear in key size. -/
theorem indexJoin_trace {n : ℕ} (a b : Index (Fin n))
    (regs : Fin 5 → Bool) (output : List Bool) :
    ∃ final, Trace indexJoinProgram (4*(a.u+b.u+a.z+b.z)+6*n+22)
      ((maskData regs (encodeIndex a) (encodeIndex b) output).withPC
        (some indexJoinProgram.entry))
      ((maskData final [] [] ((encodeIndex (a.join b)).reverse ++ output)).withPC none) := by
  obtain ⟨final,h⟩ := indexJoin_eval a b regs output
  exact ⟨final,by simpa [indexJoinProgram,Nat.add_assoc] using compiled_halt_trace h 0 2⟩

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
theorem joinPorts_inj : Function.Injective joinPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [joinPorts]

theorem join_store_oai {n : ℕ} (regs : Fin 8 → Bool) (s : Store) (a b : Index (Fin n))
    (ha : s.leftCopy = encodeIndex a) (hb : s.rightKey = encodeIndex b)
    (ho : s.joinedRev = []) :
    ∃ rr, Eval join (4*(a.u+b.u+a.z+b.z)+6*n+22) (state regs s)
      (state rr {s with leftCopy := [], rightKey := [], joinedRev := (encodeIndex (a.join b)).reverse}) := by
  obtain ⟨rf,ht⟩ := Program.indexJoin_trace a b (regs ∘ regs5) []
  let finish := Program.maskData rf [] [] (encodeIndex (a.join b)).reverse
  let rr := (embedState regs5 joinPorts (state regs s) finish).regs
  have hs : embedState regs5 joinPorts (state regs s)
      (Program.maskData (regs ∘ regs5) (encodeIndex a) (encodeIndex b) []) = state regs s := by
    apply embedState_eq_of_ports _ _ _ _ _ regs5_inj joinPorts_inj
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [Program.maskData,joinPorts,state,tapes,ha,hb,ho]
    · intros; rfl
  have hf : embedState regs5 joinPorts (state regs s) finish =
      state rr {s with leftCopy := [], rightKey := [], joinedRev := (encodeIndex (a.join b)).reverse} := by
    apply embedState_eq_of_ports _ _ _ _ _ regs5_inj joinPorts_inj
    · intro i; exact embedState_register regs5 joinPorts (state regs s) finish regs5_inj i
    · intro i hi; exact embedState_register_frame regs5 joinPorts (state regs s) finish i hi
    · intro i; fin_cases i <;> simp [finish,Program.maskData,joinPorts,state,tapes]
    · intro i hi
      fin_cases i <;> simp_all [joinPorts,state,tapes,Fin.exists_fin_succ]
  have he := eval_call_lifted Program.indexJoinProgram regs5 joinPorts
    (state regs s) regs5_inj joinPorts_inj ht
  simp only [List.append_nil] at he
  dsimp only [finish] at hf
  exact ⟨rr, by simpa only [join,hs,hf] using he⟩

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.join_store_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.join_store_oai
