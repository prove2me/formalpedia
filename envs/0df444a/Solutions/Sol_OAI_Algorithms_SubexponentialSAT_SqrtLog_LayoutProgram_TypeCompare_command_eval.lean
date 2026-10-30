-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:29:56.108695+00:00
-- url     : https://prove2.me/submissions/1211f2cb-c684-414a-85cd-050e0f947d7b

import Mathlib
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S091
import Definitions.Def_OAIQ081S097
import Definitions.Def_OAIQ081S099

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputAccess
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port array access used to prepare the matrix-entry comparison. -/

namespace SubexponentialSAT.Subexp.MatrixInputAccess

open BitProgram StructuredCalls StackRoutines

theorem eqRegs_injective : Function.Injective eqRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)

theorem eqPorts_injective : Function.Injective eqPorts := by
  decide

theorem equality_eval (a : Data) (h11 : a.stacks 11 = []) :
    ∃ n ≤ 11 * (a.stacks 0).length + 2 * (a.stacks 28).length + 22,
      Eval equality n a (compared a (decide (a.stacks 0 = a.stacks 28))) := by
  let x : State 5 13 := ⟨a.regs ∘ eqRegs, a.stacks ∘ eqPorts⟩
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.seal_eval x
  let y := CollisionStreamProgram.sealed x (decide (a.stacks 0 = a.stacks 28))
  let mid : Data :=
    ⟨fun j => if j.val < 5 then false else a.regs j,
      Function.update (Function.update (Function.update a.stacks 0 []) 28 [])
        11 [decide (a.stacks 0 = a.stacks 28)]⟩
  have hx : embedState eqRegs eqPorts a x = a := by
    apply embedState_eq_of_ports _ _ _ _ _ eqRegs_injective eqPorts_injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hy : embedState eqRegs eqPorts a y = mid := by
    apply embedState_eq_of_ports _ _ _ _ _ eqRegs_injective eqPorts_injective
    · intro i
      change (if i.val < 5 then false else a.regs (eqRegs i)) = false
      simp [i.isLt]
    · intro j hj
      have hge : ¬ j.val < 5 := fun h => hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [mid, hge]
    · intro i
      by_cases hi1 : i = 1
      · subst i; simp [mid, y, x, CollisionStreamProgram.sealed, h11]
      by_cases hi12 : i = 12
      · subst i; simp [mid, y, x, CollisionStreamProgram.sealed, h11]
      by_cases hi11 : i = 11
      · subst i; simp [mid, y, x, CollisionStreamProgram.sealed, h11]
      have h0 : eqPorts i ≠ 0 := fun h => hi1 (eqPorts_injective (h.trans eqPorts_one.symm))
      have h28 : eqPorts i ≠ 28 := fun h => hi12 (eqPorts_injective (h.trans eqPorts_twelve.symm))
      have h11' : eqPorts i ≠ 11 := fun h => hi11 (eqPorts_injective (h.trans eqPorts_eleven.symm))
      simp [mid, y, x, CollisionStreamProgram.sealed, hi1, hi12, hi11, h0, h28, h11']
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨1, h.symm⟩
      have h28 : j ≠ 28 := fun h => hj ⟨12, h.symm⟩
      have h11' : j ≠ 11 := fun h => hj ⟨11, h.symm⟩
      simp [mid, h0, h28, h11']
  have ht' : Trace equalityInner (n + 1) (x.withPC (some equalityInner.entry))
      (y.withPC none) := by
    simpa [equalityInner, y, x, Function.comp_def, eqPorts] using
      compiled_halt_trace ht (1 : Fin 13) 11
  have hl := eval_call_lifted equalityInner eqRegs eqPorts a
    eqRegs_injective eqPorts_injective ht'
  have hl' : Eval (.call (ProgramLinking.liftProgram equalityInner eqRegs eqPorts))
      (n + 1) a mid := by
    simpa only [hx, hy] using hl
  have hf : (StructuredProgram.Atom.set (0 : Fin 8) false).eval
      ((StructuredProgram.Atom.pop (11 : Fin 29) 7 0).eval mid) =
      compared a (decide (a.stacks 0 = a.stacks 28)) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      by_cases hj0 : j = 0
      · subst j
        simp [mid, readRegs, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
      by_cases hj7 : j = 7
      · subst j
        simp [mid, readRegs, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
      simp [mid, readRegs, hj0, hj7, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
    · funext j; by_cases hj : j = 11 <;>
        simp [mid, hj, h11, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
  have he := hl'.seq
    ((Eval.base (StructuredProgram.Eval.atom (.pop (11 : Fin 29) (7 : Fin 8) 0) mid)).seq
      (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false)
        ((StructuredProgram.Atom.pop (11 : Fin 29) 7 0).eval mid))))
  rw [hf] at he
  refine ⟨n + 1 + (1 + 1), ?_, he⟩
  change n ≤ 11 * (a.stacks 0).length + 2 * (a.stacks 28).length + 19 at hn
  omega

end SubexponentialSAT.Subexp.MatrixInputAccess

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ConstraintEntryCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Compare the two preserved universal-type byte arrays without changing
the scalar result or any input stack of the matrix-entry service. -/

namespace SubexponentialSAT.Subexp.ConstraintEntryCompare

open BitProgram StructuredCalls StackRoutines

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _
theorem ports_injective : Function.Injective ports := by decide

theorem equality_eval (a : Data) (h45 : a.stacks 45 = []) :
    ∃ n ≤ 11 * (a.stacks 43).length + 2 * (a.stacks 44).length + 23,
      ∃ out : Fin 10 → Bool,
        Eval equality n a
          ⟨out, Function.update (Function.update a.stacks 43 []) 44 []⟩ ∧
        out 7 = decide (a.stacks 43 = a.stacks 44) := by
  let small := projectState registers ports a
  obtain ⟨n, hn, ht⟩ := MatrixInputAccess.equality_eval small
    (by simpa [small, projectState, ports] using h45)
  let b := embedState registers ports a
    (MatrixInputAccess.compared small (decide (small.stacks 0 = small.stacks 28)))
  have he := eval_liftCommand_from_state MatrixInputAccess.equality 0 0
    registers ports a registers_injective ports_injective ht
  have hbase : Function.extend ports (a.stacks ∘ ports) a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks
      (embedState_project registers ports a registers_injective ports_injective)
  have hs : b.stacks = Function.update (Function.update a.stacks 43 []) 44 [] := by
    change Function.extend ports
      (Function.update (Function.update (a.stacks ∘ ports) 0 []) 28 []) a.stacks = _
    rw [ProgramLinking.extend_update ports_injective,
      ProgramLinking.extend_update ports_injective, hbase]
    rfl
  have hb : b =
      (⟨b.regs, Function.update (Function.update a.stacks 43 []) 44 []⟩ : Data) :=
    congrArg (StructuredProgram.State.mk b.regs) hs
  have hr : b.regs 7 = decide (a.stacks 43 = a.stacks 44) := by
    change b.regs (registers 7) = _
    rw [embedState_register _ _ _ _ registers_injective]
    simp [small, projectState, ports ]
  refine ⟨n + 1, ?_, b.regs, ?_, hr⟩
  · change n ≤ 11 * (a.stacks 43).length + 2 * (a.stacks 44).length + 22 at hn
    omega
  · change Eval equality (n + 1) a b at he
    rw [hb] at he
    exact he

/-- The comparison is computed from actual copied bytes; every source stack
is restored, including the matrix-entry result on stack 0. -/
theorem command_eval (a : Data)
    (h42 : a.stacks 42 = []) (h43 : a.stacks 43 = [])
    (h44 : a.stacks 44 = []) (h45 : a.stacks 45 = []) :
    ∃ n ≤ 18 * (a.stacks 23).length + 9 * (a.stacks 24).length + 33,
      ∃ out : Fin 10 → Bool,
        Eval command n a ⟨out, a.stacks⟩ ∧
        out 7 = decide (a.stacks 23 = a.stacks 24) := by
  let a1 := copied a 23 43
  let a2 := copied a1 24 44
  have t0 := TupleProgram.copy_eval (23 : Fin 46) 43 42 (0 : Fin 10) 1
    (by decide) (by decide) (by decide) (by decide) a h42
  have t1 := TupleProgram.copy_eval (24 : Fin 46) 44 42 (0 : Fin 10) 1
    (by decide) (by decide) (by decide) (by decide) a1
    (by simp [a1, copied, copyStacks, h42])
  obtain ⟨ne, hne, out, te, hout⟩ := equality_eval a2
    (by simp [a2, a1, copied, copyStacks, h45])
  have hf : Function.update (Function.update a2.stacks 43 []) 44 [] = a.stacks := by
    funext j
    by_cases h43j : j = 43
    · subst j; simp [h43]
    by_cases h44j : j = 44
    · subst j; simp [h44]
    simp [a2, a1, copied, copyStacks, h43j, h44j]
  rw [hf] at te
  have he := t0.seq (t1.seq te)
  refine ⟨_, ?_, out, he, ?_⟩
  · simp only [a2, a1, copied, copyStacks, Function.update_self,
      Function.update_of_ne (by decide : (24 : Fin 46) ≠ 43),
      Function.update_of_ne (by decide : (43 : Fin 46) ≠ 44),
      Function.update_of_ne (by decide : (44 : Fin 46) ≠ 43),
      h43, h44, List.append_nil] at hne ⊢
    omega
  · simpa [a2, a1, copied, copyStacks, h43, h44] using hout

end SubexponentialSAT.Subexp.ConstraintEntryCompare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramTypeCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving comparison of the two type words using scratch0..3. All cache
ports42..48 remain intact. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem ports_inj : Function.Injective ports := by decide

theorem command_eval_oai (a : Data) (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[])
    (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[]) :
    ∃ n ≤ 18*(a.stacks 23).length+9*(a.stacks 24).length+34,
      ∃ e : Data, Eval command n a e ∧ e.stacks=a.stacks ∧
        e.regs 7=decide (a.stacks 23=a.stacks 24) := by
  let p := projectState id ports a
  obtain ⟨n,hn,rr,he,hr⟩ := ConstraintEntryCompare.command_eval p h0 h1 h2 h3
  let e := embedState id ports a ⟨rr,p.stacks⟩
  have hh := eval_liftCommand_from_state ConstraintEntryCompare.command 23 23 id ports a
    Function.injective_id ports_inj he
  have hs : e.stacks=a.stacks := by
    change Function.extend ports p.stacks a.stacks=a.stacks
    exact congrArg StructuredProgram.State.stacks (embedState_project id ports a Function.injective_id ports_inj)
  have h7 : e.regs 7=rr 7 :=
    embedState_register id ports a ⟨rr,p.stacks⟩ Function.injective_id 7
  refine ⟨n+1,?_,e,hh,hs,?_⟩
  · simpa [p,projectState,ports] using Nat.add_le_add_right hn 1
  · simpa [p,projectState,ports] using h7.trans hr

end SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command_eval_oai
