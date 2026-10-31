-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.accumulateLow_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:00:23.710305+00:00
-- url     : https://prove2.me/submissions/8fd4c5ef-6f52-4ffa-8cd1-2440b065221f

import Mathlib
import Definitions.Def_OAIQ081S130

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-register local operations for the actual residual statistics scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
theorem copy_eval (src dst tmp : Fin 21) (a : Data)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (ht : a.stacks tmp = []) :
    Eval (copy src dst tmp) (7*(a.stacks src).length+5) a (copied src dst a) :=
  .call _ (ListRegisterProgram.copy_run src dst tmp 0 1 hsd hst htd (by decide) a.regs a.stacks ht)

theorem transfer_eval (src dst : Fin 21) (a : Data) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(a.stacks src).length+3) a (transferred src dst a) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hsd (by decide) a.regs a.stacks)

theorem pushTrue_eval (dst : Fin 21) (a : Data) : Eval (pushTrue dst) 2 a (pushedTrue dst a) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) true) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push dst (0 : Fin 10)) _))
  simpa [pushTrue,pushedTrue,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using h

theorem pop_eval (src : Fin 21) (a : Data) : Eval (pop src) 1 a (popped src a) := .base (.atom _ _)

theorem peek_eval (src : Fin 21) (a : Data) : Eval (peek src) 1 a (peeked src a) := .base (.atom _ _)

theorem maxRegs_injective : Function.Injective maxRegs := Fin.castAdd_injective _ _
theorem maxStacks_injective : Function.Injective maxStacks := by decide

theorem maximum_eval (a : Data) (x y : ℕ)
    (hx : a.stacks 18 = unary x) (hy : a.stacks 15 = unary y) (ht : a.stacks 19 = []) :
    ∃ rf, Eval maximum (8*x+6) a
      ⟨rf,Function.update (Function.update a.stacks 18 []) 15 (unary (max x y))⟩ := by
  obtain ⟨rf,he⟩ := Max.command_eval (a.regs ∘ maxRegs) x y
  let b := Max.state rf [] (unary (max x y)) []
  have hp : projectState maxRegs maxStacks a = Max.state (a.regs ∘ maxRegs) (unary x) (unary y) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [maxStacks,hx,hy,ht]
  have tr := compiled_halt_trace he 0 1
  rw [← hp] at tr
  have hc := eval_call_from_state Max.program maxRegs maxStacks a maxRegs_injective maxStacks_injective tr
  let e := embedState maxRegs maxStacks a b
  have heq : e = ⟨e.regs,Function.update (Function.update a.stacks 18 []) 15 (unary (max x y))⟩ := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    by_cases h18 : i = 18
    · subst i; exact embedState_stack maxRegs maxStacks a b maxStacks_injective 0
    by_cases h15 : i = 15
    · subst i; exact embedState_stack maxRegs maxStacks a b maxStacks_injective 1
    by_cases h19 : i = 19
    · subst i
      calc
        Function.extend maxStacks b.stacks a.stacks 19 = b.stacks 2 := by
          simpa [maxStacks] using
            (maxStacks_injective.extend_apply b.stacks a.stacks 2)
        _ = Function.update (Function.update a.stacks 18 []) 15
            (unary (max x y)) 19 := by simp [b, ht]
    · have hf := embedState_stack_frame maxRegs maxStacks a b i (by
        rintro ⟨j,hj⟩; fin_cases j <;> simp [maxStacks] at hj <;> simp_all)
      change (embedState maxRegs maxStacks a b).stacks i =
        Function.update (Function.update a.stacks 18 []) 15 (unary (max x y)) i
      rw [Function.update_noteq h15, Function.update_noteq h18]
      exact hf
  refine ⟨e.regs,?_⟩
  change Eval maximum (8*x+5+1) a e at hc
  rw [heq] at hc
  convert hc using 1
  all_goals try with_reducible_and_instances rfl

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramVariables
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact runtime accumulation of residual variable statistics. Each degree is
computed by scanning the serialized original scopes. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem neutralize_eval (a : Data) (d u : ℕ)
    (hd : a.stacks 3 = unary d) (hu : a.stacks 17 = unary u) :
    ∃ n rf, n ≤ 6 ∧ Eval neutralize n a
      ⟨rf,Function.update (Function.update a.stacks 3 (unary (max 1 d))) 17
        (unary (u+(if d=0 then 1 else 0)))⟩ := by
  cases d with
  | zero =>
    let b := peeked 3 a
    let c := pushedTrue 3 b
    let e := pushedTrue 17 c
    have hbranch : Eval (.ite 1 (.base .skip) (.seq (pushTrue 3) (pushTrue 17))) 5 b e :=
      Eval.ite_false (by simp [b,peeked,hd,unary,readRegs])
        ((pushTrue_eval 3 b).seq (pushTrue_eval 17 c))
    refine ⟨6,e.regs,by omega,?_⟩
    have heq : e = ⟨e.regs,Function.update (Function.update a.stacks 3 (unary (max 1 0))) 17
        (unary (u+(if 0=0 then 1 else 0)))⟩ := by
      apply congrArg (StructuredProgram.State.mk e.regs)
      funext i
      by_cases h17 : i=17
      · subst i; simp [c,b,pushedTrue,peeked,hu,unary,List.replicate_succ]
      by_cases h3 : i=3
      · subst i; simp [c,b,pushedTrue,peeked,hd,unary]
      · simp [c,b,pushedTrue,peeked,h17,h3]
    have h := (peek_eval 3 a).seq hbranch
    rw [heq] at h
    exact h
  | succ d =>
    let b := peeked 3 a
    have hbranch : Eval (.ite 1 (.base .skip) (.seq (pushTrue 3) (pushTrue 17))) 1 b b :=
      Eval.ite_true (by simp [b,peeked,hd,unary,readRegs,List.replicate_succ])
        (Eval.base (StructuredProgram.Eval.skip b))
    refine ⟨2,b.regs,by omega,?_⟩
    have heq : b = ⟨b.regs,Function.update (Function.update a.stacks 3 (unary (max 1 (d+1)))) 17
        (unary (u+(if d+1=0 then 1 else 0)))⟩ := by
      apply congrArg (StructuredProgram.State.mk b.regs)
      have hm : max 1 (d+1)=d+1 := by omega
      simp [←hd,←hu]
    have h := (peek_eval 3 a).seq hbranch
    rw [heq] at h
    exact h

theorem accumulateLow_eval_oai (r : Fin 10 → Bool) (scopes : List (List ℕ))
    (v d : ℕ) (mask master : List Bool) (t : Totals) :
    ∃ n rf, n ≤ 30*(d+1)+30 ∧
      Eval accumulateLow n
        ⟨r,Function.update (variableState r scopes v mask master t).stacks 3 (unary (d+1))⟩
        (variableState rf scopes v mask master (t.add d)) := by
  let a : Data := ⟨r,Function.update (variableState r scopes v mask master t).stacks 3 (unary (d+1))⟩
  let b := pushedTrue 14 a
  let c := popped 3 b
  have hc3 : c.stacks 3 = unary d := by simp [c,b,a,popped,pushedTrue,unary,List.replicate_succ]
  have hc17 : c.stacks 17 = unary t.uncovered := by simp [c,b,a,popped,pushedTrue,variableState]
  obtain ⟨nn,rn,hnn,hen⟩ := neutralize_eval c d t.uncovered hc3 hc17
  let e : Data := ⟨rn,Function.update (Function.update c.stacks 3 (unary (max 1 d))) 17
    (unary (t.uncovered+(if d=0 then 1 else 0)))⟩
  let f := copied 3 18 e
  let g := transferred 3 16 f
  have he19 : e.stacks 19 = [] := by simp [e,c,b,a,popped,pushedTrue,variableState]
  have hcopy := copy_eval 3 18 19 e (by decide) (by decide) (by decide) he19
  have htransfer := transfer_eval 3 16 f (by decide)
  have hg18 : g.stacks 18 = unary (max 1 d) := by
    simp [g,f,e,c,b,a,transferred,copied,popped,pushedTrue,variableState,
      StackRoutines.transferStacks,StackRoutines.copyStacks]
  have hg15 : g.stacks 15 = unary t.occurrence := by
    simp [g,f,e,c,b,a,transferred,copied,popped,pushedTrue,StackRoutines.transferStacks,
      StackRoutines.copyStacks,variableState]
  have hg19 : g.stacks 19 = [] := by
    simp [g,f,e,c,b,a,transferred,copied,popped,pushedTrue,StackRoutines.transferStacks,
      StackRoutines.copyStacks,variableState]
  obtain ⟨rf,hmax⟩ := maximum_eval g (max 1 d) t.occurrence hg18 hg15 hg19
  have hfinal : (⟨rf,Function.update (Function.update g.stacks 18 []) 15
      (unary (max (max 1 d) t.occurrence))⟩ : Data) =
      variableState rf scopes v mask master (t.add d) := by
    apply congrArg (StructuredProgram.State.mk rf)
    funext i; fin_cases i <;>
      simp [g,f,e,c,b,a,transferred,copied,popped,pushedTrue,StackRoutines.transferStacks,
        StackRoutines.copyStacks,variableState,Totals.add,unary,List.replicate_succ,
        List.reverse_replicate,Nat.add_comm]
  rw [hfinal] at hmax
  have h := (pushTrue_eval 14 a).seq ((pop_eval 3 b).seq
    (hen.seq (hcopy.seq (htransfer.seq hmax))))
  refine ⟨_,rf,?_,h⟩
  have he3 : (e.stacks 3).length = max 1 d := by simp [e]
  have hf3 : (f.stacks 3).length = max 1 d := by
    simp [f,e,copied,StackRoutines.copyStacks]
  rw [he3,hf3]
  omega

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.accumulateLow_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.accumulateLow_eval_oai
