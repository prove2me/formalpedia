-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareBlocks_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:44:14.296824+00:00
-- url     : https://prove2.me/submissions/366cbf1e-dd3f-4bc3-8db0-027e2f14f53f

import Mathlib
import Definitions.Def_OAIQ081S137
import Definitions.Def_OAIQ081S168

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisEntryCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete framed-word, comparison, and scalar-cell services for the
global matrix entry callback. Register 6 is the persistent row-kind flag. -/

namespace SubexponentialSAT.Subexp.GlobalBasisEntryCore

open BitProgram StructuredCalls SubexpScanPrimitives

theorem pop_eval (src : Fin 32) (d : Data) (bit : Bool) (tail : List Bool)
    (hs : d.stacks src = bit :: tail) : Eval (pop src) 1 d (popped src bit tail d) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop src 7 0) d
  simpa [pop, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hs] using Eval.base h

theorem smallRegs_ne_six (i : Fin 5) : smallRegs i ≠ 6 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = 6 at hv
  omega

theorem sealCall_eval (d : Data) :
    ∃ n e, n ≤ 11 * (d.stacks 17).length + 2 * (d.stacks 28).length + 20 ∧
      Eval sealCall n d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 17 []) 28 [])
        27 (decide (d.stacks 17 = d.stacks 28) :: d.stacks 27) ∧
      e.regs 6 = d.regs 6 := by
  let a := projectState smallRegs sealPorts d
  obtain ⟨n, hn, he⟩ := CollisionStreamProgram.seal_eval a
  let b := CollisionStreamProgram.sealed a (decide (a.stacks 1 = a.stacks 12))
  let e := embedState smallRegs sealPorts d b
  have hn' : n ≤ 11 * (d.stacks 17).length + 2 * (d.stacks 28).length + 19 := by
    change n ≤ 11 * (d.stacks 17).length + 2 * (d.stacks 28).length + 19 at hn
    exact hn
  refine ⟨n + 1, e, by omega,
    eval_liftCommand_from_state CollisionStreamProgram.sealCommand 1 11 smallRegs sealPorts d
      smallRegs.injective sealPorts.injective he, ?_, ?_⟩
  · change Function.extend sealPorts b.stacks d.stacks = _
    dsimp [b, CollisionStreamProgram.sealed]
    rw [ProgramLinking.extend_update sealPorts.injective,
      ProgramLinking.extend_update sealPorts.injective,
      ProgramLinking.extend_update sealPorts.injective]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project smallRegs sealPorts d smallRegs.injective sealPorts.injective)
    change Function.extend sealPorts a.stacks d.stacks = d.stacks at hb
    rw [hb]
    rfl
  · exact embedState_register_frame smallRegs sealPorts d b 6 (by
      rintro ⟨i, hi⟩
      exact smallRegs_ne_six i hi)

theorem low_ne_high (i j : Fin 32) (hi : i.val < 16) (hj : 16 ≤ j.val) : i ≠ j := by
  intro h
  subst j
  omega

theorem compare_eval (left right : Fin 32) (hl : left.val < 16) (hr : right.val < 16)
    (d : Data) (h17 : d.stacks 17 = []) (h28 : d.stacks 28 = [])
    (h27 : d.stacks 27 = []) (h31 : d.stacks 31 = []) :
    ∃ n e, n ≤ 18 * (d.stacks left).length + 9 * (d.stacks right).length + 31 ∧
      Eval (compare left right) n d e ∧ e.stacks = d.stacks ∧
      e.regs 6 = d.regs 6 ∧ e.regs 7 = decide (d.stacks left = d.stacks right) := by
  have hl17 := low_ne_high left 17 hl (by decide)
  have hl31 := low_ne_high left 31 hl (by decide)
  have hr17 := low_ne_high right 17 hr (by decide)
  have hr28 := low_ne_high right 28 hr (by decide)
  have hr31 := low_ne_high right 31 hr (by decide)
  let a := afterCopy d left 17 0 1
  let b := afterCopy a right 28 0 1
  have ha := SubexpScanPrimitives.copy_eval d left 17 31 0 1
    hl17 hl31 (by decide) (by decide) h31
  have hb := SubexpScanPrimitives.copy_eval a right 28 31 0 1
    hr28 hr31 (by decide) (by decide) (by simp [a, afterCopy, StackRoutines.copyStacks, h31])
  have haRight : a.stacks right = d.stacks right := by
    simp [a, afterCopy, StackRoutines.copyStacks, hr17]
  have hb17 : b.stacks 17 = d.stacks left := by
    simp [b, a, afterCopy, StackRoutines.copyStacks, h17]
  have hb28 : b.stacks 28 = d.stacks right := by
    simp [b, a, afterCopy, StackRoutines.copyStacks, h28, hr17]
  have hb27 : b.stacks 27 = [] := by
    simp [b, a, afterCopy, StackRoutines.copyStacks, h27]
  obtain ⟨n, c, hn, hc, hcs, hc6⟩ := sealCall_eval b
  let answer := decide (d.stacks left = d.stacks right)
  have hc27 : c.stacks 27 = [answer] := by simp [hcs, hb17, hb28, hb27, answer]
  let e := popped 27 answer [] c
  have he := pop_eval 27 c answer [] hc27
  refine ⟨(7 * (d.stacks left).length + 5) +
      ((7 * (a.stacks right).length + 5) + (n + 1)), e, ?_,
    ha.seq (hb.seq (hc.seq he)), ?_, ?_, ?_⟩
  · rw [haRight, hb17, hb28] at *
    omega
  · funext j
    by_cases hj17 : j = 17 <;> by_cases hj28 : j = 28 <;> by_cases hj27 : j = 27 <;>
      simp [e, popped, hcs, b, a, afterCopy, StackRoutines.copyStacks,
        Function.update_apply, hj17, hj28, hj27, h17, h28, h27]
  · simp [e, popped, readRegs, hc6, b, a, afterCopy]
  · simp [e, popped, readRegs, answer]

end SubexponentialSAT.Subexp.GlobalBasisEntryCore

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrameCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and measured-call lemmas used by the concrete entry-bank program.
The state maps below only specify the outcomes of actual fixed commands. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem compare_lifted {S : ℕ} (ports : Fin 32 → Fin S)
    (hp : Function.Injective ports) (a : State 16 S)
    (h17 : a.stacks (ports 17)=[]) (h28 : a.stacks (ports 28)=[])
    (h27 : a.stacks (ports 27)=[]) (h31 : a.stacks (ports 31)=[]) :
    ∃ n ≤ 18*(a.stacks (ports 0)).length+9*(a.stacks (ports 1)).length+32,
      ∃ e : State 16 S,
      Eval (liftCommand (GlobalBasisEntryCore.compare 0 1) 0 1 id ports) n a e ∧
      e.stacks=a.stacks ∧ e.regs 6=a.regs 6 ∧
      e.regs 7=decide (a.stacks (ports 0)=a.stacks (ports 1)) := by
  let p := projectState id ports a
  obtain ⟨n,b,hn,he,hbs,h6,h7⟩ := GlobalBasisEntryCore.compare_eval 0 1
    (by decide) (by decide) p h17 h28 h27 h31
  let e := embedState id ports a b
  refine ⟨n+1,by simpa [p,projectState] using Nat.add_le_add_right hn 1,e,
    eval_liftCommand_from_state _ 0 1 id ports a Function.injective_id hp he,?_,?_,?_⟩
  · change Function.extend ports b.stacks a.stacks=a.stacks
    rw [hbs]
    exact congrArg StructuredProgram.State.stacks
      (embedState_project id ports a Function.injective_id hp)
  · exact (embedState_register id ports a b Function.injective_id 6).trans h6
  · exact (embedState_register id ports a b Function.injective_id 7).trans h7

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem blockPorts_inj : Function.Injective (comparePorts 288 291) := by decide

theorem compareBlocks_eval_oai (a : Data) (h301 : a.stacks 301=[]) (h302 : a.stacks 302=[])
    (h303 : a.stacks 303=[]) (h307 : a.stacks 307=[]) :
    ∃ n ≤ 18*(a.stacks 288).length+9*(a.stacks 291).length+32,
      ∃ e : Data, Eval compareBlocks n a e ∧ e.stacks=a.stacks ∧
        e.regs 6=a.regs 6 ∧ e.regs 7=decide (a.stacks 288=a.stacks 291) :=
  EntryBankFrame.compare_lifted _ blockPorts_inj a h301 h302 h303 h307

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareBlocks_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareBlocks_eval_oai
