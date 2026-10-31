-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_tail_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:11:59.810979+00:00
-- url     : https://prove2.me/submissions/ad5b81c3-060e-4155-9b02-514663874f26

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Factor_accumulate_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafAssignmentSetupProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete storage and framed service calls for each head assignment. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem clear_eval (a : Data) (src : Fin 768) :
    Eval (clear src) (2*(a.stacks src).length+3) a (cleared a src) := by
  apply Eval.call
  have he := halt_after_trace _
    (clearProgram_trace src (0 : Fin 40) 1 a.regs a.stacks) 2 rfl rfl
  simpa [cleared,clearResult,clearStacks,StructuredProgram.State.withPC,clearProgram,
    Nat.add_assoc] using he

end SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid cleanup and multiplication after a real factor service. The running
product remains on151 and all source/cache tapes are framed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native

theorem clear_eval (a : Data) (i : Fin 768) :
    Eval (clear i) (2*(a.stacks i).length+3) a (cleared a i) :=
  LeafAssignmentSetupProgram.clear_eval a i

theorem lowReady_clear (a : Data) (e : MomentsProgram.Product.Store)
    (h : lowReady a e) (j : Fin 768) (hj : 56 ≤ j.val) :
    lowReady (cleared a j) e := by
  intro i
  have hn : nativeStacks (Memory.lowPort i) ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change i.val=j.val at hv
    omega
  simpa only [cleared,LeafAssignmentSetupProgram.cleared,Function.update_of_ne hn] using h i

/-- The actual suffix shared by the marked and ordinary hash branches. -/
theorem marked_tail_eval_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (u J : ℕ) (seed factor : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (a : Data)
    (hlo : lowReady a (MomentsProgram.Product.idle M.bits width cache.zero.val
      (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)))
    (hseed : a.stacks 151=MomentsProgram.Product.bytes seed)
    (hfactor : a.stacks 67=MomentsProgram.Product.bytes factor)
    (h61 : a.stacks 61=[]) (h70 : a.stacks 70=[]) (h159 : a.stacks 159=[]) :
    let result := MomentsProgram.Product.run p t M cache table u J seed factor []
    ∃ k b, k ≤ 2*(a.stacks 62).length+3+productBudget p t M cache table u J seed factor ∧
      Eval (.seq (clear 62) accumulate) k a b ∧
      b.stacks=Function.update (Function.update (Function.update a.stacks 62 []) 67 [])
        151 (MomentsProgram.Product.bytes result) := by
  dsimp only
  let c := cleared a 62
  obtain ⟨k,b,hk,he,hb⟩ := accumulate_eval p t M cache hz table degree width hd hw u J seed factor c
    (lowReady_clear a _ hlo 62 (by decide))
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using hseed)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using hfactor)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using h61)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using h70)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using h159)
  exact ⟨_,b,Nat.add_le_add_left hk _,(clear_eval a 62).seq he,hb⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_tail_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_tail_eval_oai
