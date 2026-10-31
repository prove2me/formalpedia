-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_time_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:57:56.903357+00:00
-- url     : https://prove2.me/submissions/6d046037-26fb-4989-87fd-b0bf7e2aaad0

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_frontend_eval_input_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPrimeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable pieces of prime trial division

The numeric trial-division functions in the first section are specifications.
They are never instructions of a program. The executable zero test and Boolean
accumulator below contain only existing finite Boolean-stack instructions.
Candidate numbers, divisors, and remainders are runtime data.
-/

namespace SubexponentialSAT.SubexpPrimeProgram

open BitProgram StructuredProgram StructuredCalls

private theorem terminal_trace_steps_unique {α : Type*} {step : α → Option α}
    {n m : ℕ} {a b c : α} (h₁ : Computation.Trace step n a b)
    (h₂ : Computation.Trace step m a c) (hb : step b = none) (hc : step c = none) :
    n = m := by
  induction h₁ generalizing m c with
  | refl a =>
      cases h₂ with
      | refl => rfl
      | cons hs ht => simp [hb] at hs
  | @cons n a a' b hs ht ih =>
      cases h₂ with
      | refl => simp [hc] at hs
      | @cons m _ a'' c hs' ht' =>
          have haa : a' = a'' := Option.some.inj (hs.symm.trans hs')
          subst a''
          exact congrArg Nat.succ (ih ht' hb hc)

/-- The exact instruction count of a terminating structured execution is
unique as well as its result. This allows proved execution bounds to be used
for every actual occurrence of a subroutine in a larger trace. -/
theorem eval_steps_unique {R S : ℕ} {cmd : StructuredCalls.Cmd R S}
    {n m : ℕ} {a b c : StructuredProgram.State R S}
    (h₁ : StructuredCalls.Eval cmd n a b)
    (h₂ : StructuredCalls.Eval cmd m a c) (input output : Fin S) : n = m := by
  have h := terminal_trace_steps_unique
    (StructuredCalls.compiled_halt_trace h₁ input output)
    (StructuredCalls.compiled_halt_trace h₂ input output) rfl rfl
  omega

end SubexponentialSAT.SubexpPrimeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendUniform
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The input bound applies to every occurrence of the frontend in a larger
execution, by uniqueness of its deterministic instruction count. -/
theorem frontend_time_le_oai (q : Query) (k : ℕ) {a b : Data} {n : ℕ}
    (hv : q.Valid) (ha : q.Ready a) (ho : q.OutputEmpty a)
    (he : Eval (frontend k) n a b) : n ≤ q.inputBudget k := by
  obtain ⟨m,c,hm,hb⟩ := frontend_eval_input_bound q k a hv ha ho
  exact (SubexpPrimeProgram.eval_steps_unique he hm 700 382) ▸ hb

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_time_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_time_le_oai
