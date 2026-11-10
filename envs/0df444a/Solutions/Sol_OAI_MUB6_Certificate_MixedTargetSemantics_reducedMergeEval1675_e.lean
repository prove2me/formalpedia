-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1675_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:19:13.3732+00:00
-- url     : https://prove2.me/submissions/3c4e70ae-5fae-42b0-af9d-fa77b958b1da

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E122
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E138
import Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval1555_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_CompareMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse collection needs only a computable comparison, not order axioms.
The comparison changes the representation but never its real evaluation. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*} [DecidableEq ι]

theorem eval_mergeByFuel (less : ι → ι → Bool) (fuel : ℕ)
    (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeByFuel less fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeByFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeByFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeByFuel]
      | cons b bs =>
        simp only [mergeByFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_mergeBy (less : ι → ι → Bool) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeBy less a b) x = eval a x + eval b x := eval_mergeByFuel _ _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4158 node4158Labels = Sparse.eval nodeValue4158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4158) = mixedMoment B node4158 node4158Labels := rfl
  simpa [nodeValue4158, Sparse.eval] using hc.symm

theorem sound4159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4159 node4159Labels = Sparse.eval nodeValue4159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4159) = mixedMoment B node4159 node4159Labels := rfl
  simpa [nodeValue4159, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4160 node4160Labels = Sparse.eval nodeValue4160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4160) = mixedMoment B node4160 node4160Labels := rfl
  simpa [nodeValue4160, Sparse.eval] using hc.symm

theorem sound4161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4161 node4161Labels = Sparse.eval nodeValue4161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4161) = mixedMoment B node4161 node4161Labels := rfl
  simpa [nodeValue4161, Sparse.eval] using hc.symm

theorem sound4162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4162 node4162Labels = Sparse.eval nodeValue4162 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4162) = mixedMoment B node4162 node4162Labels := rfl
  simpa [nodeValue4162, Sparse.eval] using hc.symm

theorem sound4163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4163 node4163Labels = Sparse.eval nodeValue4163 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4163) = mixedMoment B node4163 node4163Labels := rfl
  simpa [nodeValue4163, Sparse.eval] using hc.symm

theorem sound4169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4169 node4169Labels = Sparse.eval nodeValue4169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4169) = mixedMoment B node4169 node4169Labels := rfl
  simpa [nodeValue4169, Sparse.eval] using hc.symm

theorem sound4173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4173 node4173Labels = Sparse.eval nodeValue4173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4173) = mixedMoment B node4173 node4173Labels := rfl
  simpa [nodeValue4173, Sparse.eval] using hc.symm

theorem sound4176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4176 node4176Labels = Sparse.eval nodeValue4176 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4176) = mixedMoment B node4176 node4176Labels := rfl
  simpa [nodeValue4176, Sparse.eval] using hc.symm

theorem sound4178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4178 node4178Labels = Sparse.eval nodeValue4178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4178) = mixedMoment B node4178 node4178Labels := rfl
  simpa [nodeValue4178, Sparse.eval] using hc.symm

theorem sound4179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4179 node4179Labels = Sparse.eval nodeValue4179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4179) = mixedMoment B node4179 node4179Labels := rfl
  simpa [nodeValue4179, Sparse.eval] using hc.symm

theorem sound4184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4184 node4184Labels = Sparse.eval nodeValue4184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4184) = mixedMoment B node4184 node4184Labels := rfl
  simpa [nodeValue4184, Sparse.eval] using hc.symm

theorem sound4188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4188 node4188Labels = Sparse.eval nodeValue4188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4188) = mixedMoment B node4188 node4188Labels := rfl
  simpa [nodeValue4188, Sparse.eval] using hc.symm

theorem sound4189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4189 node4189Labels = Sparse.eval nodeValue4189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4189) = mixedMoment B node4189 node4189Labels := rfl
  simpa [nodeValue4189, Sparse.eval] using hc.symm

theorem sound4193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4193 node4193Labels = Sparse.eval nodeValue4193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4193) = mixedMoment B node4193 node4193Labels := rfl
  simpa [nodeValue4193, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4327 node4327Labels = Sparse.eval nodeValue4327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4327) = mixedMoment B node4327 node4327Labels := rfl
  simpa [nodeValue4327, Sparse.eval] using hc.symm

theorem sound4328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4328 node4328Labels = Sparse.eval nodeValue4328 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4328) = mixedMoment B node4328 node4328Labels := rfl
  simpa [nodeValue4328, Sparse.eval] using hc.symm

theorem sound4330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4330 node4330Labels = Sparse.eval nodeValue4330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4330) = mixedMoment B node4330 node4330Labels := rfl
  simpa [nodeValue4330, Sparse.eval] using hc.symm

theorem sound4331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4331 node4331Labels = Sparse.eval nodeValue4331 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4331) = mixedMoment B node4331 node4331Labels := rfl
  simpa [nodeValue4331, Sparse.eval] using hc.symm

theorem sound4332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4332 node4332Labels = Sparse.eval nodeValue4332 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4332) = mixedMoment B node4332 node4332Labels := rfl
  simpa [nodeValue4332, Sparse.eval] using hc.symm

theorem sound4333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4333 node4333Labels = Sparse.eval nodeValue4333 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4333) = mixedMoment B node4333 node4333Labels := rfl
  simpa [nodeValue4333, Sparse.eval] using hc.symm

theorem sound4334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4334 node4334Labels = Sparse.eval nodeValue4334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4334) = mixedMoment B node4334 node4334Labels := rfl
  simpa [nodeValue4334, Sparse.eval] using hc.symm

theorem sound4335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4335 node4335Labels = Sparse.eval nodeValue4335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4335) = mixedMoment B node4335 node4335Labels := rfl
  simpa [nodeValue4335, Sparse.eval] using hc.symm

theorem sound4336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4336 node4336Labels = Sparse.eval nodeValue4336 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4336) = mixedMoment B node4336 node4336Labels := rfl
  simpa [nodeValue4336, Sparse.eval] using hc.symm

theorem sound4345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4345 node4345Labels = Sparse.eval nodeValue4345 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4345) = mixedMoment B node4345 node4345Labels := rfl
  simpa [nodeValue4345, Sparse.eval] using hc.symm

theorem sound4347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4347 node4347Labels = Sparse.eval nodeValue4347 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4347) = mixedMoment B node4347 node4347Labels := rfl
  simpa [nodeValue4347, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4353 node4353Labels = Sparse.eval nodeValue4353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4353) = mixedMoment B node4353 node4353Labels := rfl
  simpa [nodeValue4353, Sparse.eval] using hc.symm

theorem sound4357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4357 node4357Labels = Sparse.eval nodeValue4357 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4357) = mixedMoment B node4357 node4357Labels := rfl
  simpa [nodeValue4357, Sparse.eval] using hc.symm

theorem sound4358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4358 node4358Labels = Sparse.eval nodeValue4358 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4358) = mixedMoment B node4358 node4358Labels := rfl
  simpa [nodeValue4358, Sparse.eval] using hc.symm

theorem sound4362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4362 node4362Labels = Sparse.eval nodeValue4362 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4362) = mixedMoment B node4362 node4362Labels := rfl
  simpa [nodeValue4362, Sparse.eval] using hc.symm

theorem sound4363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4363 node4363Labels = Sparse.eval nodeValue4363 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4363) = mixedMoment B node4363 node4363Labels := rfl
  simpa [nodeValue4363, Sparse.eval] using hc.symm

theorem sound4364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4364 node4364Labels = Sparse.eval nodeValue4364 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4364) = mixedMoment B node4364 node4364Labels := rfl
  simpa [nodeValue4364, Sparse.eval] using hc.symm

theorem sound4365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4365 node4365Labels = Sparse.eval nodeValue4365 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4365) = mixedMoment B node4365 node4365Labels := rfl
  simpa [nodeValue4365, Sparse.eval] using hc.symm

theorem sound4366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4366 node4366Labels = Sparse.eval nodeValue4366 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4366) = mixedMoment B node4366 node4366Labels := rfl
  simpa [nodeValue4366, Sparse.eval] using hc.symm

theorem sound4367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4367 node4367Labels = Sparse.eval nodeValue4367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4367) = mixedMoment B node4367 node4367Labels := rfl
  simpa [nodeValue4367, Sparse.eval] using hc.symm

theorem sound4368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4368 node4368Labels = Sparse.eval nodeValue4368 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4368) = mixedMoment B node4368 node4368Labels := rfl
  simpa [nodeValue4368, Sparse.eval] using hc.symm

theorem sound4369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4369 node4369Labels = Sparse.eval nodeValue4369 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4369) = mixedMoment B node4369 node4369Labels := rfl
  simpa [nodeValue4369, Sparse.eval] using hc.symm

theorem sound4370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4370 node4370Labels = Sparse.eval nodeValue4370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4370) = mixedMoment B node4370 node4370Labels := rfl
  simpa [nodeValue4370, Sparse.eval] using hc.symm

theorem sound4371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4371 node4371Labels = Sparse.eval nodeValue4371 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4371) = mixedMoment B node4371 node4371Labels := rfl
  simpa [nodeValue4371, Sparse.eval] using hc.symm

theorem sound4372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4372 node4372Labels = Sparse.eval nodeValue4372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4372) = mixedMoment B node4372 node4372Labels := rfl
  simpa [nodeValue4372, Sparse.eval] using hc.symm

theorem sound4373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4373 node4373Labels = Sparse.eval nodeValue4373 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4373) = mixedMoment B node4373 node4373Labels := rfl
  simpa [nodeValue4373, Sparse.eval] using hc.symm

theorem sound4374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4374 node4374Labels = Sparse.eval nodeValue4374 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4374) = mixedMoment B node4374 node4374Labels := rfl
  simpa [nodeValue4374, Sparse.eval] using hc.symm

theorem sound4375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4375 node4375Labels = Sparse.eval nodeValue4375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4375) = mixedMoment B node4375 node4375Labels := rfl
  simpa [nodeValue4375, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4439 node4439Labels = Sparse.eval nodeValue4439 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4439) = mixedMoment B node4439 node4439Labels := rfl
  simpa [nodeValue4439, Sparse.eval] using hc.symm

theorem sound4440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4440 node4440Labels = Sparse.eval nodeValue4440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4440) = mixedMoment B node4440 node4440Labels := rfl
  simpa [nodeValue4440, Sparse.eval] using hc.symm

theorem sound4442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4442 node4442Labels = Sparse.eval nodeValue4442 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4442) = mixedMoment B node4442 node4442Labels := rfl
  simpa [nodeValue4442, Sparse.eval] using hc.symm

theorem sound4444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4444 node4444Labels = Sparse.eval nodeValue4444 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4444) = mixedMoment B node4444 node4444Labels := rfl
  simpa [nodeValue4444, Sparse.eval] using hc.symm

theorem sound4445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4445 node4445Labels = Sparse.eval nodeValue4445 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4445) = mixedMoment B node4445 node4445Labels := rfl
  simpa [nodeValue4445, Sparse.eval] using hc.symm

theorem sound4459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4459 node4459Labels = Sparse.eval nodeValue4459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4459) = mixedMoment B node4459 node4459Labels := rfl
  simpa [nodeValue4459, Sparse.eval] using hc.symm

theorem sound4464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4464 node4464Labels = Sparse.eval nodeValue4464 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4464) = mixedMoment B node4464 node4464Labels := rfl
  simpa [nodeValue4464, Sparse.eval] using hc.symm

theorem sound4473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4473 node4473Labels = Sparse.eval nodeValue4473 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4473) = mixedMoment B node4473 node4473Labels := rfl
  simpa [nodeValue4473, Sparse.eval] using hc.symm

theorem sound4474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4474 node4474Labels = Sparse.eval nodeValue4474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4474) = mixedMoment B node4474 node4474Labels := rfl
  simpa [nodeValue4474, Sparse.eval] using hc.symm

theorem sound4475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4475 node4475Labels = Sparse.eval nodeValue4475 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4475) = mixedMoment B node4475 node4475Labels := rfl
  simpa [nodeValue4475, Sparse.eval] using hc.symm

theorem sound4476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4476 node4476Labels = Sparse.eval nodeValue4476 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4476) = mixedMoment B node4476 node4476Labels := rfl
  simpa [nodeValue4476, Sparse.eval] using hc.symm

theorem sound4478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4478 node4478Labels = Sparse.eval nodeValue4478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4478) = mixedMoment B node4478 node4478Labels := rfl
  simpa [nodeValue4478, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4480 node4480Labels = Sparse.eval nodeValue4480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4480) = mixedMoment B node4480 node4480Labels := rfl
  simpa [nodeValue4480, Sparse.eval] using hc.symm

theorem sound4481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4481 node4481Labels = Sparse.eval nodeValue4481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4481) = mixedMoment B node4481 node4481Labels := rfl
  simpa [nodeValue4481, Sparse.eval] using hc.symm

theorem sound4494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4494 node4494Labels = Sparse.eval nodeValue4494 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4494) = mixedMoment B node4494 node4494Labels := rfl
  simpa [nodeValue4494, Sparse.eval] using hc.symm

theorem sound4500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4500 node4500Labels = Sparse.eval nodeValue4500 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4500) = mixedMoment B node4500 node4500Labels := rfl
  simpa [nodeValue4500, Sparse.eval] using hc.symm

theorem sound4508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4508 node4508Labels = Sparse.eval nodeValue4508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4508) = mixedMoment B node4508 node4508Labels := rfl
  simpa [nodeValue4508, Sparse.eval] using hc.symm

theorem sound4527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4527 node4527Labels = Sparse.eval nodeValue4527 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4527) = mixedMoment B node4527 node4527Labels := rfl
  simpa [nodeValue4527, Sparse.eval] using hc.symm

theorem sound4528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4528 node4528Labels = Sparse.eval nodeValue4528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4528) = mixedMoment B node4528 node4528Labels := rfl
  simpa [nodeValue4528, Sparse.eval] using hc.symm

theorem sound4529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4529 node4529Labels = Sparse.eval nodeValue4529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4529) = mixedMoment B node4529 node4529Labels := rfl
  simpa [nodeValue4529, Sparse.eval] using hc.symm

theorem sound4530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4530 node4530Labels = Sparse.eval nodeValue4530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4530) = mixedMoment B node4530 node4530Labels := rfl
  simpa [nodeValue4530, Sparse.eval] using hc.symm

theorem sound4531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4531 node4531Labels = Sparse.eval nodeValue4531 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4531) = mixedMoment B node4531 node4531Labels := rfl
  simpa [nodeValue4531, Sparse.eval] using hc.symm

theorem sound4532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4532 node4532Labels = Sparse.eval nodeValue4532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4532) = mixedMoment B node4532 node4532Labels := rfl
  simpa [nodeValue4532, Sparse.eval] using hc.symm

theorem sound4533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4533 node4533Labels = Sparse.eval nodeValue4533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4533) = mixedMoment B node4533 node4533Labels := rfl
  simpa [nodeValue4533, Sparse.eval] using hc.symm

theorem sound4534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4534 node4534Labels = Sparse.eval nodeValue4534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4534) = mixedMoment B node4534 node4534Labels := rfl
  simpa [nodeValue4534, Sparse.eval] using hc.symm

theorem sound4535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4535 node4535Labels = Sparse.eval nodeValue4535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4535) = mixedMoment B node4535 node4535Labels := rfl
  simpa [nodeValue4535, Sparse.eval] using hc.symm

theorem sound4536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4536 node4536Labels = Sparse.eval nodeValue4536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4536) = mixedMoment B node4536 node4536Labels := rfl
  simpa [nodeValue4536, Sparse.eval] using hc.symm

theorem sound4540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4540 node4540Labels = Sparse.eval nodeValue4540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4540) = mixedMoment B node4540 node4540Labels := rfl
  simpa [nodeValue4540, Sparse.eval] using hc.symm

theorem sound4542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4542 node4542Labels = Sparse.eval nodeValue4542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4542) = mixedMoment B node4542 node4542Labels := rfl
  simpa [nodeValue4542, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4545 node4545Labels = Sparse.eval nodeValue4545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4545) = mixedMoment B node4545 node4545Labels := rfl
  simpa [nodeValue4545, Sparse.eval] using hc.symm

theorem sound4547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4547 node4547Labels = Sparse.eval nodeValue4547 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4547) = mixedMoment B node4547 node4547Labels := rfl
  simpa [nodeValue4547, Sparse.eval] using hc.symm

theorem sound4548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4548 node4548Labels = Sparse.eval nodeValue4548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4548) = mixedMoment B node4548 node4548Labels := rfl
  simpa [nodeValue4548, Sparse.eval] using hc.symm

theorem sound4552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4552 node4552Labels = Sparse.eval nodeValue4552 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4552) = mixedMoment B node4552 node4552Labels := rfl
  simpa [nodeValue4552, Sparse.eval] using hc.symm

theorem sound4556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4556 node4556Labels = Sparse.eval nodeValue4556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4556) = mixedMoment B node4556 node4556Labels := rfl
  simpa [nodeValue4556, Sparse.eval] using hc.symm

theorem sound4560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4560 node4560Labels = Sparse.eval nodeValue4560 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4560) = mixedMoment B node4560 node4560Labels := rfl
  simpa [nodeValue4560, Sparse.eval] using hc.symm

theorem sound4589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4589 node4589Labels = Sparse.eval nodeValue4589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4589) = mixedMoment B node4589 node4589Labels := rfl
  simpa [nodeValue4589, Sparse.eval] using hc.symm

theorem sound4590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4590 node4590Labels = Sparse.eval nodeValue4590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4590) = mixedMoment B node4590 node4590Labels := rfl
  simpa [nodeValue4590, Sparse.eval] using hc.symm

theorem sound4591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4591 node4591Labels = Sparse.eval nodeValue4591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4591) = mixedMoment B node4591 node4591Labels := rfl
  simpa [nodeValue4591, Sparse.eval] using hc.symm

theorem sound4592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4592 node4592Labels = Sparse.eval nodeValue4592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4592) = mixedMoment B node4592 node4592Labels := rfl
  simpa [nodeValue4592, Sparse.eval] using hc.symm

theorem sound4593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4593 node4593Labels = Sparse.eval nodeValue4593 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4593) = mixedMoment B node4593 node4593Labels := rfl
  simpa [nodeValue4593, Sparse.eval] using hc.symm

theorem sound4594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4594 node4594Labels = Sparse.eval nodeValue4594 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4594) = mixedMoment B node4594 node4594Labels := rfl
  simpa [nodeValue4594, Sparse.eval] using hc.symm

theorem sound4599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4599 node4599Labels = Sparse.eval nodeValue4599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4599) = mixedMoment B node4599 node4599Labels := rfl
  simpa [nodeValue4599, Sparse.eval] using hc.symm

theorem sound4600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4600 node4600Labels = Sparse.eval nodeValue4600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4600) = mixedMoment B node4600 node4600Labels := rfl
  simpa [nodeValue4600, Sparse.eval] using hc.symm

theorem sound4603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4603 node4603Labels = Sparse.eval nodeValue4603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4603) = mixedMoment B node4603 node4603Labels := rfl
  simpa [nodeValue4603, Sparse.eval] using hc.symm

theorem sound4607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4607 node4607Labels = Sparse.eval nodeValue4607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4607) = mixedMoment B node4607 node4607Labels := rfl
  simpa [nodeValue4607, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4609 node4609Labels = Sparse.eval nodeValue4609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4609) = mixedMoment B node4609 node4609Labels := rfl
  simpa [nodeValue4609, Sparse.eval] using hc.symm

theorem sound4611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4611 node4611Labels = Sparse.eval nodeValue4611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4611) = mixedMoment B node4611 node4611Labels := rfl
  simpa [nodeValue4611, Sparse.eval] using hc.symm

theorem sound4616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4616 node4616Labels = Sparse.eval nodeValue4616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4616) = mixedMoment B node4616 node4616Labels := rfl
  simpa [nodeValue4616, Sparse.eval] using hc.symm

theorem sound4617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4617 node4617Labels = Sparse.eval nodeValue4617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4617) = mixedMoment B node4617 node4617Labels := rfl
  simpa [nodeValue4617, Sparse.eval] using hc.symm

theorem sound4620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4620 node4620Labels = Sparse.eval nodeValue4620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4620) = mixedMoment B node4620 node4620Labels := rfl
  simpa [nodeValue4620, Sparse.eval] using hc.symm

theorem sound4626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4626 node4626Labels = Sparse.eval nodeValue4626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4626) = mixedMoment B node4626 node4626Labels := rfl
  simpa [nodeValue4626, Sparse.eval] using hc.symm

theorem sound4663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4663 node4663Labels = Sparse.eval nodeValue4663 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4663) = mixedMoment B node4663 node4663Labels := rfl
  simpa [nodeValue4663, Sparse.eval] using hc.symm

theorem sound4664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4664 node4664Labels = Sparse.eval nodeValue4664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4664) = mixedMoment B node4664 node4664Labels := rfl
  simpa [nodeValue4664, Sparse.eval] using hc.symm

theorem sound4665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4665 node4665Labels = Sparse.eval nodeValue4665 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4665) = mixedMoment B node4665 node4665Labels := rfl
  simpa [nodeValue4665, Sparse.eval] using hc.symm

theorem sound4666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4666 node4666Labels = Sparse.eval nodeValue4666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4666) = mixedMoment B node4666 node4666Labels := rfl
  simpa [nodeValue4666, Sparse.eval] using hc.symm

theorem sound4667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4667 node4667Labels = Sparse.eval nodeValue4667 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4667) = mixedMoment B node4667 node4667Labels := rfl
  simpa [nodeValue4667, Sparse.eval] using hc.symm

theorem sound4668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4668 node4668Labels = Sparse.eval nodeValue4668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4668) = mixedMoment B node4668 node4668Labels := rfl
  simpa [nodeValue4668, Sparse.eval] using hc.symm

theorem sound4669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4669 node4669Labels = Sparse.eval nodeValue4669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4669) = mixedMoment B node4669 node4669Labels := rfl
  simpa [nodeValue4669, Sparse.eval] using hc.symm

theorem sound4670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4670 node4670Labels = Sparse.eval nodeValue4670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4670) = mixedMoment B node4670 node4670Labels := rfl
  simpa [nodeValue4670, Sparse.eval] using hc.symm

theorem sound4671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4671 node4671Labels = Sparse.eval nodeValue4671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4671) = mixedMoment B node4671 node4671Labels := rfl
  simpa [nodeValue4671, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4677 node4677Labels = Sparse.eval nodeValue4677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4677) = mixedMoment B node4677 node4677Labels := rfl
  simpa [nodeValue4677, Sparse.eval] using hc.symm

theorem sound4680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4680 node4680Labels = Sparse.eval nodeValue4680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4680) = mixedMoment B node4680 node4680Labels := rfl
  simpa [nodeValue4680, Sparse.eval] using hc.symm

theorem sound4682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4682 node4682Labels = Sparse.eval nodeValue4682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4682) = mixedMoment B node4682 node4682Labels := rfl
  simpa [nodeValue4682, Sparse.eval] using hc.symm

theorem sound4683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4683 node4683Labels = Sparse.eval nodeValue4683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4683) = mixedMoment B node4683 node4683Labels := rfl
  simpa [nodeValue4683, Sparse.eval] using hc.symm

theorem sound4687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4687 node4687Labels = Sparse.eval nodeValue4687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4687) = mixedMoment B node4687 node4687Labels := rfl
  simpa [nodeValue4687, Sparse.eval] using hc.symm

theorem sound4690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4690 node4690Labels = Sparse.eval nodeValue4690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4690) = mixedMoment B node4690 node4690Labels := rfl
  simpa [nodeValue4690, Sparse.eval] using hc.symm

theorem sound4694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4694 node4694Labels = Sparse.eval nodeValue4694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4694) = mixedMoment B node4694 node4694Labels := rfl
  simpa [nodeValue4694, Sparse.eval] using hc.symm

theorem sound4695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4695 node4695Labels = Sparse.eval nodeValue4695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4695) = mixedMoment B node4695 node4695Labels := rfl
  simpa [nodeValue4695, Sparse.eval] using hc.symm

theorem sound4696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4696 node4696Labels = Sparse.eval nodeValue4696 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4696) = mixedMoment B node4696 node4696Labels := rfl
  simpa [nodeValue4696, Sparse.eval] using hc.symm

theorem sound4697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4697 node4697Labels = Sparse.eval nodeValue4697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4697) = mixedMoment B node4697 node4697Labels := rfl
  simpa [nodeValue4697, Sparse.eval] using hc.symm

theorem sound4698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4698 node4698Labels = Sparse.eval nodeValue4698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4698) = mixedMoment B node4698 node4698Labels := rfl
  simpa [nodeValue4698, Sparse.eval] using hc.symm

theorem sound4699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4699 node4699Labels = Sparse.eval nodeValue4699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4699) = mixedMoment B node4699 node4699Labels := rfl
  simpa [nodeValue4699, Sparse.eval] using hc.symm

theorem sound4700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4700 node4700Labels = Sparse.eval nodeValue4700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4700) = mixedMoment B node4700 node4700Labels := rfl
  simpa [nodeValue4700, Sparse.eval] using hc.symm

theorem sound4701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4701 node4701Labels = Sparse.eval nodeValue4701 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4701) = mixedMoment B node4701 node4701Labels := rfl
  simpa [nodeValue4701, Sparse.eval] using hc.symm

theorem sound4702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4702 node4702Labels = Sparse.eval nodeValue4702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4702) = mixedMoment B node4702 node4702Labels := rfl
  simpa [nodeValue4702, Sparse.eval] using hc.symm

theorem sound4703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4703 node4703Labels = Sparse.eval nodeValue4703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4703) = mixedMoment B node4703 node4703Labels := rfl
  simpa [nodeValue4703, Sparse.eval] using hc.symm

theorem sound4704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4704 node4704Labels = Sparse.eval nodeValue4704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4704) = mixedMoment B node4704 node4704Labels := rfl
  simpa [nodeValue4704, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1559 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1559 x = (5593363103425757184000 : ℝ) * Sparse.eval nodeValue4158 x := by
  norm_num [reducedTerm1559, nodeValue4158, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1560 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1560 x = (2053490911783944192000 : ℝ) * Sparse.eval nodeValue4159 x := by
  norm_num [reducedTerm1560, nodeValue4159, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1561 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1561 x = (7912784430110343168000 : ℝ) * Sparse.eval nodeValue4160 x := by
  norm_num [reducedTerm1561, nodeValue4160, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1562 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1562 x = (14905306338389655552000 : ℝ) * Sparse.eval nodeValue4161 x := by
  norm_num [reducedTerm1562, nodeValue4161, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1563 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1563 x = (-761589926485032960000 : ℝ) * Sparse.eval nodeValue4162 x := by
  norm_num [reducedTerm1563, nodeValue4162, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1564 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1564 x = (368168093238951936000 : ℝ) * Sparse.eval nodeValue4163 x := by
  norm_num [reducedTerm1564, nodeValue4163, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1565 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1565 x = (-5693122080040550400000 : ℝ) * Sparse.eval nodeValue4169 x := by
  norm_num [reducedTerm1565, nodeValue4169, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1566 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1566 x = (5693122080040550400000 : ℝ) * Sparse.eval nodeValue4173 x := by
  norm_num [reducedTerm1566, nodeValue4173, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1567 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1567 x = (-7248938720166936576000 : ℝ) * Sparse.eval nodeValue4176 x := by
  norm_num [reducedTerm1567, nodeValue4176, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1568 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1568 x = (12502505035448451072000 : ℝ) * Sparse.eval nodeValue4178 x := by
  norm_num [reducedTerm1568, nodeValue4178, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1569 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1569 x = (3231726734524022784000 : ℝ) * Sparse.eval nodeValue4179 x := by
  norm_num [reducedTerm1569, nodeValue4179, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1570 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1570 x = (-716116926716706816000 : ℝ) * Sparse.eval nodeValue4184 x := by
  norm_num [reducedTerm1570, nodeValue4184, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1571 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1571 x = (12949757789032415232000 : ℝ) * Sparse.eval nodeValue4188 x := by
  norm_num [reducedTerm1571, nodeValue4188, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1572 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1572 x = (1197078318949072896000 : ℝ) * Sparse.eval nodeValue4189 x := by
  norm_num [reducedTerm1572, nodeValue4189, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1573 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1573 x = (-97261095987707904000 : ℝ) * Sparse.eval nodeValue4193 x := by
  norm_num [reducedTerm1573, nodeValue4193, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1574 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1574 x = (-2940208664430772224000 : ℝ) * Sparse.eval nodeValue4327 x := by
  norm_num [reducedTerm1574, nodeValue4327, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1575 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1575 x = (-4362670631726088192000 : ℝ) * Sparse.eval nodeValue4328 x := by
  norm_num [reducedTerm1575, nodeValue4328, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1576 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1576 x = (-2461303460148019200000 : ℝ) * Sparse.eval nodeValue4330 x := by
  norm_num [reducedTerm1576, nodeValue4330, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1577 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1577 x = (2418118564976787456000 : ℝ) * Sparse.eval nodeValue4331 x := by
  norm_num [reducedTerm1577, nodeValue4331, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1578 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1578 x = (11195660614200459264000 : ℝ) * Sparse.eval nodeValue4332 x := by
  norm_num [reducedTerm1578, nodeValue4332, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1579 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1579 x = (5221252535535009792000 : ℝ) * Sparse.eval nodeValue4333 x := by
  norm_num [reducedTerm1579, nodeValue4333, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1580 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1580 x = (16817110373118246912000 : ℝ) * Sparse.eval nodeValue4334 x := by
  norm_num [reducedTerm1580, nodeValue4334, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1581 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1581 x = (14664773306621362176000 : ℝ) * Sparse.eval nodeValue4335 x := by
  norm_num [reducedTerm1581, nodeValue4335, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1582 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1582 x = (3643443110785056768000 : ℝ) * Sparse.eval nodeValue4336 x := by
  norm_num [reducedTerm1582, nodeValue4336, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1583 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1583 x = (-4407922008608735232000 : ℝ) * Sparse.eval nodeValue4345 x := by
  norm_num [reducedTerm1583, nodeValue4345, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1584 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1584 x = (1765372925391667200000 : ℝ) * Sparse.eval nodeValue4347 x := by
  norm_num [reducedTerm1584, nodeValue4347, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1585 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1585 x = (3157621618243534848000 : ℝ) * Sparse.eval nodeValue4353 x := by
  norm_num [reducedTerm1585, nodeValue4353, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1586 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1586 x = (17560644030085201920000 : ℝ) * Sparse.eval nodeValue4357 x := by
  norm_num [reducedTerm1586, nodeValue4357, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1587 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1587 x = (3552084349459365888000 : ℝ) * Sparse.eval nodeValue4358 x := by
  norm_num [reducedTerm1587, nodeValue4358, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1588 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1588 x = (-483156672380928000000 : ℝ) * Sparse.eval nodeValue4362 x := by
  norm_num [reducedTerm1588, nodeValue4362, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1589 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1589 x = (2200392789160624128000 : ℝ) * Sparse.eval nodeValue4363 x := by
  norm_num [reducedTerm1589, nodeValue4363, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1590 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1590 x = (8030508152059330560000 : ℝ) * Sparse.eval nodeValue4364 x := by
  norm_num [reducedTerm1590, nodeValue4364, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1591 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1591 x = (2333580197392023552000 : ℝ) * Sparse.eval nodeValue4365 x := by
  norm_num [reducedTerm1591, nodeValue4365, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1592 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1592 x = (-19011338932645527552000 : ℝ) * Sparse.eval nodeValue4366 x := by
  norm_num [reducedTerm1592, nodeValue4366, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1593 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1593 x = (-6166085797247975424000 : ℝ) * Sparse.eval nodeValue4367 x := by
  norm_num [reducedTerm1593, nodeValue4367, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1594 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1594 x = (-19274765724083552256000 : ℝ) * Sparse.eval nodeValue4368 x := by
  norm_num [reducedTerm1594, nodeValue4368, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1595 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1595 x = (5544829063963607040000 : ℝ) * Sparse.eval nodeValue4369 x := by
  norm_num [reducedTerm1595, nodeValue4369, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1596 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1596 x = (6870049258648633344000 : ℝ) * Sparse.eval nodeValue4370 x := by
  norm_num [reducedTerm1596, nodeValue4370, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1597 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1597 x = (476851978047062016000 : ℝ) * Sparse.eval nodeValue4371 x := by
  norm_num [reducedTerm1597, nodeValue4371, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1598 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1598 x = (-382460818968281088000 : ℝ) * Sparse.eval nodeValue4372 x := by
  norm_num [reducedTerm1598, nodeValue4372, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1599 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1599 x = (9211036774796623872000 : ℝ) * Sparse.eval nodeValue4373 x := by
  norm_num [reducedTerm1599, nodeValue4373, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1600 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1600 x = (17575348253457383424000 : ℝ) * Sparse.eval nodeValue4374 x := by
  norm_num [reducedTerm1600, nodeValue4374, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1601 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1601 x = (-34507362327330816000 : ℝ) * Sparse.eval nodeValue4375 x := by
  norm_num [reducedTerm1601, nodeValue4375, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1602 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1602 x = (-13515513231445327872000 : ℝ) * Sparse.eval nodeValue4439 x := by
  norm_num [reducedTerm1602, nodeValue4439, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1603 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1603 x = (-19241651017431908352000 : ℝ) * Sparse.eval nodeValue4440 x := by
  norm_num [reducedTerm1603, nodeValue4440, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1604 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1604 x = (-2216492015908552704000 : ℝ) * Sparse.eval nodeValue4442 x := by
  norm_num [reducedTerm1604, nodeValue4442, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1605 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1605 x = (9836938992486187008000 : ℝ) * Sparse.eval nodeValue4444 x := by
  norm_num [reducedTerm1605, nodeValue4444, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1606 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1606 x = (-2888188832156221440000 : ℝ) * Sparse.eval nodeValue4445 x := by
  norm_num [reducedTerm1606, nodeValue4445, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1607 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1607 x = (-24911231228112273408000 : ℝ) * Sparse.eval nodeValue4459 x := by
  norm_num [reducedTerm1607, nodeValue4459, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1608 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1608 x = (-11076753145762676736000 : ℝ) * Sparse.eval nodeValue4464 x := by
  norm_num [reducedTerm1608, nodeValue4464, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1609 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1609 x = (-3609473985785364480000 : ℝ) * Sparse.eval nodeValue4473 x := by
  norm_num [reducedTerm1609, nodeValue4473, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1610 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1610 x = (-8041495388340879360000 : ℝ) * Sparse.eval nodeValue4474 x := by
  norm_num [reducedTerm1610, nodeValue4474, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1611 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1611 x = (-8553475027189628928000 : ℝ) * Sparse.eval nodeValue4475 x := by
  norm_num [reducedTerm1611, nodeValue4475, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1612 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1612 x = (15007094450225676288000 : ℝ) * Sparse.eval nodeValue4476 x := by
  norm_num [reducedTerm1612, nodeValue4476, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1613 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1613 x = (-14254645456457957376000 : ℝ) * Sparse.eval nodeValue4478 x := by
  norm_num [reducedTerm1613, nodeValue4478, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1614 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1614 x = (18099022219727339520000 : ℝ) * Sparse.eval nodeValue4480 x := by
  norm_num [reducedTerm1614, nodeValue4480, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1615 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1615 x = (-1896689902925905920000 : ℝ) * Sparse.eval nodeValue4481 x := by
  norm_num [reducedTerm1615, nodeValue4481, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1616 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1616 x = (-4276208522593566720000 : ℝ) * Sparse.eval nodeValue4494 x := by
  norm_num [reducedTerm1616, nodeValue4494, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1617 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1617 x = (7704059375140208640000 : ℝ) * Sparse.eval nodeValue4500 x := by
  norm_num [reducedTerm1617, nodeValue4500, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1618 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1618 x = (-4470330666478731264000 : ℝ) * Sparse.eval nodeValue4508 x := by
  norm_num [reducedTerm1618, nodeValue4508, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1619 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1619 x = (5324013064735948800000 : ℝ) * Sparse.eval nodeValue4527 x := by
  norm_num [reducedTerm1619, nodeValue4527, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1620 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1620 x = (4730383620298506240000 : ℝ) * Sparse.eval nodeValue4528 x := by
  norm_num [reducedTerm1620, nodeValue4528, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1621 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1621 x = (-6127988909884047360000 : ℝ) * Sparse.eval nodeValue4529 x := by
  norm_num [reducedTerm1621, nodeValue4529, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1622 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1622 x = (1083441906686361600000 : ℝ) * Sparse.eval nodeValue4530 x := by
  norm_num [reducedTerm1622, nodeValue4530, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1623 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1623 x = (7918345276749250560000 : ℝ) * Sparse.eval nodeValue4531 x := by
  norm_num [reducedTerm1623, nodeValue4531, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1624 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1624 x = (-4345332613952569344000 : ℝ) * Sparse.eval nodeValue4532 x := by
  norm_num [reducedTerm1624, nodeValue4532, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1625 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1625 x = (215658764367298560000 : ℝ) * Sparse.eval nodeValue4533 x := by
  norm_num [reducedTerm1625, nodeValue4533, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1626 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1626 x = (-8819748555444191232000 : ℝ) * Sparse.eval nodeValue4534 x := by
  norm_num [reducedTerm1626, nodeValue4534, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1627 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1627 x = (-3968589383710801920000 : ℝ) * Sparse.eval nodeValue4535 x := by
  norm_num [reducedTerm1627, nodeValue4535, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1628 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1628 x = (-14113916079842525184000 : ℝ) * Sparse.eval nodeValue4536 x := by
  norm_num [reducedTerm1628, nodeValue4536, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1629 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1629 x = (8499226830254899200000 : ℝ) * Sparse.eval nodeValue4540 x := by
  norm_num [reducedTerm1629, nodeValue4540, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1630 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1630 x = (23732159479676928000000 : ℝ) * Sparse.eval nodeValue4542 x := by
  norm_num [reducedTerm1630, nodeValue4542, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1631 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1631 x = (36626429413905924096000 : ℝ) * Sparse.eval nodeValue4545 x := by
  norm_num [reducedTerm1631, nodeValue4545, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1632 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1632 x = (15452458461052010496000 : ℝ) * Sparse.eval nodeValue4547 x := by
  norm_num [reducedTerm1632, nodeValue4547, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1633 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1633 x = (14639794103047421952000 : ℝ) * Sparse.eval nodeValue4548 x := by
  norm_num [reducedTerm1633, nodeValue4548, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1634 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1634 x = (-11692002548014645248000 : ℝ) * Sparse.eval nodeValue4552 x := by
  norm_num [reducedTerm1634, nodeValue4552, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1635 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1635 x = (-8265191798831579136000 : ℝ) * Sparse.eval nodeValue4556 x := by
  norm_num [reducedTerm1635, nodeValue4556, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1636 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1636 x = (-1142729568214843392000 : ℝ) * Sparse.eval nodeValue4560 x := by
  norm_num [reducedTerm1636, nodeValue4560, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1637 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1637 x = (1220339788645662720000 : ℝ) * Sparse.eval nodeValue4589 x := by
  norm_num [reducedTerm1637, nodeValue4589, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1638 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1638 x = (6476173958106316800000 : ℝ) * Sparse.eval nodeValue4590 x := by
  norm_num [reducedTerm1638, nodeValue4590, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1639 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1639 x = (-6085807301323653120000 : ℝ) * Sparse.eval nodeValue4591 x := by
  norm_num [reducedTerm1639, nodeValue4591, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1640 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1640 x = (-15157581060922933248000 : ℝ) * Sparse.eval nodeValue4592 x := by
  norm_num [reducedTerm1640, nodeValue4592, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1641 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1641 x = (-7559615864792678400000 : ℝ) * Sparse.eval nodeValue4593 x := by
  norm_num [reducedTerm1641, nodeValue4593, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1642 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1642 x = (3011436319122653184000 : ℝ) * Sparse.eval nodeValue4594 x := by
  norm_num [reducedTerm1642, nodeValue4594, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1643 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1643 x = (10617849996847349760000 : ℝ) * Sparse.eval nodeValue4599 x := by
  norm_num [reducedTerm1643, nodeValue4599, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1644 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1644 x = (-1692590756154310656000 : ℝ) * Sparse.eval nodeValue4600 x := by
  norm_num [reducedTerm1644, nodeValue4600, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1645 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1645 x = (-35786008029537239040000 : ℝ) * Sparse.eval nodeValue4603 x := by
  norm_num [reducedTerm1645, nodeValue4603, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1646 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1646 x = (-38147155763799785472000 : ℝ) * Sparse.eval nodeValue4607 x := by
  norm_num [reducedTerm1646, nodeValue4607, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1647 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1647 x = (-5558333516289146880000 : ℝ) * Sparse.eval nodeValue4609 x := by
  norm_num [reducedTerm1647, nodeValue4609, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1648 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1648 x = (-10846457928298266624000 : ℝ) * Sparse.eval nodeValue4611 x := by
  norm_num [reducedTerm1648, nodeValue4611, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1649 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1649 x = (-2261821083603959808000 : ℝ) * Sparse.eval nodeValue4616 x := by
  norm_num [reducedTerm1649, nodeValue4616, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1650 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1650 x = (-757540324473569280000 : ℝ) * Sparse.eval nodeValue4617 x := by
  norm_num [reducedTerm1650, nodeValue4617, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1651 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1651 x = (-747979948051660800000 : ℝ) * Sparse.eval nodeValue4620 x := by
  norm_num [reducedTerm1651, nodeValue4620, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1652 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1652 x = (-875893157801754624000 : ℝ) * Sparse.eval nodeValue4626 x := by
  norm_num [reducedTerm1652, nodeValue4626, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1653 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1653 x = (-4224921028263936000000 : ℝ) * Sparse.eval nodeValue4663 x := by
  norm_num [reducedTerm1653, nodeValue4663, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1654 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1654 x = (-5601048967764246528000 : ℝ) * Sparse.eval nodeValue4664 x := by
  norm_num [reducedTerm1654, nodeValue4664, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1655 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1655 x = (4938879732374568960000 : ℝ) * Sparse.eval nodeValue4665 x := by
  norm_num [reducedTerm1655, nodeValue4665, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1656 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1656 x = (-7805365883397734400000 : ℝ) * Sparse.eval nodeValue4666 x := by
  norm_num [reducedTerm1656, nodeValue4666, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1657 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1657 x = (1400988782872756224000 : ℝ) * Sparse.eval nodeValue4667 x := by
  norm_num [reducedTerm1657, nodeValue4667, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1658 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1658 x = (1662907014489047040000 : ℝ) * Sparse.eval nodeValue4668 x := by
  norm_num [reducedTerm1658, nodeValue4668, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1659 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1659 x = (-799209977907511296000 : ℝ) * Sparse.eval nodeValue4669 x := by
  norm_num [reducedTerm1659, nodeValue4669, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1660 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1660 x = (-16331923481962217472000 : ℝ) * Sparse.eval nodeValue4670 x := by
  norm_num [reducedTerm1660, nodeValue4670, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1661 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1661 x = (1843237901377732608000 : ℝ) * Sparse.eval nodeValue4671 x := by
  norm_num [reducedTerm1661, nodeValue4671, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1662 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1662 x = (-5693122080040550400000 : ℝ) * Sparse.eval nodeValue4677 x := by
  norm_num [reducedTerm1662, nodeValue4677, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1663 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1663 x = (2989735781018370048000 : ℝ) * Sparse.eval nodeValue4680 x := by
  norm_num [reducedTerm1663, nodeValue4680, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic1664 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1664 x = (-20337198821419253760000 : ℝ) * Sparse.eval nodeValue4682 x := by
  norm_num [reducedTerm1664, nodeValue4682, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1665 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1665 x = (-4166088676073275392000 : ℝ) * Sparse.eval nodeValue4683 x := by
  norm_num [reducedTerm1665, nodeValue4683, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1666 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1666 x = (4331084313932070912000 : ℝ) * Sparse.eval nodeValue4687 x := by
  norm_num [reducedTerm1666, nodeValue4687, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1667 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1667 x = (-7832344641172144128000 : ℝ) * Sparse.eval nodeValue4690 x := by
  norm_num [reducedTerm1667, nodeValue4690, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1668 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1668 x = (419207923271467008000 : ℝ) * Sparse.eval nodeValue4694 x := by
  norm_num [reducedTerm1668, nodeValue4694, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1669 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1669 x = (2088377879151771648000 : ℝ) * Sparse.eval nodeValue4695 x := by
  norm_num [reducedTerm1669, nodeValue4695, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1670 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1670 x = (4668687916798574592000 : ℝ) * Sparse.eval nodeValue4696 x := by
  norm_num [reducedTerm1670, nodeValue4696, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1671 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1671 x = (-47757709229948928000 : ℝ) * Sparse.eval nodeValue4697 x := by
  norm_num [reducedTerm1671, nodeValue4697, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1672 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1672 x = (-11360929018687782912000 : ℝ) * Sparse.eval nodeValue4698 x := by
  norm_num [reducedTerm1672, nodeValue4698, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1673 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1673 x = (-12243947554527510528000 : ℝ) * Sparse.eval nodeValue4699 x := by
  norm_num [reducedTerm1673, nodeValue4699, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1674 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1674 x = (-9017233195750391808000 : ℝ) * Sparse.eval nodeValue4700 x := by
  norm_num [reducedTerm1674, nodeValue4700, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1675 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1675 x = (1426161328576266240000 : ℝ) * Sparse.eval nodeValue4701 x := by
  norm_num [reducedTerm1675, nodeValue4701, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1676 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1676 x = (323950101685862400000 : ℝ) * Sparse.eval nodeValue4702 x := by
  norm_num [reducedTerm1676, nodeValue4702, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1677 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1677 x = (2481540634666598400000 : ℝ) * Sparse.eval nodeValue4703 x := by
  norm_num [reducedTerm1677, nodeValue4703, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic1678 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1678 x = (6123206211439951872000 : ℝ) * Sparse.eval nodeValue4704 x := by
  norm_num [reducedTerm1678, nodeValue4704, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1556Check : reducedMerge1556 = Integer.Sparse.mergeBy masterLess reducedTerm1560 reducedTerm1561 := by decide +kernel

theorem reducedMerge1557Check : reducedMerge1557 = Integer.Sparse.mergeBy masterLess reducedTerm1559 reducedMerge1556 := by decide +kernel

theorem reducedMerge1558Check : reducedMerge1558 = Integer.Sparse.mergeBy masterLess reducedTerm1562 reducedTerm1563 := by decide +kernel

theorem reducedMerge1559Check : reducedMerge1559 = Integer.Sparse.mergeBy masterLess reducedTerm1564 reducedTerm1565 := by decide +kernel

theorem reducedMerge1560Check : reducedMerge1560 = Integer.Sparse.mergeBy masterLess reducedMerge1558 reducedMerge1559 := by decide +kernel

theorem reducedMerge1561Check : reducedMerge1561 = Integer.Sparse.mergeBy masterLess reducedMerge1557 reducedMerge1560 := by decide +kernel

theorem reducedMerge1562Check : reducedMerge1562 = Integer.Sparse.mergeBy masterLess reducedTerm1566 reducedTerm1567 := by decide +kernel

theorem reducedMerge1563Check : reducedMerge1563 = Integer.Sparse.mergeBy masterLess reducedTerm1568 reducedTerm1569 := by decide +kernel

theorem reducedMerge1564Check : reducedMerge1564 = Integer.Sparse.mergeBy masterLess reducedMerge1562 reducedMerge1563 := by decide +kernel

theorem reducedMerge1565Check : reducedMerge1565 = Integer.Sparse.mergeBy masterLess reducedTerm1570 reducedTerm1571 := by decide +kernel

theorem reducedMerge1566Check : reducedMerge1566 = Integer.Sparse.mergeBy masterLess reducedTerm1572 reducedTerm1573 := by decide +kernel

theorem reducedMerge1567Check : reducedMerge1567 = Integer.Sparse.mergeBy masterLess reducedMerge1565 reducedMerge1566 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1568Check : reducedMerge1568 = Integer.Sparse.mergeBy masterLess reducedMerge1564 reducedMerge1567 := by decide +kernel

theorem reducedMerge1569Check : reducedMerge1569 = Integer.Sparse.mergeBy masterLess reducedMerge1561 reducedMerge1568 := by decide +kernel

theorem reducedMerge1570Check : reducedMerge1570 = Integer.Sparse.mergeBy masterLess reducedTerm1575 reducedTerm1576 := by decide +kernel

theorem reducedMerge1571Check : reducedMerge1571 = Integer.Sparse.mergeBy masterLess reducedTerm1574 reducedMerge1570 := by decide +kernel

theorem reducedMerge1572Check : reducedMerge1572 = Integer.Sparse.mergeBy masterLess reducedTerm1577 reducedTerm1578 := by decide +kernel

theorem reducedMerge1573Check : reducedMerge1573 = Integer.Sparse.mergeBy masterLess reducedTerm1579 reducedTerm1580 := by decide +kernel

theorem reducedMerge1574Check : reducedMerge1574 = Integer.Sparse.mergeBy masterLess reducedMerge1572 reducedMerge1573 := by decide +kernel

theorem reducedMerge1575Check : reducedMerge1575 = Integer.Sparse.mergeBy masterLess reducedMerge1571 reducedMerge1574 := by decide +kernel

theorem reducedMerge1576Check : reducedMerge1576 = Integer.Sparse.mergeBy masterLess reducedTerm1581 reducedTerm1582 := by decide +kernel

theorem reducedMerge1577Check : reducedMerge1577 = Integer.Sparse.mergeBy masterLess reducedTerm1583 reducedTerm1584 := by decide +kernel

theorem reducedMerge1578Check : reducedMerge1578 = Integer.Sparse.mergeBy masterLess reducedMerge1576 reducedMerge1577 := by decide +kernel

theorem reducedMerge1579Check : reducedMerge1579 = Integer.Sparse.mergeBy masterLess reducedTerm1585 reducedTerm1586 := by decide +kernel

theorem reducedMerge1580Check : reducedMerge1580 = Integer.Sparse.mergeBy masterLess reducedTerm1587 reducedTerm1588 := by decide +kernel

theorem reducedMerge1581Check : reducedMerge1581 = Integer.Sparse.mergeBy masterLess reducedMerge1579 reducedMerge1580 := by decide +kernel

theorem reducedMerge1582Check : reducedMerge1582 = Integer.Sparse.mergeBy masterLess reducedMerge1578 reducedMerge1581 := by decide +kernel

theorem reducedMerge1583Check : reducedMerge1583 = Integer.Sparse.mergeBy masterLess reducedMerge1575 reducedMerge1582 := by decide +kernel

theorem reducedMerge1584Check : reducedMerge1584 = Integer.Sparse.mergeBy masterLess reducedMerge1569 reducedMerge1583 := by decide +kernel

theorem reducedMerge1585Check : reducedMerge1585 = Integer.Sparse.mergeBy masterLess reducedTerm1590 reducedTerm1591 := by decide +kernel

theorem reducedMerge1586Check : reducedMerge1586 = Integer.Sparse.mergeBy masterLess reducedTerm1589 reducedMerge1585 := by decide +kernel

theorem reducedMerge1587Check : reducedMerge1587 = Integer.Sparse.mergeBy masterLess reducedTerm1592 reducedTerm1593 := by decide +kernel

theorem reducedMerge1588Check : reducedMerge1588 = Integer.Sparse.mergeBy masterLess reducedTerm1594 reducedTerm1595 := by decide +kernel

theorem reducedMerge1589Check : reducedMerge1589 = Integer.Sparse.mergeBy masterLess reducedMerge1587 reducedMerge1588 := by decide +kernel

theorem reducedMerge1590Check : reducedMerge1590 = Integer.Sparse.mergeBy masterLess reducedMerge1586 reducedMerge1589 := by decide +kernel

theorem reducedMerge1591Check : reducedMerge1591 = Integer.Sparse.mergeBy masterLess reducedTerm1596 reducedTerm1597 := by decide +kernel

theorem reducedMerge1592Check : reducedMerge1592 = Integer.Sparse.mergeBy masterLess reducedTerm1598 reducedTerm1599 := by decide +kernel

theorem reducedMerge1593Check : reducedMerge1593 = Integer.Sparse.mergeBy masterLess reducedMerge1591 reducedMerge1592 := by decide +kernel

theorem reducedMerge1594Check : reducedMerge1594 = Integer.Sparse.mergeBy masterLess reducedTerm1600 reducedTerm1601 := by decide +kernel

theorem reducedMerge1595Check : reducedMerge1595 = Integer.Sparse.mergeBy masterLess reducedTerm1602 reducedTerm1603 := by decide +kernel

theorem reducedMerge1596Check : reducedMerge1596 = Integer.Sparse.mergeBy masterLess reducedMerge1594 reducedMerge1595 := by decide +kernel

theorem reducedMerge1597Check : reducedMerge1597 = Integer.Sparse.mergeBy masterLess reducedMerge1593 reducedMerge1596 := by decide +kernel

theorem reducedMerge1598Check : reducedMerge1598 = Integer.Sparse.mergeBy masterLess reducedMerge1590 reducedMerge1597 := by decide +kernel

theorem reducedMerge1599Check : reducedMerge1599 = Integer.Sparse.mergeBy masterLess reducedTerm1605 reducedTerm1606 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1600Check : reducedMerge1600 = Integer.Sparse.mergeBy masterLess reducedTerm1604 reducedMerge1599 := by decide +kernel

theorem reducedMerge1601Check : reducedMerge1601 = Integer.Sparse.mergeBy masterLess reducedTerm1607 reducedTerm1608 := by decide +kernel

theorem reducedMerge1602Check : reducedMerge1602 = Integer.Sparse.mergeBy masterLess reducedTerm1609 reducedTerm1610 := by decide +kernel

theorem reducedMerge1603Check : reducedMerge1603 = Integer.Sparse.mergeBy masterLess reducedMerge1601 reducedMerge1602 := by decide +kernel

theorem reducedMerge1604Check : reducedMerge1604 = Integer.Sparse.mergeBy masterLess reducedMerge1600 reducedMerge1603 := by decide +kernel

theorem reducedMerge1605Check : reducedMerge1605 = Integer.Sparse.mergeBy masterLess reducedTerm1611 reducedTerm1612 := by decide +kernel

theorem reducedMerge1606Check : reducedMerge1606 = Integer.Sparse.mergeBy masterLess reducedTerm1613 reducedTerm1614 := by decide +kernel

theorem reducedMerge1607Check : reducedMerge1607 = Integer.Sparse.mergeBy masterLess reducedMerge1605 reducedMerge1606 := by decide +kernel

theorem reducedMerge1608Check : reducedMerge1608 = Integer.Sparse.mergeBy masterLess reducedTerm1615 reducedTerm1616 := by decide +kernel

theorem reducedMerge1609Check : reducedMerge1609 = Integer.Sparse.mergeBy masterLess reducedTerm1617 reducedTerm1618 := by decide +kernel

theorem reducedMerge1610Check : reducedMerge1610 = Integer.Sparse.mergeBy masterLess reducedMerge1608 reducedMerge1609 := by decide +kernel

theorem reducedMerge1611Check : reducedMerge1611 = Integer.Sparse.mergeBy masterLess reducedMerge1607 reducedMerge1610 := by decide +kernel

theorem reducedMerge1612Check : reducedMerge1612 = Integer.Sparse.mergeBy masterLess reducedMerge1604 reducedMerge1611 := by decide +kernel

theorem reducedMerge1613Check : reducedMerge1613 = Integer.Sparse.mergeBy masterLess reducedMerge1598 reducedMerge1612 := by decide +kernel

theorem reducedMerge1614Check : reducedMerge1614 = Integer.Sparse.mergeBy masterLess reducedMerge1584 reducedMerge1613 := by decide +kernel

theorem reducedMerge1615Check : reducedMerge1615 = Integer.Sparse.mergeBy masterLess reducedTerm1620 reducedTerm1621 := by decide +kernel

theorem reducedMerge1616Check : reducedMerge1616 = Integer.Sparse.mergeBy masterLess reducedTerm1619 reducedMerge1615 := by decide +kernel

theorem reducedMerge1617Check : reducedMerge1617 = Integer.Sparse.mergeBy masterLess reducedTerm1622 reducedTerm1623 := by decide +kernel

theorem reducedMerge1618Check : reducedMerge1618 = Integer.Sparse.mergeBy masterLess reducedTerm1624 reducedTerm1625 := by decide +kernel

theorem reducedMerge1619Check : reducedMerge1619 = Integer.Sparse.mergeBy masterLess reducedMerge1617 reducedMerge1618 := by decide +kernel

theorem reducedMerge1620Check : reducedMerge1620 = Integer.Sparse.mergeBy masterLess reducedMerge1616 reducedMerge1619 := by decide +kernel

theorem reducedMerge1621Check : reducedMerge1621 = Integer.Sparse.mergeBy masterLess reducedTerm1626 reducedTerm1627 := by decide +kernel

theorem reducedMerge1622Check : reducedMerge1622 = Integer.Sparse.mergeBy masterLess reducedTerm1628 reducedTerm1629 := by decide +kernel

theorem reducedMerge1623Check : reducedMerge1623 = Integer.Sparse.mergeBy masterLess reducedMerge1621 reducedMerge1622 := by decide +kernel

theorem reducedMerge1624Check : reducedMerge1624 = Integer.Sparse.mergeBy masterLess reducedTerm1630 reducedTerm1631 := by decide +kernel

theorem reducedMerge1625Check : reducedMerge1625 = Integer.Sparse.mergeBy masterLess reducedTerm1632 reducedTerm1633 := by decide +kernel

theorem reducedMerge1626Check : reducedMerge1626 = Integer.Sparse.mergeBy masterLess reducedMerge1624 reducedMerge1625 := by decide +kernel

theorem reducedMerge1627Check : reducedMerge1627 = Integer.Sparse.mergeBy masterLess reducedMerge1623 reducedMerge1626 := by decide +kernel

theorem reducedMerge1628Check : reducedMerge1628 = Integer.Sparse.mergeBy masterLess reducedMerge1620 reducedMerge1627 := by decide +kernel

theorem reducedMerge1629Check : reducedMerge1629 = Integer.Sparse.mergeBy masterLess reducedTerm1635 reducedTerm1636 := by decide +kernel

theorem reducedMerge1630Check : reducedMerge1630 = Integer.Sparse.mergeBy masterLess reducedTerm1634 reducedMerge1629 := by decide +kernel

theorem reducedMerge1631Check : reducedMerge1631 = Integer.Sparse.mergeBy masterLess reducedTerm1637 reducedTerm1638 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1632Check : reducedMerge1632 = Integer.Sparse.mergeBy masterLess reducedTerm1639 reducedTerm1640 := by decide +kernel

theorem reducedMerge1633Check : reducedMerge1633 = Integer.Sparse.mergeBy masterLess reducedMerge1631 reducedMerge1632 := by decide +kernel

theorem reducedMerge1634Check : reducedMerge1634 = Integer.Sparse.mergeBy masterLess reducedMerge1630 reducedMerge1633 := by decide +kernel

theorem reducedMerge1635Check : reducedMerge1635 = Integer.Sparse.mergeBy masterLess reducedTerm1641 reducedTerm1642 := by decide +kernel

theorem reducedMerge1636Check : reducedMerge1636 = Integer.Sparse.mergeBy masterLess reducedTerm1643 reducedTerm1644 := by decide +kernel

theorem reducedMerge1637Check : reducedMerge1637 = Integer.Sparse.mergeBy masterLess reducedMerge1635 reducedMerge1636 := by decide +kernel

theorem reducedMerge1638Check : reducedMerge1638 = Integer.Sparse.mergeBy masterLess reducedTerm1645 reducedTerm1646 := by decide +kernel

theorem reducedMerge1639Check : reducedMerge1639 = Integer.Sparse.mergeBy masterLess reducedTerm1647 reducedTerm1648 := by decide +kernel

theorem reducedMerge1640Check : reducedMerge1640 = Integer.Sparse.mergeBy masterLess reducedMerge1638 reducedMerge1639 := by decide +kernel

theorem reducedMerge1641Check : reducedMerge1641 = Integer.Sparse.mergeBy masterLess reducedMerge1637 reducedMerge1640 := by decide +kernel

theorem reducedMerge1642Check : reducedMerge1642 = Integer.Sparse.mergeBy masterLess reducedMerge1634 reducedMerge1641 := by decide +kernel

theorem reducedMerge1643Check : reducedMerge1643 = Integer.Sparse.mergeBy masterLess reducedMerge1628 reducedMerge1642 := by decide +kernel

theorem reducedMerge1644Check : reducedMerge1644 = Integer.Sparse.mergeBy masterLess reducedTerm1650 reducedTerm1651 := by decide +kernel

theorem reducedMerge1645Check : reducedMerge1645 = Integer.Sparse.mergeBy masterLess reducedTerm1649 reducedMerge1644 := by decide +kernel

theorem reducedMerge1646Check : reducedMerge1646 = Integer.Sparse.mergeBy masterLess reducedTerm1652 reducedTerm1653 := by decide +kernel

theorem reducedMerge1647Check : reducedMerge1647 = Integer.Sparse.mergeBy masterLess reducedTerm1654 reducedTerm1655 := by decide +kernel

theorem reducedMerge1648Check : reducedMerge1648 = Integer.Sparse.mergeBy masterLess reducedMerge1646 reducedMerge1647 := by decide +kernel

theorem reducedMerge1649Check : reducedMerge1649 = Integer.Sparse.mergeBy masterLess reducedMerge1645 reducedMerge1648 := by decide +kernel

theorem reducedMerge1650Check : reducedMerge1650 = Integer.Sparse.mergeBy masterLess reducedTerm1656 reducedTerm1657 := by decide +kernel

theorem reducedMerge1651Check : reducedMerge1651 = Integer.Sparse.mergeBy masterLess reducedTerm1658 reducedTerm1659 := by decide +kernel

theorem reducedMerge1652Check : reducedMerge1652 = Integer.Sparse.mergeBy masterLess reducedMerge1650 reducedMerge1651 := by decide +kernel

theorem reducedMerge1653Check : reducedMerge1653 = Integer.Sparse.mergeBy masterLess reducedTerm1660 reducedTerm1661 := by decide +kernel

theorem reducedMerge1654Check : reducedMerge1654 = Integer.Sparse.mergeBy masterLess reducedTerm1662 reducedTerm1663 := by decide +kernel

theorem reducedMerge1655Check : reducedMerge1655 = Integer.Sparse.mergeBy masterLess reducedMerge1653 reducedMerge1654 := by decide +kernel

theorem reducedMerge1656Check : reducedMerge1656 = Integer.Sparse.mergeBy masterLess reducedMerge1652 reducedMerge1655 := by decide +kernel

theorem reducedMerge1657Check : reducedMerge1657 = Integer.Sparse.mergeBy masterLess reducedMerge1649 reducedMerge1656 := by decide +kernel

theorem reducedMerge1658Check : reducedMerge1658 = Integer.Sparse.mergeBy masterLess reducedTerm1665 reducedTerm1666 := by decide +kernel

theorem reducedMerge1659Check : reducedMerge1659 = Integer.Sparse.mergeBy masterLess reducedTerm1664 reducedMerge1658 := by decide +kernel

theorem reducedMerge1660Check : reducedMerge1660 = Integer.Sparse.mergeBy masterLess reducedTerm1667 reducedTerm1668 := by decide +kernel

theorem reducedMerge1661Check : reducedMerge1661 = Integer.Sparse.mergeBy masterLess reducedTerm1669 reducedTerm1670 := by decide +kernel

theorem reducedMerge1662Check : reducedMerge1662 = Integer.Sparse.mergeBy masterLess reducedMerge1660 reducedMerge1661 := by decide +kernel

theorem reducedMerge1663Check : reducedMerge1663 = Integer.Sparse.mergeBy masterLess reducedMerge1659 reducedMerge1662 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge1664Check : reducedMerge1664 = Integer.Sparse.mergeBy masterLess reducedTerm1671 reducedTerm1672 := by decide +kernel

theorem reducedMerge1665Check : reducedMerge1665 = Integer.Sparse.mergeBy masterLess reducedTerm1673 reducedTerm1674 := by decide +kernel

theorem reducedMerge1666Check : reducedMerge1666 = Integer.Sparse.mergeBy masterLess reducedMerge1664 reducedMerge1665 := by decide +kernel

theorem reducedMerge1667Check : reducedMerge1667 = Integer.Sparse.mergeBy masterLess reducedTerm1675 reducedTerm1676 := by decide +kernel

theorem reducedMerge1668Check : reducedMerge1668 = Integer.Sparse.mergeBy masterLess reducedTerm1677 reducedTerm1678 := by decide +kernel

theorem reducedMerge1669Check : reducedMerge1669 = Integer.Sparse.mergeBy masterLess reducedMerge1667 reducedMerge1668 := by decide +kernel

theorem reducedMerge1670Check : reducedMerge1670 = Integer.Sparse.mergeBy masterLess reducedMerge1666 reducedMerge1669 := by decide +kernel

theorem reducedMerge1671Check : reducedMerge1671 = Integer.Sparse.mergeBy masterLess reducedMerge1663 reducedMerge1670 := by decide +kernel

theorem reducedMerge1672Check : reducedMerge1672 = Integer.Sparse.mergeBy masterLess reducedMerge1657 reducedMerge1671 := by decide +kernel

theorem reducedMerge1673Check : reducedMerge1673 = Integer.Sparse.mergeBy masterLess reducedMerge1643 reducedMerge1672 := by decide +kernel

theorem reducedMerge1674Check : reducedMerge1674 = Integer.Sparse.mergeBy masterLess reducedMerge1614 reducedMerge1673 := by decide +kernel

theorem reducedMerge1675Check : reducedMerge1675 = Integer.Sparse.mergeBy masterLess reducedMerge1555 reducedMerge1674 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1559 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1559 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1559 (originalVector B) := by
  rw [reducedTermArithmetic1559, ← sound4158 B hB hF]
  change (5593363103425757184000 : ℝ) * mixedMoment B node4158 node4158Labels =
    (37623398400 : ℝ) * ((148667141760 : ℝ) * mixedMoment B node4158 node4158Labels + 0)
  ring

theorem reducedTermEval1560 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1560 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1560 (originalVector B) := by
  rw [reducedTermArithmetic1560, ← sound4159 B hB hF]
  change (2053490911783944192000 : ℝ) * mixedMoment B node4159 node4159Labels =
    (37623398400 : ℝ) * ((54580154880 : ℝ) * mixedMoment B node4159 node4159Labels + 0)
  ring

theorem reducedTermEval1561 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1561 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1561 (originalVector B) := by
  rw [reducedTermArithmetic1561, ← sound4160 B hB hF]
  change (7912784430110343168000 : ℝ) * mixedMoment B node4160 node4160Labels =
    (37623398400 : ℝ) * ((210315515520 : ℝ) * mixedMoment B node4160 node4160Labels + 0)
  ring

theorem reducedTermEval1562 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1562 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1562 (originalVector B) := by
  rw [reducedTermArithmetic1562, ← sound4161 B hB hF]
  change (14905306338389655552000 : ℝ) * mixedMoment B node4161 node4161Labels =
    (37623398400 : ℝ) * ((396171185280 : ℝ) * mixedMoment B node4161 node4161Labels + 0)
  ring

theorem reducedTermEval1563 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1563 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1563 (originalVector B) := by
  rw [reducedTermArithmetic1563, ← sound4162 B hB hF]
  change (-761589926485032960000 : ℝ) * mixedMoment B node4162 node4162Labels =
    (37623398400 : ℝ) * (((-20242454400 : ℤ) : ℝ) * mixedMoment B node4162 node4162Labels + 0)
  ring

theorem reducedTermEval1564 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1564 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1564 (originalVector B) := by
  rw [reducedTermArithmetic1564, ← sound4163 B hB hF]
  change (368168093238951936000 : ℝ) * mixedMoment B node4163 node4163Labels =
    (37623398400 : ℝ) * ((9785615040 : ℝ) * mixedMoment B node4163 node4163Labels + 0)
  ring

theorem reducedTermEval1565 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1565 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1565 (originalVector B) := by
  rw [reducedTermArithmetic1565, ← sound4169 B hB hF]
  change (-5693122080040550400000 : ℝ) * mixedMoment B node4169 node4169Labels =
    (37623398400 : ℝ) * (((-151318656000 : ℤ) : ℝ) * mixedMoment B node4169 node4169Labels + 0)
  ring

theorem reducedTermEval1566 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1566 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1566 (originalVector B) := by
  rw [reducedTermArithmetic1566, ← sound4173 B hB hF]
  change (5693122080040550400000 : ℝ) * mixedMoment B node4173 node4173Labels =
    (37623398400 : ℝ) * ((151318656000 : ℝ) * mixedMoment B node4173 node4173Labels + 0)
  ring

theorem reducedTermEval1567 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1567 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1567 (originalVector B) := by
  rw [reducedTermArithmetic1567, ← sound4176 B hB hF]
  change (-7248938720166936576000 : ℝ) * mixedMoment B node4176 node4176Labels =
    (37623398400 : ℝ) * (((-192671024640 : ℤ) : ℝ) * mixedMoment B node4176 node4176Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1568 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1568 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1568 (originalVector B) := by
  rw [reducedTermArithmetic1568, ← sound4178 B hB hF]
  change (12502505035448451072000 : ℝ) * mixedMoment B node4178 node4178Labels =
    (37623398400 : ℝ) * ((332306638080 : ℝ) * mixedMoment B node4178 node4178Labels + 0)
  ring

theorem reducedTermEval1569 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1569 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1569 (originalVector B) := by
  rw [reducedTermArithmetic1569, ← sound4179 B hB hF]
  change (3231726734524022784000 : ℝ) * mixedMoment B node4179 node4179Labels =
    (37623398400 : ℝ) * ((85896725760 : ℝ) * mixedMoment B node4179 node4179Labels + 0)
  ring

theorem reducedTermEval1570 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1570 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1570 (originalVector B) := by
  rw [reducedTermArithmetic1570, ← sound4184 B hB hF]
  change (-716116926716706816000 : ℝ) * mixedMoment B node4184 node4184Labels =
    (37623398400 : ℝ) * (((-19033818240 : ℤ) : ℝ) * mixedMoment B node4184 node4184Labels + 0)
  ring

theorem reducedTermEval1571 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1571 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1571 (originalVector B) := by
  rw [reducedTermArithmetic1571, ← sound4188 B hB hF]
  change (12949757789032415232000 : ℝ) * mixedMoment B node4188 node4188Labels =
    (37623398400 : ℝ) * ((344194260480 : ℝ) * mixedMoment B node4188 node4188Labels + 0)
  ring

theorem reducedTermEval1572 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1572 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1572 (originalVector B) := by
  rw [reducedTermArithmetic1572, ← sound4189 B hB hF]
  change (1197078318949072896000 : ℝ) * mixedMoment B node4189 node4189Labels =
    (37623398400 : ℝ) * ((31817389440 : ℝ) * mixedMoment B node4189 node4189Labels + 0)
  ring

theorem reducedTermEval1573 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1573 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1573 (originalVector B) := by
  rw [reducedTermArithmetic1573, ← sound4193 B hB hF]
  change (-97261095987707904000 : ℝ) * mixedMoment B node4193 node4193Labels =
    (37623398400 : ℝ) * (((-2585122560 : ℤ) : ℝ) * mixedMoment B node4193 node4193Labels + 0)
  ring

theorem reducedTermEval1574 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1574 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1574 (originalVector B) := by
  rw [reducedTermArithmetic1574, ← sound4327 B hB hF]
  change (-2940208664430772224000 : ℝ) * mixedMoment B node4327 node4327Labels =
    (37623398400 : ℝ) * (((-78148407360 : ℤ) : ℝ) * mixedMoment B node4327 node4327Labels + 0)
  ring

theorem reducedTermEval1575 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1575 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1575 (originalVector B) := by
  rw [reducedTermArithmetic1575, ← sound4328 B hB hF]
  change (-4362670631726088192000 : ℝ) * mixedMoment B node4328 node4328Labels =
    (37623398400 : ℝ) * (((-115956314880 : ℤ) : ℝ) * mixedMoment B node4328 node4328Labels + 0)
  ring

theorem reducedTermEval1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1576 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1576 (originalVector B) := by
  rw [reducedTermArithmetic1576, ← sound4330 B hB hF]
  change (-2461303460148019200000 : ℝ) * mixedMoment B node4330 node4330Labels =
    (37623398400 : ℝ) * (((-65419488000 : ℤ) : ℝ) * mixedMoment B node4330 node4330Labels + 0)
  ring

theorem reducedTermEval1577 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1577 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1577 (originalVector B) := by
  rw [reducedTermArithmetic1577, ← sound4331 B hB hF]
  change (2418118564976787456000 : ℝ) * mixedMoment B node4331 node4331Labels =
    (37623398400 : ℝ) * ((64271667840 : ℝ) * mixedMoment B node4331 node4331Labels + 0)
  ring

theorem reducedTermEval1578 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1578 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1578 (originalVector B) := by
  rw [reducedTermArithmetic1578, ← sound4332 B hB hF]
  change (11195660614200459264000 : ℝ) * mixedMoment B node4332 node4332Labels =
    (37623398400 : ℝ) * ((297571752960 : ℝ) * mixedMoment B node4332 node4332Labels + 0)
  ring

theorem reducedTermEval1579 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1579 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1579 (originalVector B) := by
  rw [reducedTermArithmetic1579, ← sound4333 B hB hF]
  change (5221252535535009792000 : ℝ) * mixedMoment B node4333 node4333Labels =
    (37623398400 : ℝ) * ((138776738880 : ℝ) * mixedMoment B node4333 node4333Labels + 0)
  ring

theorem reducedTermEval1580 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1580 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1580 (originalVector B) := by
  rw [reducedTermArithmetic1580, ← sound4334 B hB hF]
  change (16817110373118246912000 : ℝ) * mixedMoment B node4334 node4334Labels =
    (37623398400 : ℝ) * ((446985415680 : ℝ) * mixedMoment B node4334 node4334Labels + 0)
  ring

theorem reducedTermEval1581 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1581 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1581 (originalVector B) := by
  rw [reducedTermArithmetic1581, ← sound4335 B hB hF]
  change (14664773306621362176000 : ℝ) * mixedMoment B node4335 node4335Labels =
    (37623398400 : ℝ) * ((389778008640 : ℝ) * mixedMoment B node4335 node4335Labels + 0)
  ring

theorem reducedTermEval1582 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1582 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1582 (originalVector B) := by
  rw [reducedTermArithmetic1582, ← sound4336 B hB hF]
  change (3643443110785056768000 : ℝ) * mixedMoment B node4336 node4336Labels =
    (37623398400 : ℝ) * ((96839819520 : ℝ) * mixedMoment B node4336 node4336Labels + 0)
  ring

theorem reducedTermEval1583 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1583 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1583 (originalVector B) := by
  rw [reducedTermArithmetic1583, ← sound4345 B hB hF]
  change (-4407922008608735232000 : ℝ) * mixedMoment B node4345 node4345Labels =
    (37623398400 : ℝ) * (((-117159060480 : ℤ) : ℝ) * mixedMoment B node4345 node4345Labels + 0)
  ring

theorem reducedTermEval1584 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1584 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1584 (originalVector B) := by
  rw [reducedTermArithmetic1584, ← sound4347 B hB hF]
  change (1765372925391667200000 : ℝ) * mixedMoment B node4347 node4347Labels =
    (37623398400 : ℝ) * ((46922208000 : ℝ) * mixedMoment B node4347 node4347Labels + 0)
  ring

theorem reducedTermEval1585 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1585 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1585 (originalVector B) := by
  rw [reducedTermArithmetic1585, ← sound4353 B hB hF]
  change (3157621618243534848000 : ℝ) * mixedMoment B node4353 node4353Labels =
    (37623398400 : ℝ) * ((83927070720 : ℝ) * mixedMoment B node4353 node4353Labels + 0)
  ring

theorem reducedTermEval1586 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1586 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1586 (originalVector B) := by
  rw [reducedTermArithmetic1586, ← sound4357 B hB hF]
  change (17560644030085201920000 : ℝ) * mixedMoment B node4357 node4357Labels =
    (37623398400 : ℝ) * ((466747948800 : ℝ) * mixedMoment B node4357 node4357Labels + 0)
  ring

theorem reducedTermEval1587 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1587 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1587 (originalVector B) := by
  rw [reducedTermArithmetic1587, ← sound4358 B hB hF]
  change (3552084349459365888000 : ℝ) * mixedMoment B node4358 node4358Labels =
    (37623398400 : ℝ) * ((94411576320 : ℝ) * mixedMoment B node4358 node4358Labels + 0)
  ring

theorem reducedTermEval1588 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1588 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1588 (originalVector B) := by
  rw [reducedTermArithmetic1588, ← sound4362 B hB hF]
  change (-483156672380928000000 : ℝ) * mixedMoment B node4362 node4362Labels =
    (37623398400 : ℝ) * (((-12841920000 : ℤ) : ℝ) * mixedMoment B node4362 node4362Labels + 0)
  ring

theorem reducedTermEval1589 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1589 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1589 (originalVector B) := by
  rw [reducedTermArithmetic1589, ← sound4363 B hB hF]
  change (2200392789160624128000 : ℝ) * mixedMoment B node4363 node4363Labels =
    (37623398400 : ℝ) * ((58484689920 : ℝ) * mixedMoment B node4363 node4363Labels + 0)
  ring

theorem reducedTermEval1590 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1590 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1590 (originalVector B) := by
  rw [reducedTermArithmetic1590, ← sound4364 B hB hF]
  change (8030508152059330560000 : ℝ) * mixedMoment B node4364 node4364Labels =
    (37623398400 : ℝ) * ((213444518400 : ℝ) * mixedMoment B node4364 node4364Labels + 0)
  ring

theorem reducedTermEval1591 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1591 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1591 (originalVector B) := by
  rw [reducedTermArithmetic1591, ← sound4365 B hB hF]
  change (2333580197392023552000 : ℝ) * mixedMoment B node4365 node4365Labels =
    (37623398400 : ℝ) * ((62024705280 : ℝ) * mixedMoment B node4365 node4365Labels + 0)
  ring

theorem reducedTermEval1592 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1592 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1592 (originalVector B) := by
  rw [reducedTermArithmetic1592, ← sound4366 B hB hF]
  change (-19011338932645527552000 : ℝ) * mixedMoment B node4366 node4366Labels =
    (37623398400 : ℝ) * (((-505306265280 : ℤ) : ℝ) * mixedMoment B node4366 node4366Labels + 0)
  ring

theorem reducedTermEval1593 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1593 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1593 (originalVector B) := by
  rw [reducedTermArithmetic1593, ← sound4367 B hB hF]
  change (-6166085797247975424000 : ℝ) * mixedMoment B node4367 node4367Labels =
    (37623398400 : ℝ) * (((-163889655360 : ℤ) : ℝ) * mixedMoment B node4367 node4367Labels + 0)
  ring

theorem reducedTermEval1594 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1594 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1594 (originalVector B) := by
  rw [reducedTermArithmetic1594, ← sound4368 B hB hF]
  change (-19274765724083552256000 : ℝ) * mixedMoment B node4368 node4368Labels =
    (37623398400 : ℝ) * (((-512307939840 : ℤ) : ℝ) * mixedMoment B node4368 node4368Labels + 0)
  ring

theorem reducedTermEval1595 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1595 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1595 (originalVector B) := by
  rw [reducedTermArithmetic1595, ← sound4369 B hB hF]
  change (5544829063963607040000 : ℝ) * mixedMoment B node4369 node4369Labels =
    (37623398400 : ℝ) * ((147377145600 : ℝ) * mixedMoment B node4369 node4369Labels + 0)
  ring

theorem reducedTermEval1596 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1596 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1596 (originalVector B) := by
  rw [reducedTermArithmetic1596, ← sound4370 B hB hF]
  change (6870049258648633344000 : ℝ) * mixedMoment B node4370 node4370Labels =
    (37623398400 : ℝ) * ((182600444160 : ℝ) * mixedMoment B node4370 node4370Labels + 0)
  ring

theorem reducedTermEval1597 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1597 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1597 (originalVector B) := by
  rw [reducedTermArithmetic1597, ← sound4371 B hB hF]
  change (476851978047062016000 : ℝ) * mixedMoment B node4371 node4371Labels =
    (37623398400 : ℝ) * ((12674346240 : ℝ) * mixedMoment B node4371 node4371Labels + 0)
  ring

theorem reducedTermEval1598 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1598 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1598 (originalVector B) := by
  rw [reducedTermArithmetic1598, ← sound4372 B hB hF]
  change (-382460818968281088000 : ℝ) * mixedMoment B node4372 node4372Labels =
    (37623398400 : ℝ) * (((-10165504320 : ℤ) : ℝ) * mixedMoment B node4372 node4372Labels + 0)
  ring

theorem reducedTermEval1599 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1599 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1599 (originalVector B) := by
  rw [reducedTermArithmetic1599, ← sound4373 B hB hF]
  change (9211036774796623872000 : ℝ) * mixedMoment B node4373 node4373Labels =
    (37623398400 : ℝ) * ((244822030080 : ℝ) * mixedMoment B node4373 node4373Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1556 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1556 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1556 (originalVector B) := by
  rw [reducedMerge1556Check, Integer.Sparse.eval_mergeBy, reducedTermEval1560 B hB hF, reducedTermEval1561 B hB hF]
  rw [originalMerge1556, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1557 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1557 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1557 (originalVector B) := by
  rw [reducedMerge1557Check, Integer.Sparse.eval_mergeBy, reducedTermEval1559 B hB hF, reducedMergeEval1556 B hB hF]
  rw [originalMerge1557, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1558 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1558 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1558 (originalVector B) := by
  rw [reducedMerge1558Check, Integer.Sparse.eval_mergeBy, reducedTermEval1562 B hB hF, reducedTermEval1563 B hB hF]
  rw [originalMerge1558, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1559 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1559 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1559 (originalVector B) := by
  rw [reducedMerge1559Check, Integer.Sparse.eval_mergeBy, reducedTermEval1564 B hB hF, reducedTermEval1565 B hB hF]
  rw [originalMerge1559, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1560 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1560 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1560 (originalVector B) := by
  rw [reducedMerge1560Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1558 B hB hF, reducedMergeEval1559 B hB hF]
  rw [originalMerge1560, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1561 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1561 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1561 (originalVector B) := by
  rw [reducedMerge1561Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1557 B hB hF, reducedMergeEval1560 B hB hF]
  rw [originalMerge1561, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1562 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1562 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1562 (originalVector B) := by
  rw [reducedMerge1562Check, Integer.Sparse.eval_mergeBy, reducedTermEval1566 B hB hF, reducedTermEval1567 B hB hF]
  rw [originalMerge1562, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1563 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1563 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1563 (originalVector B) := by
  rw [reducedMerge1563Check, Integer.Sparse.eval_mergeBy, reducedTermEval1568 B hB hF, reducedTermEval1569 B hB hF]
  rw [originalMerge1563, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1564 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1564 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1564 (originalVector B) := by
  rw [reducedMerge1564Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1562 B hB hF, reducedMergeEval1563 B hB hF]
  rw [originalMerge1564, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1565 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1565 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1565 (originalVector B) := by
  rw [reducedMerge1565Check, Integer.Sparse.eval_mergeBy, reducedTermEval1570 B hB hF, reducedTermEval1571 B hB hF]
  rw [originalMerge1565, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1566 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1566 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1566 (originalVector B) := by
  rw [reducedMerge1566Check, Integer.Sparse.eval_mergeBy, reducedTermEval1572 B hB hF, reducedTermEval1573 B hB hF]
  rw [originalMerge1566, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1567 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1567 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1567 (originalVector B) := by
  rw [reducedMerge1567Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1565 B hB hF, reducedMergeEval1566 B hB hF]
  rw [originalMerge1567, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1600 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1600 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1600 (originalVector B) := by
  rw [reducedTermArithmetic1600, ← sound4374 B hB hF]
  change (17575348253457383424000 : ℝ) * mixedMoment B node4374 node4374Labels =
    (37623398400 : ℝ) * ((467138775360 : ℝ) * mixedMoment B node4374 node4374Labels + 0)
  ring

theorem reducedTermEval1601 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1601 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1601 (originalVector B) := by
  rw [reducedTermArithmetic1601, ← sound4375 B hB hF]
  change (-34507362327330816000 : ℝ) * mixedMoment B node4375 node4375Labels =
    (37623398400 : ℝ) * (((-917178240 : ℤ) : ℝ) * mixedMoment B node4375 node4375Labels + 0)
  ring

theorem reducedTermEval1602 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1602 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1602 (originalVector B) := by
  rw [reducedTermArithmetic1602, ← sound4439 B hB hF]
  change (-13515513231445327872000 : ℝ) * mixedMoment B node4439 node4439Labels =
    (37623398400 : ℝ) * (((-359231590080 : ℤ) : ℝ) * mixedMoment B node4439 node4439Labels + 0)
  ring

theorem reducedTermEval1603 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1603 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1603 (originalVector B) := by
  rw [reducedTermArithmetic1603, ← sound4440 B hB hF]
  change (-19241651017431908352000 : ℝ) * mixedMoment B node4440 node4440Labels =
    (37623398400 : ℝ) * (((-511427777280 : ℤ) : ℝ) * mixedMoment B node4440 node4440Labels + 0)
  ring

theorem reducedTermEval1604 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1604 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1604 (originalVector B) := by
  rw [reducedTermArithmetic1604, ← sound4442 B hB hF]
  change (-2216492015908552704000 : ℝ) * mixedMoment B node4442 node4442Labels =
    (37623398400 : ℝ) * (((-58912594560 : ℤ) : ℝ) * mixedMoment B node4442 node4442Labels + 0)
  ring

theorem reducedTermEval1605 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1605 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1605 (originalVector B) := by
  rw [reducedTermArithmetic1605, ← sound4444 B hB hF]
  change (9836938992486187008000 : ℝ) * mixedMoment B node4444 node4444Labels =
    (37623398400 : ℝ) * ((261458013120 : ℝ) * mixedMoment B node4444 node4444Labels + 0)
  ring

theorem reducedTermEval1606 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1606 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1606 (originalVector B) := by
  rw [reducedTermArithmetic1606, ← sound4445 B hB hF]
  change (-2888188832156221440000 : ℝ) * mixedMoment B node4445 node4445Labels =
    (37623398400 : ℝ) * (((-76765761600 : ℤ) : ℝ) * mixedMoment B node4445 node4445Labels + 0)
  ring

theorem reducedTermEval1607 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1607 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1607 (originalVector B) := by
  rw [reducedTermArithmetic1607, ← sound4459 B hB hF]
  change (-24911231228112273408000 : ℝ) * mixedMoment B node4459 node4459Labels =
    (37623398400 : ℝ) * (((-662120709120 : ℤ) : ℝ) * mixedMoment B node4459 node4459Labels + 0)
  ring

theorem reducedTermEval1608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1608 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1608 (originalVector B) := by
  rw [reducedTermArithmetic1608, ← sound4464 B hB hF]
  change (-11076753145762676736000 : ℝ) * mixedMoment B node4464 node4464Labels =
    (37623398400 : ℝ) * (((-294411287040 : ℤ) : ℝ) * mixedMoment B node4464 node4464Labels + 0)
  ring

theorem reducedTermEval1609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1609 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1609 (originalVector B) := by
  rw [reducedTermArithmetic1609, ← sound4473 B hB hF]
  change (-3609473985785364480000 : ℝ) * mixedMoment B node4473 node4473Labels =
    (37623398400 : ℝ) * (((-95936947200 : ℤ) : ℝ) * mixedMoment B node4473 node4473Labels + 0)
  ring

theorem reducedTermEval1610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1610 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1610 (originalVector B) := by
  rw [reducedTermArithmetic1610, ← sound4474 B hB hF]
  change (-8041495388340879360000 : ℝ) * mixedMoment B node4474 node4474Labels =
    (37623398400 : ℝ) * (((-213736550400 : ℤ) : ℝ) * mixedMoment B node4474 node4474Labels + 0)
  ring

theorem reducedTermEval1611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1611 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1611 (originalVector B) := by
  rw [reducedTermArithmetic1611, ← sound4475 B hB hF]
  change (-8553475027189628928000 : ℝ) * mixedMoment B node4475 node4475Labels =
    (37623398400 : ℝ) * (((-227344561920 : ℤ) : ℝ) * mixedMoment B node4475 node4475Labels + 0)
  ring

theorem reducedTermEval1612 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1612 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1612 (originalVector B) := by
  rw [reducedTermArithmetic1612, ← sound4476 B hB hF]
  change (15007094450225676288000 : ℝ) * mixedMoment B node4476 node4476Labels =
    (37623398400 : ℝ) * ((398876632320 : ℝ) * mixedMoment B node4476 node4476Labels + 0)
  ring

theorem reducedTermEval1613 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1613 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1613 (originalVector B) := by
  rw [reducedTermArithmetic1613, ← sound4478 B hB hF]
  change (-14254645456457957376000 : ℝ) * mixedMoment B node4478 node4478Labels =
    (37623398400 : ℝ) * (((-378877136640 : ℤ) : ℝ) * mixedMoment B node4478 node4478Labels + 0)
  ring

theorem reducedTermEval1614 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1614 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1614 (originalVector B) := by
  rw [reducedTermArithmetic1614, ← sound4480 B hB hF]
  change (18099022219727339520000 : ℝ) * mixedMoment B node4480 node4480Labels =
    (37623398400 : ℝ) * ((481057612800 : ℝ) * mixedMoment B node4480 node4480Labels + 0)
  ring

theorem reducedTermEval1615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1615 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1615 (originalVector B) := by
  rw [reducedTermArithmetic1615, ← sound4481 B hB hF]
  change (-1896689902925905920000 : ℝ) * mixedMoment B node4481 node4481Labels =
    (37623398400 : ℝ) * (((-50412508800 : ℤ) : ℝ) * mixedMoment B node4481 node4481Labels + 0)
  ring

theorem reducedTermEval1616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1616 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1616 (originalVector B) := by
  rw [reducedTermArithmetic1616, ← sound4494 B hB hF]
  change (-4276208522593566720000 : ℝ) * mixedMoment B node4494 node4494Labels =
    (37623398400 : ℝ) * (((-113658220800 : ℤ) : ℝ) * mixedMoment B node4494 node4494Labels + 0)
  ring

theorem reducedTermEval1617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1617 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1617 (originalVector B) := by
  rw [reducedTermArithmetic1617, ← sound4500 B hB hF]
  change (7704059375140208640000 : ℝ) * mixedMoment B node4500 node4500Labels =
    (37623398400 : ℝ) * ((204767769600 : ℝ) * mixedMoment B node4500 node4500Labels + 0)
  ring

theorem reducedTermEval1618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1618 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1618 (originalVector B) := by
  rw [reducedTermArithmetic1618, ← sound4508 B hB hF]
  change (-4470330666478731264000 : ℝ) * mixedMoment B node4508 node4508Labels =
    (37623398400 : ℝ) * (((-118817832960 : ℤ) : ℝ) * mixedMoment B node4508 node4508Labels + 0)
  ring

theorem reducedTermEval1619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1619 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1619 (originalVector B) := by
  rw [reducedTermArithmetic1619, ← sound4527 B hB hF]
  change (5324013064735948800000 : ℝ) * mixedMoment B node4527 node4527Labels =
    (37623398400 : ℝ) * ((141508032000 : ℝ) * mixedMoment B node4527 node4527Labels + 0)
  ring

theorem reducedTermEval1620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1620 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1620 (originalVector B) := by
  rw [reducedTermArithmetic1620, ← sound4528 B hB hF]
  change (4730383620298506240000 : ℝ) * mixedMoment B node4528 node4528Labels =
    (37623398400 : ℝ) * ((125729833600 : ℝ) * mixedMoment B node4528 node4528Labels + 0)
  ring

theorem reducedTermEval1621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1621 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1621 (originalVector B) := by
  rw [reducedTermArithmetic1621, ← sound4529 B hB hF]
  change (-6127988909884047360000 : ℝ) * mixedMoment B node4529 node4529Labels =
    (37623398400 : ℝ) * (((-162877070400 : ℤ) : ℝ) * mixedMoment B node4529 node4529Labels + 0)
  ring

theorem reducedTermEval1622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1622 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1622 (originalVector B) := by
  rw [reducedTermArithmetic1622, ← sound4530 B hB hF]
  change (1083441906686361600000 : ℝ) * mixedMoment B node4530 node4530Labels =
    (37623398400 : ℝ) * ((28797024000 : ℝ) * mixedMoment B node4530 node4530Labels + 0)
  ring

theorem reducedTermEval1623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1623 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1623 (originalVector B) := by
  rw [reducedTermArithmetic1623, ← sound4531 B hB hF]
  change (7918345276749250560000 : ℝ) * mixedMoment B node4531 node4531Labels =
    (37623398400 : ℝ) * ((210463318400 : ℝ) * mixedMoment B node4531 node4531Labels + 0)
  ring

theorem reducedTermEval1624 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1624 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1624 (originalVector B) := by
  rw [reducedTermArithmetic1624, ← sound4532 B hB hF]
  change (-4345332613952569344000 : ℝ) * mixedMoment B node4532 node4532Labels =
    (37623398400 : ℝ) * (((-115495484160 : ℤ) : ℝ) * mixedMoment B node4532 node4532Labels + 0)
  ring

theorem reducedTermEval1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1625 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1625 (originalVector B) := by
  rw [reducedTermArithmetic1625, ← sound4533 B hB hF]
  change (215658764367298560000 : ℝ) * mixedMoment B node4533 node4533Labels =
    (37623398400 : ℝ) * ((5732038400 : ℝ) * mixedMoment B node4533 node4533Labels + 0)
  ring

theorem reducedTermEval1626 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1626 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1626 (originalVector B) := by
  rw [reducedTermArithmetic1626, ← sound4534 B hB hF]
  change (-8819748555444191232000 : ℝ) * mixedMoment B node4534 node4534Labels =
    (37623398400 : ℝ) * (((-234421900480 : ℤ) : ℝ) * mixedMoment B node4534 node4534Labels + 0)
  ring

theorem reducedTermEval1627 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1627 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1627 (originalVector B) := by
  rw [reducedTermArithmetic1627, ← sound4535 B hB hF]
  change (-3968589383710801920000 : ℝ) * mixedMoment B node4535 node4535Labels =
    (37623398400 : ℝ) * (((-105481948800 : ℤ) : ℝ) * mixedMoment B node4535 node4535Labels + 0)
  ring

theorem reducedTermEval1628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1628 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1628 (originalVector B) := by
  rw [reducedTermArithmetic1628, ← sound4536 B hB hF]
  change (-14113916079842525184000 : ℝ) * mixedMoment B node4536 node4536Labels =
    (37623398400 : ℝ) * (((-375136661760 : ℤ) : ℝ) * mixedMoment B node4536 node4536Labels + 0)
  ring

theorem reducedTermEval1629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1629 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1629 (originalVector B) := by
  rw [reducedTermArithmetic1629, ← sound4540 B hB hF]
  change (8499226830254899200000 : ℝ) * mixedMoment B node4540 node4540Labels =
    (37623398400 : ℝ) * ((225902688000 : ℝ) * mixedMoment B node4540 node4540Labels + 0)
  ring

theorem reducedTermEval1630 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1630 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1630 (originalVector B) := by
  rw [reducedTermArithmetic1630, ← sound4542 B hB hF]
  change (23732159479676928000000 : ℝ) * mixedMoment B node4542 node4542Labels =
    (37623398400 : ℝ) * ((630781920000 : ℝ) * mixedMoment B node4542 node4542Labels + 0)
  ring

theorem reducedTermEval1631 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1631 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1631 (originalVector B) := by
  rw [reducedTermArithmetic1631, ← sound4545 B hB hF]
  change (36626429413905924096000 : ℝ) * mixedMoment B node4545 node4545Labels =
    (37623398400 : ℝ) * ((973501357440 : ℝ) * mixedMoment B node4545 node4545Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1568 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1568 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1568 (originalVector B) := by
  rw [reducedMerge1568Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1564 B hB hF, reducedMergeEval1567 B hB hF]
  rw [originalMerge1568, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1569 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1569 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1569 (originalVector B) := by
  rw [reducedMerge1569Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1561 B hB hF, reducedMergeEval1568 B hB hF]
  rw [originalMerge1569, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1570 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1570 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1570 (originalVector B) := by
  rw [reducedMerge1570Check, Integer.Sparse.eval_mergeBy, reducedTermEval1575 B hB hF, reducedTermEval1576 B hB hF]
  rw [originalMerge1570, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1571 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1571 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1571 (originalVector B) := by
  rw [reducedMerge1571Check, Integer.Sparse.eval_mergeBy, reducedTermEval1574 B hB hF, reducedMergeEval1570 B hB hF]
  rw [originalMerge1571, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1572 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1572 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1572 (originalVector B) := by
  rw [reducedMerge1572Check, Integer.Sparse.eval_mergeBy, reducedTermEval1577 B hB hF, reducedTermEval1578 B hB hF]
  rw [originalMerge1572, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1573 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1573 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1573 (originalVector B) := by
  rw [reducedMerge1573Check, Integer.Sparse.eval_mergeBy, reducedTermEval1579 B hB hF, reducedTermEval1580 B hB hF]
  rw [originalMerge1573, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1574 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1574 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1574 (originalVector B) := by
  rw [reducedMerge1574Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1572 B hB hF, reducedMergeEval1573 B hB hF]
  rw [originalMerge1574, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1575 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1575 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1575 (originalVector B) := by
  rw [reducedMerge1575Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1571 B hB hF, reducedMergeEval1574 B hB hF]
  rw [originalMerge1575, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1576 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1576 (originalVector B) := by
  rw [reducedMerge1576Check, Integer.Sparse.eval_mergeBy, reducedTermEval1581 B hB hF, reducedTermEval1582 B hB hF]
  rw [originalMerge1576, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1577 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1577 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1577 (originalVector B) := by
  rw [reducedMerge1577Check, Integer.Sparse.eval_mergeBy, reducedTermEval1583 B hB hF, reducedTermEval1584 B hB hF]
  rw [originalMerge1577, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1578 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1578 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1578 (originalVector B) := by
  rw [reducedMerge1578Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1576 B hB hF, reducedMergeEval1577 B hB hF]
  rw [originalMerge1578, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1579 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1579 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1579 (originalVector B) := by
  rw [reducedMerge1579Check, Integer.Sparse.eval_mergeBy, reducedTermEval1585 B hB hF, reducedTermEval1586 B hB hF]
  rw [originalMerge1579, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1580 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1580 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1580 (originalVector B) := by
  rw [reducedMerge1580Check, Integer.Sparse.eval_mergeBy, reducedTermEval1587 B hB hF, reducedTermEval1588 B hB hF]
  rw [originalMerge1580, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1581 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1581 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1581 (originalVector B) := by
  rw [reducedMerge1581Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1579 B hB hF, reducedMergeEval1580 B hB hF]
  rw [originalMerge1581, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1582 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1582 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1582 (originalVector B) := by
  rw [reducedMerge1582Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1578 B hB hF, reducedMergeEval1581 B hB hF]
  rw [originalMerge1582, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1583 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1583 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1583 (originalVector B) := by
  rw [reducedMerge1583Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1575 B hB hF, reducedMergeEval1582 B hB hF]
  rw [originalMerge1583, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1584 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1584 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1584 (originalVector B) := by
  rw [reducedMerge1584Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1569 B hB hF, reducedMergeEval1583 B hB hF]
  rw [originalMerge1584, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1585 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1585 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1585 (originalVector B) := by
  rw [reducedMerge1585Check, Integer.Sparse.eval_mergeBy, reducedTermEval1590 B hB hF, reducedTermEval1591 B hB hF]
  rw [originalMerge1585, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1586 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1586 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1586 (originalVector B) := by
  rw [reducedMerge1586Check, Integer.Sparse.eval_mergeBy, reducedTermEval1589 B hB hF, reducedMergeEval1585 B hB hF]
  rw [originalMerge1586, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1587 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1587 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1587 (originalVector B) := by
  rw [reducedMerge1587Check, Integer.Sparse.eval_mergeBy, reducedTermEval1592 B hB hF, reducedTermEval1593 B hB hF]
  rw [originalMerge1587, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1588 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1588 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1588 (originalVector B) := by
  rw [reducedMerge1588Check, Integer.Sparse.eval_mergeBy, reducedTermEval1594 B hB hF, reducedTermEval1595 B hB hF]
  rw [originalMerge1588, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1589 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1589 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1589 (originalVector B) := by
  rw [reducedMerge1589Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1587 B hB hF, reducedMergeEval1588 B hB hF]
  rw [originalMerge1589, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1590 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1590 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1590 (originalVector B) := by
  rw [reducedMerge1590Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1586 B hB hF, reducedMergeEval1589 B hB hF]
  rw [originalMerge1590, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1591 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1591 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1591 (originalVector B) := by
  rw [reducedMerge1591Check, Integer.Sparse.eval_mergeBy, reducedTermEval1596 B hB hF, reducedTermEval1597 B hB hF]
  rw [originalMerge1591, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1592 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1592 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1592 (originalVector B) := by
  rw [reducedMerge1592Check, Integer.Sparse.eval_mergeBy, reducedTermEval1598 B hB hF, reducedTermEval1599 B hB hF]
  rw [originalMerge1592, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1593 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1593 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1593 (originalVector B) := by
  rw [reducedMerge1593Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1591 B hB hF, reducedMergeEval1592 B hB hF]
  rw [originalMerge1593, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1594 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1594 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1594 (originalVector B) := by
  rw [reducedMerge1594Check, Integer.Sparse.eval_mergeBy, reducedTermEval1600 B hB hF, reducedTermEval1601 B hB hF]
  rw [originalMerge1594, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1595 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1595 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1595 (originalVector B) := by
  rw [reducedMerge1595Check, Integer.Sparse.eval_mergeBy, reducedTermEval1602 B hB hF, reducedTermEval1603 B hB hF]
  rw [originalMerge1595, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1596 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1596 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1596 (originalVector B) := by
  rw [reducedMerge1596Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1594 B hB hF, reducedMergeEval1595 B hB hF]
  rw [originalMerge1596, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1597 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1597 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1597 (originalVector B) := by
  rw [reducedMerge1597Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1593 B hB hF, reducedMergeEval1596 B hB hF]
  rw [originalMerge1597, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1598 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1598 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1598 (originalVector B) := by
  rw [reducedMerge1598Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1590 B hB hF, reducedMergeEval1597 B hB hF]
  rw [originalMerge1598, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1599 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1599 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1599 (originalVector B) := by
  rw [reducedMerge1599Check, Integer.Sparse.eval_mergeBy, reducedTermEval1605 B hB hF, reducedTermEval1606 B hB hF]
  rw [originalMerge1599, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1632 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1632 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1632 (originalVector B) := by
  rw [reducedTermArithmetic1632, ← sound4547 B hB hF]
  change (15452458461052010496000 : ℝ) * mixedMoment B node4547 node4547Labels =
    (37623398400 : ℝ) * ((410714053440 : ℝ) * mixedMoment B node4547 node4547Labels + 0)
  ring

theorem reducedTermEval1633 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1633 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1633 (originalVector B) := by
  rw [reducedTermArithmetic1633, ← sound4548 B hB hF]
  change (14639794103047421952000 : ℝ) * mixedMoment B node4548 node4548Labels =
    (37623398400 : ℝ) * ((389114081280 : ℝ) * mixedMoment B node4548 node4548Labels + 0)
  ring

theorem reducedTermEval1634 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1634 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1634 (originalVector B) := by
  rw [reducedTermArithmetic1634, ← sound4552 B hB hF]
  change (-11692002548014645248000 : ℝ) * mixedMoment B node4552 node4552Labels =
    (37623398400 : ℝ) * (((-310764126720 : ℤ) : ℝ) * mixedMoment B node4552 node4552Labels + 0)
  ring

theorem reducedTermEval1635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1635 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1635 (originalVector B) := by
  rw [reducedTermArithmetic1635, ← sound4556 B hB hF]
  change (-8265191798831579136000 : ℝ) * mixedMoment B node4556 node4556Labels =
    (37623398400 : ℝ) * (((-219682223040 : ℤ) : ℝ) * mixedMoment B node4556 node4556Labels + 0)
  ring

theorem reducedTermEval1636 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1636 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1636 (originalVector B) := by
  rw [reducedTermArithmetic1636, ← sound4560 B hB hF]
  change (-1142729568214843392000 : ℝ) * mixedMoment B node4560 node4560Labels =
    (37623398400 : ℝ) * (((-30372842880 : ℤ) : ℝ) * mixedMoment B node4560 node4560Labels + 0)
  ring

theorem reducedTermEval1637 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1637 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1637 (originalVector B) := by
  rw [reducedTermArithmetic1637, ← sound4589 B hB hF]
  change (1220339788645662720000 : ℝ) * mixedMoment B node4589 node4589Labels =
    (37623398400 : ℝ) * ((32435660800 : ℝ) * mixedMoment B node4589 node4589Labels + 0)
  ring

theorem reducedTermEval1638 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1638 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1638 (originalVector B) := by
  rw [reducedTermArithmetic1638, ← sound4590 B hB hF]
  change (6476173958106316800000 : ℝ) * mixedMoment B node4590 node4590Labels =
    (37623398400 : ℝ) * ((172131552000 : ℝ) * mixedMoment B node4590 node4590Labels + 0)
  ring

theorem reducedTermEval1639 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1639 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1639 (originalVector B) := by
  rw [reducedTermArithmetic1639, ← sound4591 B hB hF]
  change (-6085807301323653120000 : ℝ) * mixedMoment B node4591 node4591Labels =
    (37623398400 : ℝ) * (((-161755916800 : ℤ) : ℝ) * mixedMoment B node4591 node4591Labels + 0)
  ring

theorem reducedTermEval1640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1640 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1640 (originalVector B) := by
  rw [reducedTermArithmetic1640, ← sound4592 B hB hF]
  change (-15157581060922933248000 : ℝ) * mixedMoment B node4592 node4592Labels =
    (37623398400 : ℝ) * (((-402876446720 : ℤ) : ℝ) * mixedMoment B node4592 node4592Labels + 0)
  ring

theorem reducedTermEval1641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1641 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1641 (originalVector B) := by
  rw [reducedTermArithmetic1641, ← sound4593 B hB hF]
  change (-7559615864792678400000 : ℝ) * mixedMoment B node4593 node4593Labels =
    (37623398400 : ℝ) * (((-200928576000 : ℤ) : ℝ) * mixedMoment B node4593 node4593Labels + 0)
  ring

theorem reducedTermEval1642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1642 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1642 (originalVector B) := by
  rw [reducedTermArithmetic1642, ← sound4594 B hB hF]
  change (3011436319122653184000 : ℝ) * mixedMoment B node4594 node4594Labels =
    (37623398400 : ℝ) * ((80041581760 : ℝ) * mixedMoment B node4594 node4594Labels + 0)
  ring

theorem reducedTermEval1643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1643 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1643 (originalVector B) := by
  rw [reducedTermArithmetic1643, ← sound4599 B hB hF]
  change (10617849996847349760000 : ℝ) * mixedMoment B node4599 node4599Labels =
    (37623398400 : ℝ) * ((282214006400 : ℝ) * mixedMoment B node4599 node4599Labels + 0)
  ring

theorem reducedTermEval1644 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1644 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1644 (originalVector B) := by
  rw [reducedTermArithmetic1644, ← sound4600 B hB hF]
  change (-1692590756154310656000 : ℝ) * mixedMoment B node4600 node4600Labels =
    (37623398400 : ℝ) * (((-44987715840 : ℤ) : ℝ) * mixedMoment B node4600 node4600Labels + 0)
  ring

theorem reducedTermEval1645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1645 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1645 (originalVector B) := by
  rw [reducedTermArithmetic1645, ← sound4603 B hB hF]
  change (-35786008029537239040000 : ℝ) * mixedMoment B node4603 node4603Labels =
    (37623398400 : ℝ) * (((-951163625600 : ℤ) : ℝ) * mixedMoment B node4603 node4603Labels + 0)
  ring

theorem reducedTermEval1646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1646 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1646 (originalVector B) := by
  rw [reducedTermArithmetic1646, ← sound4607 B hB hF]
  change (-38147155763799785472000 : ℝ) * mixedMoment B node4607 node4607Labels =
    (37623398400 : ℝ) * (((-1013921054080 : ℤ) : ℝ) * mixedMoment B node4607 node4607Labels + 0)
  ring

theorem reducedTermEval1647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1647 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1647 (originalVector B) := by
  rw [reducedTermArithmetic1647, ← sound4609 B hB hF]
  change (-5558333516289146880000 : ℝ) * mixedMoment B node4609 node4609Labels =
    (37623398400 : ℝ) * (((-147736083200 : ℤ) : ℝ) * mixedMoment B node4609 node4609Labels + 0)
  ring

theorem reducedTermEval1648 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1648 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1648 (originalVector B) := by
  rw [reducedTermArithmetic1648, ← sound4611 B hB hF]
  change (-10846457928298266624000 : ℝ) * mixedMoment B node4611 node4611Labels =
    (37623398400 : ℝ) * (((-288290223360 : ℤ) : ℝ) * mixedMoment B node4611 node4611Labels + 0)
  ring

theorem reducedTermEval1649 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1649 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1649 (originalVector B) := by
  rw [reducedTermArithmetic1649, ← sound4616 B hB hF]
  change (-2261821083603959808000 : ℝ) * mixedMoment B node4616 node4616Labels =
    (37623398400 : ℝ) * (((-60117405120 : ℤ) : ℝ) * mixedMoment B node4616 node4616Labels + 0)
  ring

theorem reducedTermEval1650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1650 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1650 (originalVector B) := by
  rw [reducedTermArithmetic1650, ← sound4617 B hB hF]
  change (-757540324473569280000 : ℝ) * mixedMoment B node4617 node4617Labels =
    (37623398400 : ℝ) * (((-20134819200 : ℤ) : ℝ) * mixedMoment B node4617 node4617Labels + 0)
  ring

theorem reducedTermEval1651 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1651 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1651 (originalVector B) := by
  rw [reducedTermArithmetic1651, ← sound4620 B hB hF]
  change (-747979948051660800000 : ℝ) * mixedMoment B node4620 node4620Labels =
    (37623398400 : ℝ) * (((-19880712000 : ℤ) : ℝ) * mixedMoment B node4620 node4620Labels + 0)
  ring

theorem reducedTermEval1652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1652 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1652 (originalVector B) := by
  rw [reducedTermArithmetic1652, ← sound4626 B hB hF]
  change (-875893157801754624000 : ℝ) * mixedMoment B node4626 node4626Labels =
    (37623398400 : ℝ) * (((-23280543360 : ℤ) : ℝ) * mixedMoment B node4626 node4626Labels + 0)
  ring

theorem reducedTermEval1653 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1653 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1653 (originalVector B) := by
  rw [reducedTermArithmetic1653, ← sound4663 B hB hF]
  change (-4224921028263936000000 : ℝ) * mixedMoment B node4663 node4663Labels =
    (37623398400 : ℝ) * (((-112295040000 : ℤ) : ℝ) * mixedMoment B node4663 node4663Labels + 0)
  ring

theorem reducedTermEval1654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1654 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1654 (originalVector B) := by
  rw [reducedTermArithmetic1654, ← sound4664 B hB hF]
  change (-5601048967764246528000 : ℝ) * mixedMoment B node4664 node4664Labels =
    (37623398400 : ℝ) * (((-148871425920 : ℤ) : ℝ) * mixedMoment B node4664 node4664Labels + 0)
  ring

theorem reducedTermEval1655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1655 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1655 (originalVector B) := by
  rw [reducedTermArithmetic1655, ← sound4665 B hB hF]
  change (4938879732374568960000 : ℝ) * mixedMoment B node4665 node4665Labels =
    (37623398400 : ℝ) * ((131271494400 : ℝ) * mixedMoment B node4665 node4665Labels + 0)
  ring

theorem reducedTermEval1656 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1656 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1656 (originalVector B) := by
  rw [reducedTermArithmetic1656, ← sound4666 B hB hF]
  change (-7805365883397734400000 : ℝ) * mixedMoment B node4666 node4666Labels =
    (37623398400 : ℝ) * (((-207460416000 : ℤ) : ℝ) * mixedMoment B node4666 node4666Labels + 0)
  ring

theorem reducedTermEval1657 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1657 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1657 (originalVector B) := by
  rw [reducedTermArithmetic1657, ← sound4667 B hB hF]
  change (1400988782872756224000 : ℝ) * mixedMoment B node4667 node4667Labels =
    (37623398400 : ℝ) * ((37237167360 : ℝ) * mixedMoment B node4667 node4667Labels + 0)
  ring

theorem reducedTermEval1658 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1658 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1658 (originalVector B) := by
  rw [reducedTermArithmetic1658, ← sound4668 B hB hF]
  change (1662907014489047040000 : ℝ) * mixedMoment B node4668 node4668Labels =
    (37623398400 : ℝ) * ((44198745600 : ℝ) * mixedMoment B node4668 node4668Labels + 0)
  ring

theorem reducedTermEval1659 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1659 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1659 (originalVector B) := by
  rw [reducedTermArithmetic1659, ← sound4669 B hB hF]
  change (-799209977907511296000 : ℝ) * mixedMoment B node4669 node4669Labels =
    (37623398400 : ℝ) * (((-21242365440 : ℤ) : ℝ) * mixedMoment B node4669 node4669Labels + 0)
  ring

theorem reducedTermEval1660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1660 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1660 (originalVector B) := by
  rw [reducedTermArithmetic1660, ← sound4670 B hB hF]
  change (-16331923481962217472000 : ℝ) * mixedMoment B node4670 node4670Labels =
    (37623398400 : ℝ) * (((-434089534080 : ℤ) : ℝ) * mixedMoment B node4670 node4670Labels + 0)
  ring

theorem reducedTermEval1661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1661 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1661 (originalVector B) := by
  rw [reducedTermArithmetic1661, ← sound4671 B hB hF]
  change (1843237901377732608000 : ℝ) * mixedMoment B node4671 node4671Labels =
    (37623398400 : ℝ) * ((48991797120 : ℝ) * mixedMoment B node4671 node4671Labels + 0)
  ring

theorem reducedTermEval1662 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1662 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1662 (originalVector B) := by
  rw [reducedTermArithmetic1662, ← sound4677 B hB hF]
  change (-5693122080040550400000 : ℝ) * mixedMoment B node4677 node4677Labels =
    (37623398400 : ℝ) * (((-151318656000 : ℤ) : ℝ) * mixedMoment B node4677 node4677Labels + 0)
  ring

theorem reducedTermEval1663 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1663 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1663 (originalVector B) := by
  rw [reducedTermArithmetic1663, ← sound4680 B hB hF]
  change (2989735781018370048000 : ℝ) * mixedMoment B node4680 node4680Labels =
    (37623398400 : ℝ) * ((79464798720 : ℝ) * mixedMoment B node4680 node4680Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1600 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1600 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1600 (originalVector B) := by
  rw [reducedMerge1600Check, Integer.Sparse.eval_mergeBy, reducedTermEval1604 B hB hF, reducedMergeEval1599 B hB hF]
  rw [originalMerge1600, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1601 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1601 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1601 (originalVector B) := by
  rw [reducedMerge1601Check, Integer.Sparse.eval_mergeBy, reducedTermEval1607 B hB hF, reducedTermEval1608 B hB hF]
  rw [originalMerge1601, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1602 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1602 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1602 (originalVector B) := by
  rw [reducedMerge1602Check, Integer.Sparse.eval_mergeBy, reducedTermEval1609 B hB hF, reducedTermEval1610 B hB hF]
  rw [originalMerge1602, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1603 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1603 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1603 (originalVector B) := by
  rw [reducedMerge1603Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1601 B hB hF, reducedMergeEval1602 B hB hF]
  rw [originalMerge1603, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1604 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1604 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1604 (originalVector B) := by
  rw [reducedMerge1604Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1600 B hB hF, reducedMergeEval1603 B hB hF]
  rw [originalMerge1604, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1605 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1605 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1605 (originalVector B) := by
  rw [reducedMerge1605Check, Integer.Sparse.eval_mergeBy, reducedTermEval1611 B hB hF, reducedTermEval1612 B hB hF]
  rw [originalMerge1605, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1606 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1606 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1606 (originalVector B) := by
  rw [reducedMerge1606Check, Integer.Sparse.eval_mergeBy, reducedTermEval1613 B hB hF, reducedTermEval1614 B hB hF]
  rw [originalMerge1606, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1607 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1607 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1607 (originalVector B) := by
  rw [reducedMerge1607Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1605 B hB hF, reducedMergeEval1606 B hB hF]
  rw [originalMerge1607, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1608 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1608 (originalVector B) := by
  rw [reducedMerge1608Check, Integer.Sparse.eval_mergeBy, reducedTermEval1615 B hB hF, reducedTermEval1616 B hB hF]
  rw [originalMerge1608, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1609 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1609 (originalVector B) := by
  rw [reducedMerge1609Check, Integer.Sparse.eval_mergeBy, reducedTermEval1617 B hB hF, reducedTermEval1618 B hB hF]
  rw [originalMerge1609, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1610 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1610 (originalVector B) := by
  rw [reducedMerge1610Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1608 B hB hF, reducedMergeEval1609 B hB hF]
  rw [originalMerge1610, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1611 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1611 (originalVector B) := by
  rw [reducedMerge1611Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1607 B hB hF, reducedMergeEval1610 B hB hF]
  rw [originalMerge1611, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1612 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1612 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1612 (originalVector B) := by
  rw [reducedMerge1612Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1604 B hB hF, reducedMergeEval1611 B hB hF]
  rw [originalMerge1612, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1613 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1613 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1613 (originalVector B) := by
  rw [reducedMerge1613Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1598 B hB hF, reducedMergeEval1612 B hB hF]
  rw [originalMerge1613, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1614 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1614 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1614 (originalVector B) := by
  rw [reducedMerge1614Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1584 B hB hF, reducedMergeEval1613 B hB hF]
  rw [originalMerge1614, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1615 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1615 (originalVector B) := by
  rw [reducedMerge1615Check, Integer.Sparse.eval_mergeBy, reducedTermEval1620 B hB hF, reducedTermEval1621 B hB hF]
  rw [originalMerge1615, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1616 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1616 (originalVector B) := by
  rw [reducedMerge1616Check, Integer.Sparse.eval_mergeBy, reducedTermEval1619 B hB hF, reducedMergeEval1615 B hB hF]
  rw [originalMerge1616, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1617 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1617 (originalVector B) := by
  rw [reducedMerge1617Check, Integer.Sparse.eval_mergeBy, reducedTermEval1622 B hB hF, reducedTermEval1623 B hB hF]
  rw [originalMerge1617, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1618 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1618 (originalVector B) := by
  rw [reducedMerge1618Check, Integer.Sparse.eval_mergeBy, reducedTermEval1624 B hB hF, reducedTermEval1625 B hB hF]
  rw [originalMerge1618, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1619 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1619 (originalVector B) := by
  rw [reducedMerge1619Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1617 B hB hF, reducedMergeEval1618 B hB hF]
  rw [originalMerge1619, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1620 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1620 (originalVector B) := by
  rw [reducedMerge1620Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1616 B hB hF, reducedMergeEval1619 B hB hF]
  rw [originalMerge1620, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1621 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1621 (originalVector B) := by
  rw [reducedMerge1621Check, Integer.Sparse.eval_mergeBy, reducedTermEval1626 B hB hF, reducedTermEval1627 B hB hF]
  rw [originalMerge1621, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1622 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1622 (originalVector B) := by
  rw [reducedMerge1622Check, Integer.Sparse.eval_mergeBy, reducedTermEval1628 B hB hF, reducedTermEval1629 B hB hF]
  rw [originalMerge1622, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1623 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1623 (originalVector B) := by
  rw [reducedMerge1623Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1621 B hB hF, reducedMergeEval1622 B hB hF]
  rw [originalMerge1623, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1624 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1624 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1624 (originalVector B) := by
  rw [reducedMerge1624Check, Integer.Sparse.eval_mergeBy, reducedTermEval1630 B hB hF, reducedTermEval1631 B hB hF]
  rw [originalMerge1624, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1625 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1625 (originalVector B) := by
  rw [reducedMerge1625Check, Integer.Sparse.eval_mergeBy, reducedTermEval1632 B hB hF, reducedTermEval1633 B hB hF]
  rw [originalMerge1625, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1626 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1626 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1626 (originalVector B) := by
  rw [reducedMerge1626Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1624 B hB hF, reducedMergeEval1625 B hB hF]
  rw [originalMerge1626, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1627 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1627 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1627 (originalVector B) := by
  rw [reducedMerge1627Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1623 B hB hF, reducedMergeEval1626 B hB hF]
  rw [originalMerge1627, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1628 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1628 (originalVector B) := by
  rw [reducedMerge1628Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1620 B hB hF, reducedMergeEval1627 B hB hF]
  rw [originalMerge1628, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1629 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1629 (originalVector B) := by
  rw [reducedMerge1629Check, Integer.Sparse.eval_mergeBy, reducedTermEval1635 B hB hF, reducedTermEval1636 B hB hF]
  rw [originalMerge1629, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1630 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1630 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1630 (originalVector B) := by
  rw [reducedMerge1630Check, Integer.Sparse.eval_mergeBy, reducedTermEval1634 B hB hF, reducedMergeEval1629 B hB hF]
  rw [originalMerge1630, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1631 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1631 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1631 (originalVector B) := by
  rw [reducedMerge1631Check, Integer.Sparse.eval_mergeBy, reducedTermEval1637 B hB hF, reducedTermEval1638 B hB hF]
  rw [originalMerge1631, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1664 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1664 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1664 (originalVector B) := by
  rw [reducedTermArithmetic1664, ← sound4682 B hB hF]
  change (-20337198821419253760000 : ℝ) * mixedMoment B node4682 node4682Labels =
    (37623398400 : ℝ) * (((-540546566400 : ℤ) : ℝ) * mixedMoment B node4682 node4682Labels + 0)
  ring

theorem reducedTermEval1665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1665 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1665 (originalVector B) := by
  rw [reducedTermArithmetic1665, ← sound4683 B hB hF]
  change (-4166088676073275392000 : ℝ) * mixedMoment B node4683 node4683Labels =
    (37623398400 : ℝ) * (((-110731322880 : ℤ) : ℝ) * mixedMoment B node4683 node4683Labels + 0)
  ring

theorem reducedTermEval1666 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1666 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1666 (originalVector B) := by
  rw [reducedTermArithmetic1666, ← sound4687 B hB hF]
  change (4331084313932070912000 : ℝ) * mixedMoment B node4687 node4687Labels =
    (37623398400 : ℝ) * ((115116775680 : ℝ) * mixedMoment B node4687 node4687Labels + 0)
  ring

theorem reducedTermEval1667 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1667 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1667 (originalVector B) := by
  rw [reducedTermArithmetic1667, ← sound4690 B hB hF]
  change (-7832344641172144128000 : ℝ) * mixedMoment B node4690 node4690Labels =
    (37623398400 : ℝ) * (((-208177489920 : ℤ) : ℝ) * mixedMoment B node4690 node4690Labels + 0)
  ring

theorem reducedTermEval1668 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1668 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1668 (originalVector B) := by
  rw [reducedTermArithmetic1668, ← sound4694 B hB hF]
  change (419207923271467008000 : ℝ) * mixedMoment B node4694 node4694Labels =
    (37623398400 : ℝ) * ((11142213120 : ℝ) * mixedMoment B node4694 node4694Labels + 0)
  ring

theorem reducedTermEval1669 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1669 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1669 (originalVector B) := by
  rw [reducedTermArithmetic1669, ← sound4695 B hB hF]
  change (2088377879151771648000 : ℝ) * mixedMoment B node4695 node4695Labels =
    (37623398400 : ℝ) * ((55507422720 : ℝ) * mixedMoment B node4695 node4695Labels + 0)
  ring

theorem reducedTermEval1670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1670 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1670 (originalVector B) := by
  rw [reducedTermArithmetic1670, ← sound4696 B hB hF]
  change (4668687916798574592000 : ℝ) * mixedMoment B node4696 node4696Labels =
    (37623398400 : ℝ) * ((124090010880 : ℝ) * mixedMoment B node4696 node4696Labels + 0)
  ring

theorem reducedTermEval1671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1671 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1671 (originalVector B) := by
  rw [reducedTermArithmetic1671, ← sound4697 B hB hF]
  change (-47757709229948928000 : ℝ) * mixedMoment B node4697 node4697Labels =
    (37623398400 : ℝ) * (((-1269361920 : ℤ) : ℝ) * mixedMoment B node4697 node4697Labels + 0)
  ring

theorem reducedTermEval1672 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1672 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1672 (originalVector B) := by
  rw [reducedTermArithmetic1672, ← sound4698 B hB hF]
  change (-11360929018687782912000 : ℝ) * mixedMoment B node4698 node4698Labels =
    (37623398400 : ℝ) * (((-301964455680 : ℤ) : ℝ) * mixedMoment B node4698 node4698Labels + 0)
  ring

theorem reducedTermEval1673 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1673 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1673 (originalVector B) := by
  rw [reducedTermArithmetic1673, ← sound4699 B hB hF]
  change (-12243947554527510528000 : ℝ) * mixedMoment B node4699 node4699Labels =
    (37623398400 : ℝ) * (((-325434385920 : ℤ) : ℝ) * mixedMoment B node4699 node4699Labels + 0)
  ring

theorem reducedTermEval1674 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1674 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1674 (originalVector B) := by
  rw [reducedTermArithmetic1674, ← sound4700 B hB hF]
  change (-9017233195750391808000 : ℝ) * mixedMoment B node4700 node4700Labels =
    (37623398400 : ℝ) * (((-239670885120 : ℤ) : ℝ) * mixedMoment B node4700 node4700Labels + 0)
  ring

theorem reducedTermEval1675 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1675 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1675 (originalVector B) := by
  rw [reducedTermArithmetic1675, ← sound4701 B hB hF]
  change (1426161328576266240000 : ℝ) * mixedMoment B node4701 node4701Labels =
    (37623398400 : ℝ) * ((37906233600 : ℝ) * mixedMoment B node4701 node4701Labels + 0)
  ring

theorem reducedTermEval1676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1676 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1676 (originalVector B) := by
  rw [reducedTermArithmetic1676, ← sound4702 B hB hF]
  change (323950101685862400000 : ℝ) * mixedMoment B node4702 node4702Labels =
    (37623398400 : ℝ) * ((8610336000 : ℝ) * mixedMoment B node4702 node4702Labels + 0)
  ring

theorem reducedTermEval1677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1677 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1677 (originalVector B) := by
  rw [reducedTermArithmetic1677, ← sound4703 B hB hF]
  change (2481540634666598400000 : ℝ) * mixedMoment B node4703 node4703Labels =
    (37623398400 : ℝ) * ((65957376000 : ℝ) * mixedMoment B node4703 node4703Labels + 0)
  ring

theorem reducedTermEval1678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1678 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1678 (originalVector B) := by
  rw [reducedTermArithmetic1678, ← sound4704 B hB hF]
  change (6123206211439951872000 : ℝ) * mixedMoment B node4704 node4704Labels =
    (37623398400 : ℝ) * ((162749950080 : ℝ) * mixedMoment B node4704 node4704Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1632 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1632 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1632 (originalVector B) := by
  rw [reducedMerge1632Check, Integer.Sparse.eval_mergeBy, reducedTermEval1639 B hB hF, reducedTermEval1640 B hB hF]
  rw [originalMerge1632, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1633 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1633 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1633 (originalVector B) := by
  rw [reducedMerge1633Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1631 B hB hF, reducedMergeEval1632 B hB hF]
  rw [originalMerge1633, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1634 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1634 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1634 (originalVector B) := by
  rw [reducedMerge1634Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1630 B hB hF, reducedMergeEval1633 B hB hF]
  rw [originalMerge1634, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1635 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1635 (originalVector B) := by
  rw [reducedMerge1635Check, Integer.Sparse.eval_mergeBy, reducedTermEval1641 B hB hF, reducedTermEval1642 B hB hF]
  rw [originalMerge1635, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1636 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1636 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1636 (originalVector B) := by
  rw [reducedMerge1636Check, Integer.Sparse.eval_mergeBy, reducedTermEval1643 B hB hF, reducedTermEval1644 B hB hF]
  rw [originalMerge1636, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1637 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1637 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1637 (originalVector B) := by
  rw [reducedMerge1637Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1635 B hB hF, reducedMergeEval1636 B hB hF]
  rw [originalMerge1637, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1638 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1638 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1638 (originalVector B) := by
  rw [reducedMerge1638Check, Integer.Sparse.eval_mergeBy, reducedTermEval1645 B hB hF, reducedTermEval1646 B hB hF]
  rw [originalMerge1638, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1639 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1639 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1639 (originalVector B) := by
  rw [reducedMerge1639Check, Integer.Sparse.eval_mergeBy, reducedTermEval1647 B hB hF, reducedTermEval1648 B hB hF]
  rw [originalMerge1639, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1640 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1640 (originalVector B) := by
  rw [reducedMerge1640Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1638 B hB hF, reducedMergeEval1639 B hB hF]
  rw [originalMerge1640, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1641 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1641 (originalVector B) := by
  rw [reducedMerge1641Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1637 B hB hF, reducedMergeEval1640 B hB hF]
  rw [originalMerge1641, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1642 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1642 (originalVector B) := by
  rw [reducedMerge1642Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1634 B hB hF, reducedMergeEval1641 B hB hF]
  rw [originalMerge1642, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1643 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1643 (originalVector B) := by
  rw [reducedMerge1643Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1628 B hB hF, reducedMergeEval1642 B hB hF]
  rw [originalMerge1643, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1644 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1644 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1644 (originalVector B) := by
  rw [reducedMerge1644Check, Integer.Sparse.eval_mergeBy, reducedTermEval1650 B hB hF, reducedTermEval1651 B hB hF]
  rw [originalMerge1644, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1645 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1645 (originalVector B) := by
  rw [reducedMerge1645Check, Integer.Sparse.eval_mergeBy, reducedTermEval1649 B hB hF, reducedMergeEval1644 B hB hF]
  rw [originalMerge1645, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1646 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1646 (originalVector B) := by
  rw [reducedMerge1646Check, Integer.Sparse.eval_mergeBy, reducedTermEval1652 B hB hF, reducedTermEval1653 B hB hF]
  rw [originalMerge1646, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1647 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1647 (originalVector B) := by
  rw [reducedMerge1647Check, Integer.Sparse.eval_mergeBy, reducedTermEval1654 B hB hF, reducedTermEval1655 B hB hF]
  rw [originalMerge1647, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1648 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1648 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1648 (originalVector B) := by
  rw [reducedMerge1648Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1646 B hB hF, reducedMergeEval1647 B hB hF]
  rw [originalMerge1648, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1649 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1649 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1649 (originalVector B) := by
  rw [reducedMerge1649Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1645 B hB hF, reducedMergeEval1648 B hB hF]
  rw [originalMerge1649, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1650 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1650 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1650 (originalVector B) := by
  rw [reducedMerge1650Check, Integer.Sparse.eval_mergeBy, reducedTermEval1656 B hB hF, reducedTermEval1657 B hB hF]
  rw [originalMerge1650, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1651 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1651 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1651 (originalVector B) := by
  rw [reducedMerge1651Check, Integer.Sparse.eval_mergeBy, reducedTermEval1658 B hB hF, reducedTermEval1659 B hB hF]
  rw [originalMerge1651, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1652 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1652 (originalVector B) := by
  rw [reducedMerge1652Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1650 B hB hF, reducedMergeEval1651 B hB hF]
  rw [originalMerge1652, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1653 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1653 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1653 (originalVector B) := by
  rw [reducedMerge1653Check, Integer.Sparse.eval_mergeBy, reducedTermEval1660 B hB hF, reducedTermEval1661 B hB hF]
  rw [originalMerge1653, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1654 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1654 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1654 (originalVector B) := by
  rw [reducedMerge1654Check, Integer.Sparse.eval_mergeBy, reducedTermEval1662 B hB hF, reducedTermEval1663 B hB hF]
  rw [originalMerge1654, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1655 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1655 (originalVector B) := by
  rw [reducedMerge1655Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1653 B hB hF, reducedMergeEval1654 B hB hF]
  rw [originalMerge1655, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1656 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1656 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1656 (originalVector B) := by
  rw [reducedMerge1656Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1652 B hB hF, reducedMergeEval1655 B hB hF]
  rw [originalMerge1656, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1657 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1657 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1657 (originalVector B) := by
  rw [reducedMerge1657Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1649 B hB hF, reducedMergeEval1656 B hB hF]
  rw [originalMerge1657, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1658 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1658 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1658 (originalVector B) := by
  rw [reducedMerge1658Check, Integer.Sparse.eval_mergeBy, reducedTermEval1665 B hB hF, reducedTermEval1666 B hB hF]
  rw [originalMerge1658, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1659 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1659 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1659 (originalVector B) := by
  rw [reducedMerge1659Check, Integer.Sparse.eval_mergeBy, reducedTermEval1664 B hB hF, reducedMergeEval1658 B hB hF]
  rw [originalMerge1659, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1660 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1660 (originalVector B) := by
  rw [reducedMerge1660Check, Integer.Sparse.eval_mergeBy, reducedTermEval1667 B hB hF, reducedTermEval1668 B hB hF]
  rw [originalMerge1660, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1661 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1661 (originalVector B) := by
  rw [reducedMerge1661Check, Integer.Sparse.eval_mergeBy, reducedTermEval1669 B hB hF, reducedTermEval1670 B hB hF]
  rw [originalMerge1661, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1662 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1662 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1662 (originalVector B) := by
  rw [reducedMerge1662Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1660 B hB hF, reducedMergeEval1661 B hB hF]
  rw [originalMerge1662, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1663 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1663 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1663 (originalVector B) := by
  rw [reducedMerge1663Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1659 B hB hF, reducedMergeEval1662 B hB hF]
  rw [originalMerge1663, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1664 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1664 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1664 (originalVector B) := by
  rw [reducedMerge1664Check, Integer.Sparse.eval_mergeBy, reducedTermEval1671 B hB hF, reducedTermEval1672 B hB hF]
  rw [originalMerge1664, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1665 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1665 (originalVector B) := by
  rw [reducedMerge1665Check, Integer.Sparse.eval_mergeBy, reducedTermEval1673 B hB hF, reducedTermEval1674 B hB hF]
  rw [originalMerge1665, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1666 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1666 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1666 (originalVector B) := by
  rw [reducedMerge1666Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1664 B hB hF, reducedMergeEval1665 B hB hF]
  rw [originalMerge1666, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1667 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1667 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1667 (originalVector B) := by
  rw [reducedMerge1667Check, Integer.Sparse.eval_mergeBy, reducedTermEval1675 B hB hF, reducedTermEval1676 B hB hF]
  rw [originalMerge1667, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1668 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1668 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1668 (originalVector B) := by
  rw [reducedMerge1668Check, Integer.Sparse.eval_mergeBy, reducedTermEval1677 B hB hF, reducedTermEval1678 B hB hF]
  rw [originalMerge1668, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1669 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1669 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1669 (originalVector B) := by
  rw [reducedMerge1669Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1667 B hB hF, reducedMergeEval1668 B hB hF]
  rw [originalMerge1669, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1670 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1670 (originalVector B) := by
  rw [reducedMerge1670Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1666 B hB hF, reducedMergeEval1669 B hB hF]
  rw [originalMerge1670, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1671 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1671 (originalVector B) := by
  rw [reducedMerge1671Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1663 B hB hF, reducedMergeEval1670 B hB hF]
  rw [originalMerge1671, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1672 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1672 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1672 (originalVector B) := by
  rw [reducedMerge1672Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1657 B hB hF, reducedMergeEval1671 B hB hF]
  rw [originalMerge1672, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1673 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1673 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1673 (originalVector B) := by
  rw [reducedMerge1673Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1643 B hB hF, reducedMergeEval1672 B hB hF]
  rw [originalMerge1673, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1674 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1674 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1674 (originalVector B) := by
  rw [reducedMerge1674Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1614 B hB hF, reducedMergeEval1673 B hB hF]
  rw [originalMerge1674, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1675_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1675 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1675 (originalVector B) := by
  rw [reducedMerge1675Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1555_e B hB hF, reducedMergeEval1674 B hB hF]
  rw [originalMerge1675, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1675_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1675_e_oai
