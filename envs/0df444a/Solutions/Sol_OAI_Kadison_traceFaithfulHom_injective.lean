-- Prove2me | solution 1 for OAI.Kadison.traceFaithfulHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:09:46.395781+00:00
-- url     : https://prove2.me/submissions/e1035876-4c40-4bb3-a6c8-f3c090a92230

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_TraceFaithfulHomInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

omit [StarModule ℂ A] [StarModule ℂ B] in
lemma traceFaithfulHom_injective_oai (φ : A →⋆ₐ[ℂ] B) (τ : A →ₗ[ℂ] ℂ) (ρ : B →ₗ[ℂ] ℂ)
    (hfaith : ∀ a : A,τ (star a*a)=0 → a=0) (htrace : ∀ a,ρ (φ a)=τ a) :
    Function.Injective φ := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hfaith
  rw [←htrace,map_mul,map_star,map_sub,hab,sub_self,star_zero,mul_zero,map_zero]

end Kadison

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.traceFaithfulHom_injective_oai.{u_1, u_2} := @OAI.Kadison.traceFaithfulHom_injective_oai.{u_1, u_2}
