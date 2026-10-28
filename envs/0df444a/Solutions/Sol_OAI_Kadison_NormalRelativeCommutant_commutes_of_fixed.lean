-- Prove2me | solution 1 for OAI.Kadison.NormalRelativeCommutant.commutes_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:21:14.541099+00:00
-- url     : https://prove2.me/submissions/b4bc2d5d-4fad-4529-9914-525c91492158

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C040

section
-- module Solutions.OAIQ039_CM.Commutator_NormalRelativeCommutant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Kadison.NormalRelativeCommutant

open TracialGNS NormalGNS

variable {H D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra D]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (π : D →⋆ₐ[ℂ] M)

lemma vector_injective (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    Function.Injective (algebraVector τ) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hfaith
  have hv : algebraVector τ (a-b)=0 := by rw [map_sub,hab,sub_self]
  rw [←inner_algebraVector,hv,inner_zero_left]

lemma commutes_of_fixed_oai (b : M) (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfix : ∀ u : unitary D,
      conjugation τ hτ (liftedUnitary M π u) (algebraVector τ b)=algebraVector τ b) :
    ∀ a : D, π a*b=b*π a := by
  have hu (u : unitary D) : π (u:D)*b=b*π (u:D) := by
    have hh0 := hfix u
    rw [algebraVector_apply,conjugation_coe] at hh0
    have he : π (u:D)*b*star (π (u:D))=b := vector_injective M τ hfaith hh0
    have hh := congrArg (fun x : M => x*π (u:D)) he
    have hut : star (π (u:D))*π (u:D)=1 := (liftedUnitary M π u).property.1
    simpa only [mul_assoc,hut,mul_one] using hh
  intro a
  have ha : a∈Submodule.span ℂ (unitary D:Set D) := by rw [CStarAlgebra.span_unitary]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha => exact hu ⟨a,ha⟩
  | zero => simp
  | add a b ha hb h1 h2 => simp only [map_add,add_mul,mul_add,h1,h2]
  | smul c a ha h1 => simp only [map_smul,smul_mul_assoc,mul_smul_comm,h1]

end Kadison.NormalRelativeCommutant

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.NormalRelativeCommutant.commutes_of_fixed_oai.{u_1, u_2} := @OAI.Kadison.NormalRelativeCommutant.commutes_of_fixed_oai.{u_1, u_2}
