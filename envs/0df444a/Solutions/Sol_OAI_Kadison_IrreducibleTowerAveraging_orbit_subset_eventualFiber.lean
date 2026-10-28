-- Prove2me | solution 1 for OAI.Kadison.IrreducibleTowerAveraging.orbit_subset_eventualFiber
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:44:53.118415+00:00
-- url     : https://prove2.me/submissions/251ef7f3-8c2c-49c2-8210-823533f461e7

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C038

section
-- module Solutions.OAIQ039_CM.Commutator_IrreducibleTowerAveraging
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.IrreducibleTowerAveraging

open TracialGNS NormalGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ}, n ≤ m → (stage n).range ≤ (stage m).range)

section SingleStage

variable {A I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (ρ : A →ₚ[ℂ] ℂ)
  (hρ : ∀ a b : A, ρ (a*b)=ρ (b*a))

include hρ in
omit [Nonempty I] in
lemma vector_expectation_conjugation (u : unitary A) (hu : (u:A)∈φ.range) (a : A) :
    algebraVector ρ (expectation φ ((u:A)*a*star (u:A)))=
      algebraVector ρ (expectation φ a) := by
  apply (algebraVector_dense ρ).eq_of_inner_left ℂ
  intro b
  rw [inner_symm φ ρ hρ,inner_symm φ ρ hρ,inner_algebraVector,inner_algebraVector]
  obtain ⟨v,hv⟩ := hu
  change φ v=(u:A) at hv
  have hc : (u:A)*expectation φ b=expectation φ b*(u:A) := by
    rw [←hv]
    exact commutes φ b v
  simp only [star_mul,star_star]
  have he : star (u:A)*expectation φ b*(u:A)=expectation φ b := by
    rw [mul_assoc,←hc,←mul_assoc,u.property.1,one_mul]
  calc
    _ = ρ ((u:A)*(star a*(star (u:A)*expectation φ b))) := by
      simp only [mul_assoc]
    _ = ρ ((star a*(star (u:A)*expectation φ b))*(u:A)) := hρ _ _
    _ = ρ (star a*(star (u:A)*expectation φ b*(u:A))) := by
      simp only [mul_assoc]
    _ = _ := by rw [he]

end SingleStage

include hτ in
omit [∀ n, Nonempty (ι n)] in
lemma orbit_subset_eventualFiber_oai (a : M) :
    orbit M τ stage hmono a ⊆ eventualFiber M τ stage a := by
  rintro x ⟨u,rfl⟩
  refine ⟨(u.val:M)*a*star (u.val:M),rfl,?_⟩
  obtain ⟨N,hN⟩ := u.property
  filter_upwards [eventually_ge_atTop N] with n hn
  exact vector_expectation_conjugation (stage n) τ hτ u.val (hmono hn hN) a

end Kadison.IrreducibleTowerAveraging

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.IrreducibleTowerAveraging.orbit_subset_eventualFiber_oai.{u_1, u_2} := @OAI.Kadison.IrreducibleTowerAveraging.orbit_subset_eventualFiber_oai.{u_1, u_2}
