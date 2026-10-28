-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.tower_requirement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:48:10.763162+00:00
-- url     : https://prove2.me/submissions/2107c9cf-df90-401d-b8c6-c94f4d00a4c9

import Mathlib
import Definitions.Def_OAIQ039C075

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTower
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixTower

open TracialGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [instance] Stage.finite Stage.dec Stage.nonempty

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hnormal : NormalGNS.BoundedWOTContinuous M τ)
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
  (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)

variable (x : ℕ → M) (hx : ∀ j,IsSelfAdjoint (x j))

lemma next_spec (n : ℕ) (F : Stage M) :
    2*Fintype.card F.I≤Fintype.card (next M τ hτ hnormal hfaith hone hfac hdiffuse x hx n F).I ∧
    F.hom.range≤(next M τ hτ hnormal hfaith hone hfac hdiffuse x hx n F).hom.range ∧
    ‖algebraVector τ (expectation (next M τ hτ hnormal hfaith hone hfac hdiffuse x hx n F).hom
      (x (Nat.unpair n).1)-τ (x (Nat.unpair n).1) • (1:M))‖<((Nat.unpair n).2+1:ℝ)⁻¹ :=
  Classical.choose_spec (exists_stage_extension M τ hτ hnormal hfaith hone hfac hdiffuse F
    (x (Nat.unpair n).1) (hx _) (show 0<((Nat.unpair n).2+1:ℝ)⁻¹ by positivity))

lemma tower_requirement_oai (j : ℕ) {ε : ℝ} (hε : 0<ε) : ∃ n,
    ‖algebraVector τ (expectation (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx n).hom
      (x j)-τ (x j) • (1:M))‖<ε := by
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
  refine ⟨Nat.pair j k+1,?_⟩
  have he := (next_spec M τ hτ hnormal hfaith hone hfac hdiffuse x hx (Nat.pair j k)
    (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx (Nat.pair j k))).2.2
  simp only [Nat.unpair_pair] at he
  exact he.trans (by simpa only [one_div] using hk)

end Kadison.MatrixTower

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.MatrixTower.tower_requirement_oai.{u_1} := @OAI.Kadison.MatrixTower.tower_requirement_oai.{u_1}
