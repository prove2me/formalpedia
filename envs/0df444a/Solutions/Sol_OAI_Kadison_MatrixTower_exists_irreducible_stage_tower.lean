-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.exists_irreducible_stage_tower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:46:44.438773+00:00
-- url     : https://prove2.me/submissions/d2f01253-1dfa-4278-9f5f-fd6a8da8b448

import Mathlib
import Definitions.Def_OAIQ039C075
import Theorems.Thm_OAI_Kadison_MatrixTower_scalar_of_commutes
import Theorems.Thm_OAI_Kadison_MatrixTower_tower_requirement

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

lemma tower_increasing : Monotone (fun n =>
    (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx n).hom.range) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (next_spec M τ hτ hnormal hfaith hone hfac hdiffuse x hx n _).2.1

lemma tower_size (n : ℕ) : n+1≤
    Fintype.card (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx n).I := by
  induction n with
  | zero => exact Fintype.card_pos (α:=Unit)
  | succ n ih =>
    have he := (next_spec M τ hτ hnormal hfaith hone hfac hdiffuse x hx n
      (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx n)).1
    change 2*Fintype.card (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx n).I≤
      Fintype.card (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx (n+1)).I at he
    omega

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerIrreducible
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace ComplexStarModule

namespace Kadison.MatrixTower

open TracialGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma exists_selfAdjoint_dense_sequence [TopologicalSpace.SeparableSpace τ.GNS] :
    ∃ x : ℕ → M, (∀ j,IsSelfAdjoint (x j)) ∧
      ∀ a : M,IsSelfAdjoint a → ∀ ε : ℝ,0<ε → ∃ j,‖algebraVector τ (a-x j)‖<ε := by
  classical
  let S : Set τ.GNS := Set.range (fun a : selfAdjoint M => algebraVector τ (a:M))
  have : Nonempty S := ⟨⟨algebraVector τ 0,⟨⟨0,IsSelfAdjoint.zero M⟩,rfl⟩⟩⟩
  obtain ⟨u,hu⟩ := TopologicalSpace.exists_dense_seq S
  choose x hx using (fun n => (u n).property)
  refine ⟨fun n => (x n:M),fun n => (x n).property,?_⟩
  intro a ha ε hε
  obtain ⟨j,hj⟩ := hu.exists_dist_lt ⟨algebraVector τ a,⟨⟨a,ha⟩,rfl⟩⟩ hε
  refine ⟨j,?_⟩
  change dist (algebraVector τ a) (u j).val<ε at hj
  rwa [←hx j,dist_eq_norm,←map_sub] at hj

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStandardUnconditional
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification TracialSequence CyclicColumns HilbertPadding

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M]

variable (τ : M →ₚ[ℂ] ℂ)

omit [Nontrivial M] in
theorem exists_irreducible_stage_tower_oai [TopologicalSpace.SeparableSpace τ.GNS]
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M) :
    ∃ E : ℕ → Stage M, Monotone (fun n => (E n).hom.range) ∧
      (∀ n,n+1 ≤ Fintype.card (E n).I) ∧
      (∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M)) := by
  obtain ⟨x,hx,hxden⟩ := exists_selfAdjoint_dense_sequence M τ
  let E := tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx
  refine ⟨E,tower_increasing M τ hτ hnormal hfaith hone hfac hdiffuse x hx,
    tower_size M τ hτ hnormal hfaith hone hfac hdiffuse x hx,?_⟩
  intro a ha
  refine ⟨τ a,?_⟩
  exact scalar_of_commutes M τ hτ hone x hxden E
    (fun j _ hε => tower_requirement M τ hτ hnormal hfaith hone hfac hdiffuse x hx j hε)
    hfaith a ha

end Kadison.MatrixTower

end

end OAI
end

theorem solution : type_of% @OAI.Kadison.MatrixTower.exists_irreducible_stage_tower_oai := @OAI.Kadison.MatrixTower.exists_irreducible_stage_tower_oai
