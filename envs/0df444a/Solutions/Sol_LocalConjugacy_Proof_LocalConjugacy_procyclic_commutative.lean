-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.procyclic_commutative
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:49:45.200456+00:00
-- url     : https://prove2.me/submissions/caffed43-5339-4af5-8b59-dd2f245e47eb

import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_CocycleZorn
import Definitions.Def_LocalConjugacy_Proof_CocycleProducts
import Definitions.Def_LocalConjugacy_Proof_FiniteCoefficientSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInvarianceSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInjectivity
import Definitions.Def_LocalConjugacy_Proof_CocycleRebase
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
import Definitions.Def_LocalConjugacy_Proof_ProfiniteHall
import Definitions.Def_LocalConjugacy_Proof_ActionProductTopology
import Definitions.Def_LocalConjugacy_Proof_HallCohomology
import Definitions.Def_LocalConjugacy_Proof_SupersolvableRestriction
import Definitions.Def_LocalConjugacy_Proof_NilpotentCoefficients
import Definitions.Def_LocalConjugacy_Proof_NonabelianComplement
import Definitions.Def_LocalConjugacy_Proof_ComplementSupersolvable
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion
import Definitions.Def_LocalConjugacy_Proof_QuaternionCohomology
import Definitions.Def_LocalConjugacy_Proof_QuaternionMatrices
import Definitions.Def_LocalConjugacy_Proof_QuaternionAction
import Definitions.Def_LocalConjugacy_Proof_QuaternionComplements

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open scoped IsMulCommutative

private theorem procyclic_commutative_preparedProof {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] (hG : Procyclic G) :
    ∀ x y : G, x * y = y * x := by
  obtain ⟨g, hg⟩ := hG
  have hz : ∀ x ∈ Subgroup.zpowers g, ∀ y : G, x * y = y * x := by
    intro x hx
    have hc : IsClosed {y : G | x * y = y * x} := isClosed_eq
      (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
    have hs : (Subgroup.zpowers g : Set G) ⊆ {y : G | x * y = y * x} := by
      intro y hy
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Subgroup.zpowers g) ⟨y, hy⟩)
    have ht := closure_minimal hs hc
    rw [hg.closure_eq] at ht
    exact fun y => ht (Set.mem_univ y)
  intro x y
  have hc : IsClosed {x : G | x * y = y * x} := isClosed_eq
    (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have ht := closure_minimal (fun z hz' => hz z hz' y) hc
  rw [hg.closure_eq] at ht
  exact ht (Set.mem_univ x)

section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [DiscreteTopology N] [MulDistribMulAction J N] [ContinuousSMul J N]





end

section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]



end
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G] [@IsTopologicalGroup.{u_1} G inst_1 inst]
  [@T2Space.{u_1} G inst_1] (hG : @LocalConjugacy.Proof.LocalConjugacy.Procyclic.{u_1} G inst inst_1) (x y : G),
  @Eq.{u_1 + 1} G
    (@HMul.hMul.{u_1, u_1, u_1} G G G
      (@instHMul.{u_1} G
        (@MulOne.toMul.{u_1} G
          (@MulOneClass.toMulOne.{u_1} G
            (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))))
      x y)
    (@HMul.hMul.{u_1, u_1, u_1} G G G
      (@instHMul.{u_1} G
        (@MulOne.toMul.{u_1} G
          (@MulOneClass.toMulOne.{u_1} G
            (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))))
      y x) :=
  @LocalConjugacy.Proof.LocalConjugacy.procyclic_commutative_preparedProof
