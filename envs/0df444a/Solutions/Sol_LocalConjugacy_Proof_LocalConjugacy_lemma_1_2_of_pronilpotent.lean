-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.lemma_1_2_of_pronilpotent
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:35:35.441852+00:00
-- url     : https://prove2.me/submissions/1a2e6126-373c-4ece-a62c-aa0094382f7e

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_primaryDecomposition_of_equiv
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_primaryDecomposition_pGroup_of_restriction
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_primaryDecomposition_pi
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_pronilpotent_sylow_extension_zorn
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_pronilpotent_sylow_restriction_injective_zorn

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Algebra
variable {G F : Type*} [Group G] [Group F]





end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]

/-- A continuous discrete quotient of a pronilpotent group is nilpotent. -/
private theorem nilpotent_of_pronilpotent_surjective (hG : Pronilpotent G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Group.IsNilpotent F := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  letI := hG U
  exact Group.nilpotent_of_surjective (QuotientGroup.kerLift f)
    (QuotientGroup.lift_surjective_of_surjective _ f hs le_rfl)





end Topology

section Discrete
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

private theorem pronilpotent_iff_nilpotent : Pronilpotent G ↔ Group.IsNilpotent G := by
  constructor
  · intro h
    exact nilpotent_of_pronilpotent_surjective h (MonoidHom.id G) continuous_id Function.surjective_id
  · intro h
    letI := h
    intro U
    infer_instance



end Discrete
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [Finite N] [MulDistribMulAction J N] [ContinuousSMul J N]





/-- The restriction isomorphism used for each primary coefficient factor in
the pronilpotent case of Lemma 1.2, for arbitrary profinite acting groups. -/
private theorem pronilpotent_sylow_restriction
    {p : ℕ} [Fact p.Prime] (hJ : Pronilpotent J) (hN : IsPGroup p N)
    (P : Subgroup J) (hP : IsSylowPro p ⊤ P) :
    RestrictionIsomorphism (N := N) ⊤ P le_top := by
  refine ⟨pronilpotent_sylow_restriction_injective_zorn hJ hN P hP, ?_⟩
  intro τ hτ
  obtain ⟨_, φ, hφ⟩ := pronilpotent_sylow_extension_zorn hJ hN P hP τ hτ
  exact ⟨φ, hφ⟩

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [Finite N] [MulDistribMulAction J N] [ContinuousSMul J N]





/-- The full primary-decomposition assertion for a single finite primary
coefficient group and a pronilpotent acting group. -/
private theorem primaryDecomposition_pGroup_of_pronilpotent
    {p : ℕ} [Fact p.Prime] (hJ : Pronilpotent J) (hN : IsPGroup p N)
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ q, IsSylowPro q.val.val ⊤ (P q)) :
    PrimaryDecomposition (N := N) P :=
  primaryDecomposition_pGroup_of_restriction hN (pronilpotent_sylow_restriction hJ hN) P hP

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
namespace NilpotentCoefficients

variable {N : Type*} [Group N] [Finite N] [Group.IsNilpotent N]















variable {J : Type*} [Group J] [MulDistribMulAction J N]



attribute [local instance] factorAction

set_option backward.isDefEq.respectTransparency false in
private theorem productEquiv_smul (j : J) (x : ∀ p : PrimeIndex N, Factor N p) :
    productEquiv (j • x) = j • productEquiv x := by
  classical
  change Subgroup.noncommPiCoprod factors_commute (j • x) =
    (MulDistribMulAction.toMulAut J N j) (Subgroup.noncommPiCoprod factors_commute x)
  simp only [Subgroup.noncommPiCoprod_apply]
  exact (Finset.map_noncommProd Finset.univ (fun i : PrimeIndex N => (x i : N))
    (fun i _ k _ hik => factors_commute hik _ _ (x i).property (x k).property)
    (MulDistribMulAction.toMulAut J N j)).symm

variable [TopologicalSpace J] [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul J N]



end NilpotentCoefficients

/-- Lemma 1.2 in the pronilpotent-acting-group case, with finite nilpotent
coefficients. This includes the product over all primes of the ambient group,
not only the prime divisors of the coefficient order. -/
private theorem lemma_1_2_of_pronilpotent_preparedProof
    {J N : Type*} [Group J] [Group N] [TopologicalSpace J] [Profinite J]
    [TopologicalSpace N] [DiscreteTopology N] [Finite N]
    [MulDistribMulAction J N] [ContinuousSMul J N]
    (hN : Pronilpotent N) (hJ : Pronilpotent J)
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ p, IsSylowPro p.val.val ⊤ (P p)) :
    PrimaryDecomposition (N := N) P := by
  letI := pronilpotent_iff_nilpotent.mp hN
  letI (p : NilpotentCoefficients.PrimeIndex N) :=
    NilpotentCoefficients.factorAction (J := J) p
  have h (p : NilpotentCoefficients.PrimeIndex N) :
      PrimaryDecomposition (N := NilpotentCoefficients.Factor N p) P :=
    primaryDecomposition_pGroup_of_pronilpotent hJ
      (NilpotentCoefficients.primarySylow p).isPGroup' P hP
  let e := (NilpotentCoefficients.productEquiv (N := N)).symm
  apply primaryDecomposition_of_equiv P e continuous_of_discreteTopology
    continuous_of_discreteTopology _ (primaryDecomposition_pi P h)
  intro j n
  apply e.symm.injective
  change NilpotentCoefficients.productEquiv (e (j • n)) =
    NilpotentCoefficients.productEquiv (j • e n)
  rw [NilpotentCoefficients.productEquiv_smul]
  exact (e.symm_apply_apply (j • n)).trans (congrArg (fun x => j • x) (e.symm_apply_apply n).symm)

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@DiscreteTopology.{u_2} N inst_4] [Finite.{u_2 + 1} N]
  [inst_7 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
      inst_2 inst_4]
  (hN : @LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_2} N inst_1 inst_4)
  (hJ : @LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1} J inst inst_2)
  (P : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_2 → @Subgroup.{u_1} J inst)
  (hP :
    ∀ (p : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_2),
      @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1}
        (@Subtype.val.{1} Nat (fun (p : Nat) => Nat.Prime p)
          (@Subtype.val.{1} Nat.Primes
            (fun (p : Nat.Primes) =>
              @Exists.{u_1 + 1} (@OpenNormalSubgroup.{u_1} J inst inst_2)
                fun (U : @OpenNormalSubgroup.{u_1} J inst inst_2) =>
                @Dvd.dvd.{0} Nat Nat.instDvd (@Subtype.val.{1} Nat (fun (p : Nat) => Nat.Prime p) p)
                  (Nat.card.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} J inst)
                      (@OpenSubgroup.toSubgroup.{u_1} J inst inst_2
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} J inst inst_2 U)))))
            p))
        J inst inst_2 (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) (P p)),
  @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 P :=
  @LocalConjugacy.Proof.LocalConjugacy.lemma_1_2_of_pronilpotent_preparedProof
