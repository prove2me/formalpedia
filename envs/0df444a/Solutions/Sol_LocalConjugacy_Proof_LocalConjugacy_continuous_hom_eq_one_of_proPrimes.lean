-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.continuous_hom_eq_one_of_proPrimes
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:46:10.086382+00:00
-- url     : https://prove2.me/submissions/85602d98-b83a-4024-8c97-5139fc9443f1

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















/-- The coprime homomorphism argument for a whole set of primes, with
possibly infinite discrete p-group coefficients. -/
private theorem continuous_hom_eq_one_of_proPrimes_preparedProof {G N : Type*} [Group G] [Group N]
    [TopologicalSpace G] [TopologicalSpace N] [DiscreteTopology N]
    {π : Set ℕ} {p : ℕ} [hp : Fact p.Prime] (hG : HasProPrimes π G)
    (hpπ : p ∉ π) (hN : IsPGroup p N) (f : G →* N) (hf : Continuous f) (x : G) :
    f x = 1 := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  let φ := QuotientGroup.lift U.toSubgroup f (show U.toSubgroup ≤ f.ker from le_rfl)
  have hcop : p.Coprime (Nat.card (G ⧸ U.toSubgroup)) :=
    hp.out.coprime_iff_not_dvd.mpr (fun hd => hpπ (hG U p hp.out hd))
  obtain ⟨k, hk⟩ := hN (f x)
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) (orderOf_dvd_of_pow_eq_one hk)
  exact (orderOf_map_dvd φ (QuotientGroup.mk' U.toSubgroup x)).trans
    (orderOf_dvd_natCard (QuotientGroup.mk' U.toSubgroup x))



section Cocycles
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]





end Cocycles
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {G : Type u_1} {N : Type u_2} [inst : Group.{u_1} G] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} G]
  [inst_3 : TopologicalSpace.{u_2} N] [@DiscreteTopology.{u_2} N inst_3] {π : Set.{0} Nat} {p : Nat}
  [hp : Fact (Nat.Prime p)] (hG : @LocalConjugacy.Proof.LocalConjugacy.HasProPrimes.{u_1} π G inst inst_2)
  (hpπ : Not (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) π p))
  (hN : @IsPGroup.{u_2} p N inst_1)
  (f :
    @MonoidHom.{u_1, u_2} G N
      (@MulOneClass.toMulOne.{u_1} G
        (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
      (@MulOneClass.toMulOne.{u_2} N
        (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
  (hf :
    @Continuous.{u_1, u_2} G N inst_2 inst_3
      (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
        (@MonoidHom.{u_1, u_2} G N
          (@MulOneClass.toMulOne.{u_1} G
            (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
          (@MulOneClass.toMulOne.{u_2} N
            (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
        G (fun (x : G) => N)
        (@MonoidHom.instFunLike.{u_1, u_2} G N
          (@MulOneClass.toMulOne.{u_1} G
            (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
          (@MulOneClass.toMulOne.{u_2} N
            (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
        f))
  (x : G),
  @Eq.{u_2 + 1} N
    (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
      (@MonoidHom.{u_1, u_2} G N
        (@MulOneClass.toMulOne.{u_1} G
          (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
        (@MulOneClass.toMulOne.{u_2} N
          (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
      G (fun (x : G) => N)
      (@MonoidHom.instFunLike.{u_1, u_2} G N
        (@MulOneClass.toMulOne.{u_1} G
          (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
        (@MulOneClass.toMulOne.{u_2} N
          (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
      f x)
    (@OfNat.ofNat.{u_2} N (nat_lit 1)
      (@One.toOfNat1.{u_2} N
        (@InvOneClass.toOne.{u_2} N
          (@DivInvOneMonoid.toInvOneClass.{u_2} N
            (@DivisionMonoid.toDivInvOneMonoid.{u_2} N (@Group.toDivisionMonoid.{u_2} N inst_1)))))) :=
  @LocalConjugacy.Proof.LocalConjugacy.continuous_hom_eq_one_of_proPrimes_preparedProof
