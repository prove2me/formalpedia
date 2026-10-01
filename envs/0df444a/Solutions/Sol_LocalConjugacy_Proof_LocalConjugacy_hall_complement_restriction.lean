-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.hall_complement_restriction
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:07:37.366009+00:00
-- url     : https://prove2.me/submissions/68748ca7-1a72-47c7-a9f8-ec1015593da1

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_continuous_hom_eq_one_of_proPrimes
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_extend_cocycle_across_trivial_factor

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy



















section Cocycles
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



/-- Restriction to the Hall complement is injective and every cocycle on
the complement extends. The normal factor acts trivially and has no p-primes. -/
private theorem hall_complement_restriction_preparedProof [DiscreteTopology N]
    {p : ℕ} [Fact p.Prime] (hN : IsPGroup p N)
    (M Q : Subgroup J) [M.Normal]
    (hM : IsClosed (M : Set J)) (hQ : IsClosed (Q : Set J)) (hs : M.IsComplement' Q)
    (hprimes : HasProPrimes {r | p < r} M)
    (hact : ∀ (m : M) (n : N), (m : J) • n = n) :
    RestrictionIsomorphism (N := N) ⊤ Q le_top := by
  have hzero (f : Cocycle (N := N) (⊤ : Subgroup J)) (m : M) :
      f.toFun ⟨m, trivial⟩ = 1 := by
    let φ : M →* N :=
      { toFun := fun x => f.toFun ⟨x, trivial⟩
        map_one' := cocycle_one f
        map_mul' := fun x y => by
          change f.toFun ((⟨x, trivial⟩ : (⊤ : Subgroup J)) * ⟨y, trivial⟩) = _
          rw [f.map_mul, hact] }
    exact continuous_hom_eq_one_of_proPrimes hprimes (Nat.lt_irrefl p) hN φ
      (f.continuous_toFun.comp (continuous_subtype_val.subtype_mk _)) m
  have hval (f : Cocycle (N := N) (⊤ : Subgroup J)) (m : M) (q : Q) :
      f.toFun ⟨(m : J) * q, trivial⟩ = f.toFun ⟨q, trivial⟩ := by
    change f.toFun ((⟨m, trivial⟩ : (⊤ : Subgroup J)) * ⟨q, trivial⟩) = _
    rw [f.map_mul, hzero, hact, one_mul]
  constructor
  · intro f g hfg
    obtain ⟨n, hn⟩ := hfg
    refine ⟨n, fun x => ?_⟩
    obtain ⟨⟨m, q⟩, hx⟩ := hs.2 (x : J)
    have hx' : x = (⟨(m : J) * q, trivial⟩ : (⊤ : Subgroup J)) := Subtype.ext hx.symm
    rw [hx', hval, hval]
    change g.toFun ⟨q, trivial⟩ = n⁻¹ * f.toFun ⟨q, trivial⟩ * (((m : J) * q) • n)
    rw [mul_smul, hact]
    exact hn q
  · intro f _
    obtain ⟨F, hF⟩ := extend_cocycle_across_trivial_factor M Q hM hQ hs hact f
    refine ⟨F, ?_⟩
    change Cohomologous (restrictCocycle le_top F) f
    rw [hF]
    exact cohomologous_refl f

end Cocycles
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@IsTopologicalGroup.{u_2} N inst_4 inst_1]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6)))
      inst_2 inst_4]
  [@DiscreteTopology.{u_2} N inst_4] {p : Nat} [Fact (Nat.Prime p)] (hN : @IsPGroup.{u_2} p N inst_1)
  (M Q : @Subgroup.{u_1} J inst) [@Subgroup.Normal.{u_1} J inst M]
  (hM :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) M))
  (hQ :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) Q))
  (hs : @Subgroup.IsComplement'.{u_1} J inst M Q)
  (hprimes :
    @LocalConjugacy.Proof.LocalConjugacy.HasProPrimes.{u_1}
      (@Set.ofPred.{0} Nat fun (r : Nat) => @LT.lt.{0} Nat instLTNat p r)
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) M x)
      (@Subgroup.toGroup.{u_1} J inst M)
      (@instTopologicalSpaceSubtype.{u_1} J
        (fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) M x)
        inst_2))
  (hact :
    ∀
      (m :
        @Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) M x)
      (n : N),
      @Eq.{u_2 + 1} N
        (@HSMul.hSMul.{u_1, u_2, u_2} J N N
          (@instHSMul.{u_1, u_2} J N
            (@SemigroupAction.toSMul.{u_1, u_2} J N
              (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
              (@MulAction.toSemigroupAction.{u_1, u_2} J N
                (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
                  (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6))))
          (@Subtype.val.{u_1 + 1} J
            (fun (x : J) =>
              @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) M
                x)
            m)
          n)
        n),
  @LocalConjugacy.Proof.LocalConjugacy.RestrictionIsomorphism.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
    (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) Q
    (@le_top.{u_1} (@Subgroup.{u_1} J inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
      (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
        (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instCompleteLattice.{u_1} J inst)))
      Q) :=
  @LocalConjugacy.Proof.LocalConjugacy.hall_complement_restriction_preparedProof
