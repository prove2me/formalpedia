-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.NonabelianComplement.local_inclusion_of_primary
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:43:23.577986+00:00
-- url     : https://prove2.me/submissions/349ddef2-59c7-4079-a837-02cf141d7b75

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_NonabelianComplement_inclusion_of_coboundary
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_NonabelianComplement_local_coboundary
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_subgroupOf

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
namespace NonabelianComplement
open AbelianComplement

section Algebra
variable {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
  (hc : Subgroup.IsComplement' N H)







end Algebra

section Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
  (N H : Subgroup G) [N.Normal] (hc : Subgroup.IsComplement' N H)
  (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))





attribute [local instance] conjugationAction





include hc hN hH

/-- The complement/cocycle argument in Proposition 3.1, with its exact
primary-decomposition input isolated. -/
private theorem local_inclusion_of_primary_preparedProof (K : Subgroup G) (hK : IsClosed (K : Set G))
    (hloc : LocallyContains H K)
    (hprimary : ∀ (P : PrimeDivisor K → Subgroup K),
      (∀ p, IsSylowPro p.val.val ⊤ (P p)) → PrimaryDecomposition (N := N) P) :
    ∃ n : N, conjugate (n : G) K ≤ H := by
  classical
  letI := profinite_closed_subgroup K hK
  choose S hS g hg using fun p : PrimeDivisor K => hloc p.val.val p.val.property
  let P : PrimeDivisor K → Subgroup K := fun p => (S p).subgroupOf K
  have hP (p : PrimeDivisor K) : IsSylowPro p.val.val ⊤ (P p) :=
    isSylowPro_subgroupOf K (S p) hK (hS p)
  let f := inverseCocycle N H hc hN hH K
  have hcoh : Cohomologous f (trivialCocycle ⊤) := by
    apply (hprimary P hP).2.1
    intro p
    obtain ⟨n, hn⟩ := local_coboundary N H hc (S p) (g p) (hg p)
    refine ⟨n, fun x => ?_⟩
    exact hn ⟨x, x.property⟩
  obtain ⟨n, hn⟩ := hcoh
  refine ⟨n, inclusion_of_coboundary N H hc K n (fun x => ?_)⟩
  exact hn ⟨x, trivial⟩



end Topology
end NonabelianComplement
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N H : @Subgroup.{u_1} G inst)
  [inst_3 : @Subgroup.Normal.{u_1} G inst N] (hc : @Subgroup.IsComplement'.{u_1} G inst N H)
  (hN :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) N))
  (hH :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) H))
  (K : @Subgroup.{u_1} G inst)
  (hK :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) K))
  (hloc : @LocalConjugacy.Proof.LocalConjugacy.LocallyContains.{u_1} G inst inst_1 H K)
  (hprimary :
    ∀
      (P :
        @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                x)
            (@Subgroup.toGroup.{u_1} G inst K)
            (@instTopologicalSpaceSubtype.{u_1} G
              (fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                  x)
              inst_1) →
          @Subgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                x)
            (@Subgroup.toGroup.{u_1} G inst K)),
      (∀
          (p :
            @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                  x)
              (@Subgroup.toGroup.{u_1} G inst K)
              (@instTopologicalSpaceSubtype.{u_1} G
                (fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    K x)
                inst_1)),
          @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1}
            (@Subtype.val.{1} Nat (fun (p : Nat) => Nat.Prime p)
              (@Subtype.val.{1} Nat.Primes
                (fun (p : Nat.Primes) =>
                  @Exists.{u_1 + 1}
                    (@OpenNormalSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          K x)
                      (@Subgroup.toGroup.{u_1} G inst K)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            K x)
                        inst_1))
                    fun
                      (U :
                        @OpenNormalSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              K x)
                          (@Subgroup.toGroup.{u_1} G inst K)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                K x)
                            inst_1)) =>
                    @Dvd.dvd.{0} Nat Nat.instDvd (@Subtype.val.{1} Nat (fun (p : Nat) => Nat.Prime p) p)
                      (Nat.card.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              K x)
                          (@Subgroup.{u_1}
                            (@Subtype.{u_1 + 1} G fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                K x)
                            (@Subgroup.toGroup.{u_1} G inst K))
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                            (@Subtype.{u_1 + 1} G fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                K x)
                            (@Subgroup.toGroup.{u_1} G inst K))
                          (@OpenSubgroup.toSubgroup.{u_1}
                            (@Subtype.{u_1 + 1} G fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                K x)
                            (@Subgroup.toGroup.{u_1} G inst K)
                            (@instTopologicalSpaceSubtype.{u_1} G
                              (fun (x : G) =>
                                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                    (@Subgroup.instSetLike.{u_1} G inst))
                                  K x)
                              inst_1)
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                              (@Subtype.{u_1 + 1} G fun (x : G) =>
                                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                    (@Subgroup.instSetLike.{u_1} G inst))
                                  K x)
                              (@Subgroup.toGroup.{u_1} G inst K)
                              (@instTopologicalSpaceSubtype.{u_1} G
                                (fun (x : G) =>
                                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                      (@Subgroup.instSetLike.{u_1} G inst))
                                    K x)
                                inst_1)
                              U)))))
                p))
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                x)
            (@Subgroup.toGroup.{u_1} G inst K)
            (@instTopologicalSpaceSubtype.{u_1} G
              (fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                  x)
              inst_1)
            (@Top.top.{u_1}
              (@Subgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    K x)
                (@Subgroup.toGroup.{u_1} G inst K))
              (@Subgroup.instTop.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    K x)
                (@Subgroup.toGroup.{u_1} G inst K)))
            (P p)) →
        @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subgroup.toGroup.{u_1} G inst K) (@Subgroup.toGroup.{u_1} G inst N)
          (@instTopologicalSpaceSubtype.{u_1} G
            (fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                x)
            inst_1)
          (@instTopologicalSpaceSubtype.{u_1} G
            (fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            inst_1)
          (@Subgroup.instMulDistribMulActionSubtypeMem.{u_1, u_1} G
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            inst
            (@DivInvMonoid.toMonoid.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x)
              (@Group.toDivInvMonoid.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    N x)
                (@Subgroup.toGroup.{u_1} G inst N)))
            (@LocalConjugacy.Proof.LocalConjugacy.NonabelianComplement.conjugationAction.{u_1} G inst N inst_3) K)
          P),
  @Exists.{u_1 + 1}
    (@Subtype.{u_1 + 1} G fun (x : G) =>
      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
    fun
      (n :
        @Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x) =>
    @LE.le.{u_1} (@Subgroup.{u_1} G inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
      (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst
        (@Subtype.val.{u_1 + 1} G
          (fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          n)
        K)
      H :=
  @LocalConjugacy.Proof.LocalConjugacy.NonabelianComplement.local_inclusion_of_primary_preparedProof
