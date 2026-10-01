-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.NonabelianComplement.local_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:32:42.039978+00:00
-- url     : https://prove2.me/submissions/b4135f04-c13a-41b4-a1ea-e24d5be3e8e1

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
namespace AbelianComplement

variable {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
  (hc : Subgroup.IsComplement' N H)



private theorem projection_mul_right (x : G) {h : G} (hh : h ∈ H) :
    projection N H hc (x * h) = projection N H hc x := by
  have he := congrArg Prod.fst (hc.equiv_mul_right_of_mem (g := x) hh)
  exact he













end AbelianComplement
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
namespace NonabelianComplement
open AbelianComplement

section Algebra
variable {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
  (hc : Subgroup.IsComplement' N H)



/-- A conjugate inclusion gives a coboundary for the inverse projection cocycle. -/
private theorem local_coboundary_preparedProof (S : Subgroup G) (g : G) (hg : conjugate g S ≤ H) :
    ∃ n : N, ∀ x : S,
      1 = n⁻¹ * (projection N H hc x)⁻¹ * MulAut.conjNormal (x : G) n := by
  let b := projection N H hc g⁻¹
  refine ⟨b⁻¹, fun x => ?_⟩
  have hm : g * x * g⁻¹ ∈ H := hg (Subgroup.mem_map_of_mem _ x.property)
  have he : (x : G) * g⁻¹ = g⁻¹ * (g * x * g⁻¹) := by group
  have hf : MulAut.conjNormal (x : G) b * projection N H hc x = b := by
    rw [← projection_mul_reverse N H hc, he, projection_mul_right N H hc g⁻¹ hm]
  have h' : MulAut.conjNormal (x : G) b = b * (projection N H hc x)⁻¹ := by
    calc
      MulAut.conjNormal (x : G) b =
          (MulAut.conjNormal (x : G) b * projection N H hc x) * (projection N H hc x)⁻¹ := by group
      _ = _ := by rw [hf]
  rw [inv_inv, map_inv, h']
  group



end Algebra

section Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
  (N H : Subgroup G) [N.Normal] (hc : Subgroup.IsComplement' N H)
  (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))





attribute [local instance] conjugationAction





include hc hN hH





end Topology
end NonabelianComplement
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] (N H : @Subgroup.{u_1} G inst) [inst_1 : @Subgroup.Normal.{u_1} G inst N]
  (hc : @Subgroup.IsComplement'.{u_1} G inst N H) (S : @Subgroup.{u_1} G inst) (g : G)
  (hg :
    @LE.le.{u_1} (@Subgroup.{u_1} G inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
      (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst g S) H),
  @Exists.{u_1 + 1}
    (@Subtype.{u_1 + 1} G fun (x : G) =>
      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
    fun
      (n :
        @Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x) =>
    ∀
      (x :
        @Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) S x),
      @Eq.{u_1 + 1}
        (@Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
        (@OfNat.ofNat.{u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (nat_lit 1)
          (@One.toOfNat1.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (@Subgroup.one.{u_1} G inst N)))
        (@HMul.hMul.{u_1, u_1, u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@instHMul.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (@Subgroup.mul.{u_1} G inst N))
          (@HMul.hMul.{u_1, u_1, u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (@instHMul.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x)
              (@Subgroup.mul.{u_1} G inst N))
            (@Inv.inv.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x)
              (@Subgroup.inv.{u_1} G inst N) n)
            (@Inv.inv.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x)
              (@Subgroup.inv.{u_1} G inst N)
              (@LocalConjugacy.Proof.LocalConjugacy.AbelianComplement.projection.{u_1} G inst N H hc
                (@Subtype.val.{u_1 + 1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      S x)
                  x))))
          (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
            (@MulEquiv.{u_1, u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x)
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x)
              (@Subgroup.mul.{u_1} G inst N) (@Subgroup.mul.{u_1} G inst N))
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (fun
                (x :
                  @Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      N x) =>
              @Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x)
            (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
              (@MulEquiv.{u_1, u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    N x)
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    N x)
                (@Subgroup.mul.{u_1} G inst N) (@Subgroup.mul.{u_1} G inst N))
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x)
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x)
              (@MulEquiv.instEquivLike.{u_1, u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    N x)
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    N x)
                (@Subgroup.mul.{u_1} G inst N) (@Subgroup.mul.{u_1} G inst N)))
            (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
              (@MonoidHom.{u_1, u_1} G
                (@MulAut.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      N x)
                  (@Subgroup.mul.{u_1} G inst N))
                (@MulOneClass.toMulOne.{u_1} G
                  (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
                (@MulOneClass.toMulOne.{u_1}
                  (@MulAut.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        N x)
                    (@Subgroup.mul.{u_1} G inst N))
                  (@Monoid.toMulOneClass.{u_1}
                    (@MulAut.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          N x)
                      (@Subgroup.mul.{u_1} G inst N))
                    (@DivInvMonoid.toMonoid.{u_1}
                      (@MulAut.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            N x)
                        (@Subgroup.mul.{u_1} G inst N))
                      (@Group.toDivInvMonoid.{u_1}
                        (@MulAut.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              N x)
                          (@Subgroup.mul.{u_1} G inst N))
                        (@MulAut.instGroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              N x)
                          (@Subgroup.mul.{u_1} G inst N)))))))
              G
              (fun (x : G) =>
                @MulAut.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      N x)
                  (@Subgroup.mul.{u_1} G inst N))
              (@MonoidHom.instFunLike.{u_1, u_1} G
                (@MulAut.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      N x)
                  (@Subgroup.mul.{u_1} G inst N))
                (@MulOneClass.toMulOne.{u_1} G
                  (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
                (@MulOneClass.toMulOne.{u_1}
                  (@MulAut.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        N x)
                    (@Subgroup.mul.{u_1} G inst N))
                  (@Monoid.toMulOneClass.{u_1}
                    (@MulAut.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          N x)
                      (@Subgroup.mul.{u_1} G inst N))
                    (@DivInvMonoid.toMonoid.{u_1}
                      (@MulAut.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            N x)
                        (@Subgroup.mul.{u_1} G inst N))
                      (@Group.toDivInvMonoid.{u_1}
                        (@MulAut.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              N x)
                          (@Subgroup.mul.{u_1} G inst N))
                        (@MulAut.instGroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              N x)
                          (@Subgroup.mul.{u_1} G inst N)))))))
              (@MulAut.conjNormal.{u_1} G inst N inst_1)
              (@Subtype.val.{u_1 + 1} G
                (fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    S x)
                x))
            n)) :=
  @LocalConjugacy.Proof.LocalConjugacy.NonabelianComplement.local_coboundary_preparedProof
