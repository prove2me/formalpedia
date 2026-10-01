-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.AbelianComplement.conjugate_le_of_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:37:20.82664+00:00
-- url     : https://prove2.me/submissions/7c9a5bfb-24ed-4f64-946c-41b0895ecf9d

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_AbelianComplement_projection_mul

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
namespace AbelianComplement

variable {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
  (hc : Subgroup.IsComplement' N H)





private theorem projection_of_mem (n : N) : projection N H hc n = n :=
  hc.equiv_fst_eq_self_of_mem_of_one_mem H.one_mem n.property

private theorem projection_eq_one_iff (x : G) : projection N H hc x = 1 ↔ x ∈ H := by
  rw [← Subtype.coe_inj]
  exact hc.coe_equiv_fst_eq_one_iff_mem N.one_mem





private theorem conjugate_le_of_coboundary_preparedProof (hcomm : ∀ n m : N, n * m = m * n)
    (K : Subgroup G) (b : N)
    (hb : ∀ x : K, projection N H hc x = b⁻¹ * MulAut.conjNormal (x : G) b) :
    conjugate (b : G) K ≤ H := by
  rintro _ ⟨x, hx, rfl⟩
  apply (projection_eq_one_iff N H hc _).mp
  change projection N H hc ((b : G) * x * (b : G)⁻¹) = 1
  rw [projection_mul N H hc hcomm, projection_mul N H hc hcomm,
    projection_of_mem N H hc b, hb ⟨x, hx⟩]
  have ht (n : N) : MulAut.conjNormal (b : G) n = n := by
    apply Subtype.ext
    change (b : G) * n * (b : G)⁻¹ = n
    have he := congrArg Subtype.val (hcomm b n)
    change (b : G) * n = (n : G) * b at he
    rw [he]
    group
  rw [ht]
  have hi : projection N H hc (b : G)⁻¹ = b⁻¹ := projection_of_mem N H hc b⁻¹
  rw [hi, map_mul, MulAut.mul_apply, ht, map_inv]
  group



end AbelianComplement
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] (N H : @Subgroup.{u_1} G inst) [inst_1 : @Subgroup.Normal.{u_1} G inst N]
  (hc : @Subgroup.IsComplement'.{u_1} G inst N H)
  (hcomm :
    ∀
      (n m :
        @Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x),
      @Eq.{u_1 + 1}
        (@Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
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
          n m)
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
          m n))
  (K : @Subgroup.{u_1} G inst)
  (b :
    @Subtype.{u_1 + 1} G fun (x : G) =>
      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
  (hb :
    ∀
      (x :
        @Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K x),
      @Eq.{u_1 + 1}
        (@Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
        (@LocalConjugacy.Proof.LocalConjugacy.AbelianComplement.projection.{u_1} G inst N H hc
          (@Subtype.val.{u_1 + 1} G
            (fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                x)
            x))
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
          (@Inv.inv.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (@Subgroup.inv.{u_1} G inst N) b)
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
                    K x)
                x))
            b))),
  @LE.le.{u_1} (@Subgroup.{u_1} G inst)
    (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
    (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst
      (@Subtype.val.{u_1 + 1} G
        (fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
        b)
      K)
    H :=
  @LocalConjugacy.Proof.LocalConjugacy.AbelianComplement.conjugate_le_of_coboundary_preparedProof
