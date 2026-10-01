-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.AbelianComplement.projection_mul
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:32:22.389224+00:00
-- url     : https://prove2.me/submissions/991d8d9d-1a75-4c27-9a16-426f244ac1be

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









private theorem projection_mul_preparedProof (hcomm : ∀ n m : N, n * m = m * n) (x y : G) :
    projection N H hc (x * y) = projection N H hc x *
      MulAut.conjNormal x (projection N H hc y) := by
  let nx := projection N H hc x
  let ny := projection N H hc y
  let hx : H := (hc.equiv x).2
  let hy : H := (hc.equiv y).2
  have hxe : (nx : G) * hx = x := hc.equiv_fst_mul_equiv_snd x
  have hye : (ny : G) * hy = y := hc.equiv_fst_mul_equiv_snd y
  have he : ((MulAut.conjNormal x ny * nx : N) : G) * (hx * hy : H) = x * y := by
    change (x * ny * x⁻¹ * nx) * (hx * hy) = x * y
    calc
      (x * ny * x⁻¹ * nx) * (hx * hy) = x * ny * x⁻¹ * ((nx : G) * hx) * hy := by group
      _ = x * y := by rw [hxe, ← hye]; group
  have hf := congrArg (fun z => (hc.equiv z).1) he
  rw [show ((MulAut.conjNormal x ny * nx : N) : G) * (hx * hy : H) =
      hc.equiv.symm (MulAut.conjNormal x ny * nx, hx * hy) from rfl,
    hc.equiv.apply_symm_apply] at hf
  exact hf.symm.trans (hcomm _ _)







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
  (x y : G),
  @Eq.{u_1 + 1}
    (@Subtype.{u_1 + 1} G fun (x : G) =>
      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
    (@LocalConjugacy.Proof.LocalConjugacy.AbelianComplement.projection.{u_1} G inst N H hc
      (@HMul.hMul.{u_1, u_1, u_1} G G G
        (@instHMul.{u_1} G
          (@MulOne.toMul.{u_1} G
            (@MulOneClass.toMulOne.{u_1} G
              (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))))
        x y))
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
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
        (@Subgroup.mul.{u_1} G inst N))
      (@LocalConjugacy.Proof.LocalConjugacy.AbelianComplement.projection.{u_1} G inst N H hc x)
      (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
        (@MulEquiv.{u_1, u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subgroup.mul.{u_1} G inst N) (@Subgroup.mul.{u_1} G inst N))
        (@Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
        (fun
            (x :
              @Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x) =>
          @Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
        (@EquivLike.toFunLike.{u_1 + 1, u_1 + 1, u_1 + 1}
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
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@MulEquiv.instEquivLike.{u_1, u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (@Subgroup.mul.{u_1} G inst N) (@Subgroup.mul.{u_1} G inst N)))
        (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
          (@MonoidHom.{u_1, u_1} G
            (@MulAut.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x)
              (@Subgroup.mul.{u_1} G inst N))
            (@MulOneClass.toMulOne.{u_1} G
              (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
            (@MulOneClass.toMulOne.{u_1}
              (@MulAut.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
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
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x)
              (@Subgroup.mul.{u_1} G inst N))
          (@MonoidHom.instFunLike.{u_1, u_1} G
            (@MulAut.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                  x)
              (@Subgroup.mul.{u_1} G inst N))
            (@MulOneClass.toMulOne.{u_1} G
              (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
            (@MulOneClass.toMulOne.{u_1}
              (@MulAut.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
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
          (@MulAut.conjNormal.{u_1} G inst N inst_1) x)
        (@LocalConjugacy.Proof.LocalConjugacy.AbelianComplement.projection.{u_1} G inst N H hc y))) :=
  @LocalConjugacy.Proof.LocalConjugacy.AbelianComplement.projection_mul_preparedProof
