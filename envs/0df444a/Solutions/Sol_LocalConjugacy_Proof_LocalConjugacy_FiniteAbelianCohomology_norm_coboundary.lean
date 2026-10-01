-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.FiniteAbelianCohomology.norm_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:32:23.335268+00:00
-- url     : https://prove2.me/submissions/67668baf-e47a-4706-90d3-e036239396a3

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
namespace FiniteAbelianCohomology

variable {J A : Type*} [Group J] [CommGroup A]



private theorem norm_coboundary_preparedProof [Fintype J] (a : J →* MulAut A) (f : J → A)
    (hf : CocycleFn a f) (P : Subgroup J) (n : A)
    (hP : ∀ x : P, f x * a x n = n) :
    ∃ b : A, ∀ x : J, f x ^ P.index = b⁻¹ * a x b := by
  classical
  let u : J ⧸ P → A := Quotient.lift (fun x : J => f x * a x n) (by
    intro x y hxy
    have hm : x⁻¹ * y ∈ P := QuotientGroup.leftRel_apply.mp hxy
    have he := hP ⟨x⁻¹ * y, hm⟩
    have hy : x * (x⁻¹ * y) = y := by group
    calc
      f x * a x n = f x * a x (f (x⁻¹ * y) * a (x⁻¹ * y) n) := by rw [he]
      _ = f (x * (x⁻¹ * y)) * a (x * (x⁻¹ * y)) n := by
        rw [hf x (x⁻¹ * y)]
        simp only [map_mul, MulAut.mul_apply, mul_assoc]
      _ = f y * a y n := by rw [hy])
  have hu (x y : J) : u (x • (QuotientGroup.mk y : J ⧸ P)) =
      f x * a x (u (QuotientGroup.mk y)) := by
    change f (x * y) * a (x * y) n = f x * a x (f y * a y n)
    rw [hf]
    simp only [map_mul, MulAut.mul_apply]
    group
  let b : A := ∏ q : J ⧸ P, u q
  have hb (x : J) : b = f x ^ P.index * a x b := by
    calc
      b = ∏ q : J ⧸ P, u (x • q) := by
        exact (Fintype.prod_equiv (MulAction.toPerm x) _ _ (fun q => rfl)).symm
      _ = ∏ q : J ⧸ P, (f x * a x (u q)) := by
        apply Finset.prod_congr rfl
        intro q _
        induction q using Quotient.inductionOn with
        | h y => exact hu x y
      _ = f x ^ P.index * a x b := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          ← map_prod]
        rw [Fintype.card_eq_nat_card]
        rfl
  refine ⟨b⁻¹, fun x => ?_⟩
  have he := hb x
  simp only [inv_inv, map_inv]
  exact (eq_mul_inv_iff_mul_eq.mpr he.symm)



end FiniteAbelianCohomology
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {A : Type u_2} [inst : Group.{u_1} J] [inst_1 : CommGroup.{u_2} A] [Fintype.{u_1} J]
  (a :
    @MonoidHom.{u_1, u_2} J
      (@MulAut.{u_2} A
        (@MulOne.toMul.{u_2} A
          (@MulOneClass.toMulOne.{u_2} A
            (@Monoid.toMulOneClass.{u_2} A
              (@DivInvMonoid.toMonoid.{u_2} A (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
      (@MulOneClass.toMulOne.{u_1} J
        (@Monoid.toMulOneClass.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
      (@MulOneClass.toMulOne.{u_2}
        (@MulAut.{u_2} A
          (@MulOne.toMul.{u_2} A
            (@MulOneClass.toMulOne.{u_2} A
              (@Monoid.toMulOneClass.{u_2} A
                (@DivInvMonoid.toMonoid.{u_2} A (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
        (@Monoid.toMulOneClass.{u_2}
          (@MulAut.{u_2} A
            (@MulOne.toMul.{u_2} A
              (@MulOneClass.toMulOne.{u_2} A
                (@Monoid.toMulOneClass.{u_2} A
                  (@DivInvMonoid.toMonoid.{u_2} A
                    (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
          (@DivInvMonoid.toMonoid.{u_2}
            (@MulAut.{u_2} A
              (@MulOne.toMul.{u_2} A
                (@MulOneClass.toMulOne.{u_2} A
                  (@Monoid.toMulOneClass.{u_2} A
                    (@DivInvMonoid.toMonoid.{u_2} A
                      (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
            (@Group.toDivInvMonoid.{u_2}
              (@MulAut.{u_2} A
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
              (@MulAut.instGroup.{u_2} A
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))))))
  (f : J → A)
  (hf : @LocalConjugacy.Proof.LocalConjugacy.CocycleFn.{u_1, u_2} J A inst (@CommGroup.toGroup.{u_2} A inst_1) a f)
  (P : @Subgroup.{u_1} J inst) (n : A)
  (hP :
    ∀
      (x :
        @Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) P x),
      @Eq.{u_2 + 1} A
        (@HMul.hMul.{u_2, u_2, u_2} A A A
          (@instHMul.{u_2} A
            (@MulOne.toMul.{u_2} A
              (@MulOneClass.toMulOne.{u_2} A
                (@Monoid.toMulOneClass.{u_2} A
                  (@DivInvMonoid.toMonoid.{u_2} A
                    (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
          (f
            (@Subtype.val.{u_1 + 1} J
              (fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) P
                  x)
              x))
          (@DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1}
            (@MulEquiv.{u_2, u_2} A A
              (@MulOne.toMul.{u_2} A
                (@MulOneClass.toMulOne.{u_2} A
                  (@Monoid.toMulOneClass.{u_2} A
                    (@DivInvMonoid.toMonoid.{u_2} A
                      (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
              (@MulOne.toMul.{u_2} A
                (@MulOneClass.toMulOne.{u_2} A
                  (@Monoid.toMulOneClass.{u_2} A
                    (@DivInvMonoid.toMonoid.{u_2} A
                      (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
            A (fun (x : A) => A)
            (@EquivLike.toFunLike.{u_2 + 1, u_2 + 1, u_2 + 1}
              (@MulEquiv.{u_2, u_2} A A
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
              A A
              (@MulEquiv.instEquivLike.{u_2, u_2} A A
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))
            (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
              (@MonoidHom.{u_1, u_2} J
                (@MulAut.{u_2} A
                  (@MulOne.toMul.{u_2} A
                    (@MulOneClass.toMulOne.{u_2} A
                      (@Monoid.toMulOneClass.{u_2} A
                        (@DivInvMonoid.toMonoid.{u_2} A
                          (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                (@MulOneClass.toMulOne.{u_1} J
                  (@Monoid.toMulOneClass.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
                (@MulOneClass.toMulOne.{u_2}
                  (@MulAut.{u_2} A
                    (@MulOne.toMul.{u_2} A
                      (@MulOneClass.toMulOne.{u_2} A
                        (@Monoid.toMulOneClass.{u_2} A
                          (@DivInvMonoid.toMonoid.{u_2} A
                            (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                  (@Monoid.toMulOneClass.{u_2}
                    (@MulAut.{u_2} A
                      (@MulOne.toMul.{u_2} A
                        (@MulOneClass.toMulOne.{u_2} A
                          (@Monoid.toMulOneClass.{u_2} A
                            (@DivInvMonoid.toMonoid.{u_2} A
                              (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                    (@DivInvMonoid.toMonoid.{u_2}
                      (@MulAut.{u_2} A
                        (@MulOne.toMul.{u_2} A
                          (@MulOneClass.toMulOne.{u_2} A
                            (@Monoid.toMulOneClass.{u_2} A
                              (@DivInvMonoid.toMonoid.{u_2} A
                                (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                      (@Group.toDivInvMonoid.{u_2}
                        (@MulAut.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                        (@MulAut.instGroup.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))))))
              J
              (fun (x : J) =>
                @MulAut.{u_2} A
                  (@MulOne.toMul.{u_2} A
                    (@MulOneClass.toMulOne.{u_2} A
                      (@Monoid.toMulOneClass.{u_2} A
                        (@DivInvMonoid.toMonoid.{u_2} A
                          (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
              (@MonoidHom.instFunLike.{u_1, u_2} J
                (@MulAut.{u_2} A
                  (@MulOne.toMul.{u_2} A
                    (@MulOneClass.toMulOne.{u_2} A
                      (@Monoid.toMulOneClass.{u_2} A
                        (@DivInvMonoid.toMonoid.{u_2} A
                          (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                (@MulOneClass.toMulOne.{u_1} J
                  (@Monoid.toMulOneClass.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
                (@MulOneClass.toMulOne.{u_2}
                  (@MulAut.{u_2} A
                    (@MulOne.toMul.{u_2} A
                      (@MulOneClass.toMulOne.{u_2} A
                        (@Monoid.toMulOneClass.{u_2} A
                          (@DivInvMonoid.toMonoid.{u_2} A
                            (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                  (@Monoid.toMulOneClass.{u_2}
                    (@MulAut.{u_2} A
                      (@MulOne.toMul.{u_2} A
                        (@MulOneClass.toMulOne.{u_2} A
                          (@Monoid.toMulOneClass.{u_2} A
                            (@DivInvMonoid.toMonoid.{u_2} A
                              (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                    (@DivInvMonoid.toMonoid.{u_2}
                      (@MulAut.{u_2} A
                        (@MulOne.toMul.{u_2} A
                          (@MulOneClass.toMulOne.{u_2} A
                            (@Monoid.toMulOneClass.{u_2} A
                              (@DivInvMonoid.toMonoid.{u_2} A
                                (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                      (@Group.toDivInvMonoid.{u_2}
                        (@MulAut.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                        (@MulAut.instGroup.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))))))
              a
              (@Subtype.val.{u_1 + 1} J
                (fun (x : J) =>
                  @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst))
                    P x)
                x))
            n))
        n),
  @Exists.{u_2 + 1} A fun (b : A) =>
    ∀ (x : J),
      @Eq.{u_2 + 1} A
        (@HPow.hPow.{u_2, 0, u_2} A Nat A
          (@instHPow.{u_2, 0} A Nat
            (@NPow.toPow.{u_2} A
              (@Monoid.toNPow.{u_2} A
                (@DivInvMonoid.toMonoid.{u_2} A (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
          (f x) (@Subgroup.index.{u_1} J inst P))
        (@HMul.hMul.{u_2, u_2, u_2} A A A
          (@instHMul.{u_2} A
            (@MulOne.toMul.{u_2} A
              (@MulOneClass.toMulOne.{u_2} A
                (@Monoid.toMulOneClass.{u_2} A
                  (@DivInvMonoid.toMonoid.{u_2} A
                    (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
          (@Inv.inv.{u_2} A
            (@InvOneClass.toInv.{u_2} A
              (@DivInvOneMonoid.toInvOneClass.{u_2} A
                (@DivisionMonoid.toDivInvOneMonoid.{u_2} A
                  (@DivisionCommMonoid.toDivisionMonoid.{u_2} A (@CommGroup.toDivisionCommMonoid.{u_2} A inst_1)))))
            b)
          (@DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1}
            (@MulEquiv.{u_2, u_2} A A
              (@MulOne.toMul.{u_2} A
                (@MulOneClass.toMulOne.{u_2} A
                  (@Monoid.toMulOneClass.{u_2} A
                    (@DivInvMonoid.toMonoid.{u_2} A
                      (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
              (@MulOne.toMul.{u_2} A
                (@MulOneClass.toMulOne.{u_2} A
                  (@Monoid.toMulOneClass.{u_2} A
                    (@DivInvMonoid.toMonoid.{u_2} A
                      (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
            A (fun (x : A) => A)
            (@EquivLike.toFunLike.{u_2 + 1, u_2 + 1, u_2 + 1}
              (@MulEquiv.{u_2, u_2} A A
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
              A A
              (@MulEquiv.instEquivLike.{u_2, u_2} A A
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))
            (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
              (@MonoidHom.{u_1, u_2} J
                (@MulAut.{u_2} A
                  (@MulOne.toMul.{u_2} A
                    (@MulOneClass.toMulOne.{u_2} A
                      (@Monoid.toMulOneClass.{u_2} A
                        (@DivInvMonoid.toMonoid.{u_2} A
                          (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                (@MulOneClass.toMulOne.{u_1} J
                  (@Monoid.toMulOneClass.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
                (@MulOneClass.toMulOne.{u_2}
                  (@MulAut.{u_2} A
                    (@MulOne.toMul.{u_2} A
                      (@MulOneClass.toMulOne.{u_2} A
                        (@Monoid.toMulOneClass.{u_2} A
                          (@DivInvMonoid.toMonoid.{u_2} A
                            (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                  (@Monoid.toMulOneClass.{u_2}
                    (@MulAut.{u_2} A
                      (@MulOne.toMul.{u_2} A
                        (@MulOneClass.toMulOne.{u_2} A
                          (@Monoid.toMulOneClass.{u_2} A
                            (@DivInvMonoid.toMonoid.{u_2} A
                              (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                    (@DivInvMonoid.toMonoid.{u_2}
                      (@MulAut.{u_2} A
                        (@MulOne.toMul.{u_2} A
                          (@MulOneClass.toMulOne.{u_2} A
                            (@Monoid.toMulOneClass.{u_2} A
                              (@DivInvMonoid.toMonoid.{u_2} A
                                (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                      (@Group.toDivInvMonoid.{u_2}
                        (@MulAut.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                        (@MulAut.instGroup.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))))))
              J
              (fun (x : J) =>
                @MulAut.{u_2} A
                  (@MulOne.toMul.{u_2} A
                    (@MulOneClass.toMulOne.{u_2} A
                      (@Monoid.toMulOneClass.{u_2} A
                        (@DivInvMonoid.toMonoid.{u_2} A
                          (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
              (@MonoidHom.instFunLike.{u_1, u_2} J
                (@MulAut.{u_2} A
                  (@MulOne.toMul.{u_2} A
                    (@MulOneClass.toMulOne.{u_2} A
                      (@Monoid.toMulOneClass.{u_2} A
                        (@DivInvMonoid.toMonoid.{u_2} A
                          (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                (@MulOneClass.toMulOne.{u_1} J
                  (@Monoid.toMulOneClass.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
                (@MulOneClass.toMulOne.{u_2}
                  (@MulAut.{u_2} A
                    (@MulOne.toMul.{u_2} A
                      (@MulOneClass.toMulOne.{u_2} A
                        (@Monoid.toMulOneClass.{u_2} A
                          (@DivInvMonoid.toMonoid.{u_2} A
                            (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                  (@Monoid.toMulOneClass.{u_2}
                    (@MulAut.{u_2} A
                      (@MulOne.toMul.{u_2} A
                        (@MulOneClass.toMulOne.{u_2} A
                          (@Monoid.toMulOneClass.{u_2} A
                            (@DivInvMonoid.toMonoid.{u_2} A
                              (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                    (@DivInvMonoid.toMonoid.{u_2}
                      (@MulAut.{u_2} A
                        (@MulOne.toMul.{u_2} A
                          (@MulOneClass.toMulOne.{u_2} A
                            (@Monoid.toMulOneClass.{u_2} A
                              (@DivInvMonoid.toMonoid.{u_2} A
                                (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                      (@Group.toDivInvMonoid.{u_2}
                        (@MulAut.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                        (@MulAut.instGroup.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))))))
              a x)
            b)) :=
  @LocalConjugacy.Proof.LocalConjugacy.FiniteAbelianCohomology.norm_coboundary_preparedProof
