-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.primaryDecomposition_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:58:59.998872+00:00
-- url     : https://prove2.me/submissions/896ed4c0-2d64-4f61-b163-1976d365f416

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

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]



/-- The first clause of primary decomposition requires no finiteness,
nilpotence, or solvability assumption. -/
private theorem primary_restriction_is_stable (P : PrimeDivisor J → Subgroup J)
    (f : Cocycle (N := N) (⊤ : Subgroup J)) (p : PrimeDivisor J) :
    InvariantUnder ⊤ (P p) (restrictCocycle le_top f) :=
  invariant_restriction (P p) f

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Products
variable {J : Type*} [Group J] [TopologicalSpace J]
  {ι : Type*} {N : ι → Type*} [∀ i, Group (N i)] [∀ i, TopologicalSpace (N i)]
  [∀ i, MulDistribMulAction J (N i)]

namespace Cocycle





end Cocycle







end Products

section Coefficients
variable {J N M : Type*} [Group J] [Group N] [Group M]
  [TopologicalSpace J] [TopologicalSpace N] [TopologicalSpace M]
  [MulDistribMulAction J N] [MulDistribMulAction J M]

namespace Cocycle



end Cocycle



private theorem invariant_mapCoefficient {L K : Subgroup J} {f : Cocycle (N := N) K}
    (h : InvariantUnder L K f) (e : N →* M) (he : Continuous e)
    (ha : ∀ (j : J) (n : N), e (j • n) = j • e n) :
    InvariantUnder L K (f.mapCoefficient e he ha) := by
  intro j hj
  obtain ⟨n, hn⟩ := h j hj
  refine ⟨e n, fun x hx hjx => ?_⟩
  change j • e (f.toFun ⟨j⁻¹ * x * j, hjx⟩) = _
  rw [← ha, hn, e.map_mul, e.map_mul, e.map_inv, ha]
  rfl

/-- Transport primary decomposition across an equivariant continuous group
isomorphism of the coefficient groups. -/
private theorem primaryDecomposition_of_equiv_preparedProof (P : PrimeDivisor J → Subgroup J)
    (e : N ≃* M) (he : Continuous e) (hei : Continuous e.symm)
    (ha : ∀ (j : J) (n : N), e (j • n) = j • e n)
    (h : PrimaryDecomposition (N := M) P) : PrimaryDecomposition (N := N) P := by
  have hai (j : J) (m : M) : e.symm (j • m) = j • e.symm m := by
    apply e.injective
    rw [e.apply_symm_apply, ha, e.apply_symm_apply]
  refine ⟨primary_restriction_is_stable P, ?_, ?_⟩
  · intro f g hr
    have hh := h.2.1 (f.mapCoefficient e.toMonoidHom he ha)
      (g.mapCoefficient e.toMonoidHom he ha) (fun p => by
        obtain ⟨n, hn⟩ := hr p
        refine ⟨e n, fun x => ?_⟩
        change e (g.toFun ⟨x, trivial⟩) = (e n)⁻¹ * e (f.toFun ⟨x, trivial⟩) * ((x : J) • e n)
        rw [hn x, e.map_mul, e.map_mul, e.map_inv, ha])
    obtain ⟨n, hn⟩ := hh
    refine ⟨e.symm n, fun x => ?_⟩
    apply e.injective
    have hx := hn x
    change e (g.toFun x) = n⁻¹ * e (f.toFun x) * ((x : J) • n) at hx
    simpa only [map_mul, map_inv, ha, e.apply_symm_apply] using hx
  · intro f hf
    obtain ⟨g, hg⟩ := h.2.2 (fun p => (f p).mapCoefficient e.toMonoidHom he ha)
      (fun p => invariant_mapCoefficient (hf p) e.toMonoidHom he ha)
    refine ⟨g.mapCoefficient e.symm.toMonoidHom hei hai, fun p => ?_⟩
    obtain ⟨n, hn⟩ := hg p
    refine ⟨e.symm n, fun x => ?_⟩
    have hh := congrArg e.symm (hn x)
    simpa only [Cocycle.mapCoefficient, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulEquiv.symm_apply_apply, map_mul, map_inv, hai] using hh

end Coefficients
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2 u_3

theorem solution :
∀ {J : Type u_1} {N : Type u_2} {M : Type u_3} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : Group.{u_3} M]
  [inst_3 : TopologicalSpace.{u_1} J] [inst_4 : TopologicalSpace.{u_2} N] [inst_5 : TopologicalSpace.{u_3} M]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [inst_7 :
    @MulDistribMulAction.{u_1, u_3} J M (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))]
  (P : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_3 → @Subgroup.{u_1} J inst)
  (e :
    @MulEquiv.{u_2, u_3} N M
      (@MulOne.toMul.{u_2} N
        (@MulOneClass.toMulOne.{u_2} N
          (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
      (@MulOne.toMul.{u_3} M
        (@MulOneClass.toMulOne.{u_3} M
          (@Monoid.toMulOneClass.{u_3} M (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
  (he :
    @Continuous.{u_2, u_3} N M inst_4 inst_5
      (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
        (@MulEquiv.{u_2, u_3} N M
          (@MulOne.toMul.{u_2} N
            (@MulOneClass.toMulOne.{u_2} N
              (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
          (@MulOne.toMul.{u_3} M
            (@MulOneClass.toMulOne.{u_3} M
              (@Monoid.toMulOneClass.{u_3} M (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
        N (fun (x : N) => M)
        (@EquivLike.toFunLike.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
          (@MulEquiv.{u_2, u_3} N M
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
            (@MulOne.toMul.{u_3} M
              (@MulOneClass.toMulOne.{u_3} M
                (@Monoid.toMulOneClass.{u_3} M
                  (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
          N M
          (@MulEquiv.instEquivLike.{u_2, u_3} N M
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
            (@MulOne.toMul.{u_3} M
              (@MulOneClass.toMulOne.{u_3} M
                (@Monoid.toMulOneClass.{u_3} M
                  (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))))
        e))
  (hei :
    @Continuous.{u_3, u_2} M N inst_5 inst_4
      (@DFunLike.coe.{max (u_3 + 1) (u_2 + 1), u_3 + 1, u_2 + 1}
        (@MulEquiv.{u_3, u_2} M N
          (@MulOne.toMul.{u_3} M
            (@MulOneClass.toMulOne.{u_3} M
              (@Monoid.toMulOneClass.{u_3} M (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))
          (@MulOne.toMul.{u_2} N
            (@MulOneClass.toMulOne.{u_2} N
              (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
        M (fun (x : M) => N)
        (@EquivLike.toFunLike.{max (u_3 + 1) (u_2 + 1), u_3 + 1, u_2 + 1}
          (@MulEquiv.{u_3, u_2} M N
            (@MulOne.toMul.{u_3} M
              (@MulOneClass.toMulOne.{u_3} M
                (@Monoid.toMulOneClass.{u_3} M
                  (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
          M N
          (@MulEquiv.instEquivLike.{u_3, u_2} M N
            (@MulOne.toMul.{u_3} M
              (@MulOneClass.toMulOne.{u_3} M
                (@Monoid.toMulOneClass.{u_3} M
                  (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))))
        (@MulEquiv.symm.{u_2, u_3} N M
          (@MulOne.toMul.{u_2} N
            (@MulOneClass.toMulOne.{u_2} N
              (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
          (@MulOne.toMul.{u_3} M
            (@MulOneClass.toMulOne.{u_3} M
              (@Monoid.toMulOneClass.{u_3} M (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))
          e)))
  (ha :
    ∀ (j : J) (n : N),
      @Eq.{u_3 + 1} M
        (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
          (@MulEquiv.{u_2, u_3} N M
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
            (@MulOne.toMul.{u_3} M
              (@MulOneClass.toMulOne.{u_3} M
                (@Monoid.toMulOneClass.{u_3} M
                  (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
          N (fun (x : N) => M)
          (@EquivLike.toFunLike.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
            (@MulEquiv.{u_2, u_3} N M
              (@MulOne.toMul.{u_2} N
                (@MulOneClass.toMulOne.{u_2} N
                  (@Monoid.toMulOneClass.{u_2} N
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
              (@MulOne.toMul.{u_3} M
                (@MulOneClass.toMulOne.{u_3} M
                  (@Monoid.toMulOneClass.{u_3} M
                    (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
            N M
            (@MulEquiv.instEquivLike.{u_2, u_3} N M
              (@MulOne.toMul.{u_2} N
                (@MulOneClass.toMulOne.{u_2} N
                  (@Monoid.toMulOneClass.{u_2} N
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
              (@MulOne.toMul.{u_3} M
                (@MulOneClass.toMulOne.{u_3} M
                  (@Monoid.toMulOneClass.{u_3} M
                    (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))))
          e
          (@HSMul.hSMul.{u_1, u_2, u_2} J N N
            (@instHSMul.{u_1, u_2} J N
              (@SemigroupAction.toSMul.{u_1, u_2} J N
                (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
                (@MulAction.toSemigroupAction.{u_1, u_2} J N
                  (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                  (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
                    (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6))))
            j n))
        (@HSMul.hSMul.{u_1, u_3, u_3} J M M
          (@instHSMul.{u_1, u_3} J M
            (@SemigroupAction.toSMul.{u_1, u_3} J M
              (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
              (@MulAction.toSemigroupAction.{u_1, u_3} J M
                (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                (@MulDistribMulAction.toMulAction.{u_1, u_3} J M
                  (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                  (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)) inst_7))))
          j
          (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
            (@MulEquiv.{u_2, u_3} N M
              (@MulOne.toMul.{u_2} N
                (@MulOneClass.toMulOne.{u_2} N
                  (@Monoid.toMulOneClass.{u_2} N
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
              (@MulOne.toMul.{u_3} M
                (@MulOneClass.toMulOne.{u_3} M
                  (@Monoid.toMulOneClass.{u_3} M
                    (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
            N (fun (x : N) => M)
            (@EquivLike.toFunLike.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
              (@MulEquiv.{u_2, u_3} N M
                (@MulOne.toMul.{u_2} N
                  (@MulOneClass.toMulOne.{u_2} N
                    (@Monoid.toMulOneClass.{u_2} N
                      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
                (@MulOne.toMul.{u_3} M
                  (@MulOneClass.toMulOne.{u_3} M
                    (@Monoid.toMulOneClass.{u_3} M
                      (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
              N M
              (@MulEquiv.instEquivLike.{u_2, u_3} N M
                (@MulOne.toMul.{u_2} N
                  (@MulOneClass.toMulOne.{u_2} N
                    (@Monoid.toMulOneClass.{u_2} N
                      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
                (@MulOne.toMul.{u_3} M
                  (@MulOneClass.toMulOne.{u_3} M
                    (@Monoid.toMulOneClass.{u_3} M
                      (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))))
            e n)))
  (h : @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, u_3} J M inst inst_2 inst_3 inst_5 inst_7 P),
  @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, u_2} J N inst inst_1 inst_3 inst_4 inst_6 P :=
  @LocalConjugacy.Proof.LocalConjugacy.primaryDecomposition_of_equiv_preparedProof
