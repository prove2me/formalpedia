-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.card_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:38:20.874759+00:00
-- url     : https://prove2.me/submissions/bf4d802e-d649-401b-a1df-5d60853000f4

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





private theorem mem_cocycleCentralizer (K : Subgroup J)
    (f : Cocycle (N := N) (⊤ : Subgroup J)) (n : N) :
    n ∈ cocycleCentralizer K f ↔
      ∀ x : K, f.toFun ⟨x, trivial⟩ * ((x : J) • n) * (f.toFun ⟨x, trivial⟩)⁻¹ = n := by
  simp only [cocycleCentralizer, Subgroup.mem_iInf]
  rfl

/-- A nonempty set of intertwiners is a torsor for the cocycle centralizer. -/
private theorem card_intertwiners_preparedProof {p : ℕ} [Fact p.Prime] [Finite N]
    (hN : IsPGroup p N) (K : Subgroup J)
    (f g : Cocycle (N := N) (⊤ : Subgroup J))
    (n₀ : N) (hn₀ : ∀ x : K, g.toFun ⟨x, trivial⟩ =
      n₀⁻¹ * f.toFun ⟨x, trivial⟩ * ((x : J) • n₀)) :
    letI := intertwiningAction f g
    ∃ k : ℕ, Nat.card (MulAction.fixedPoints K N) = p ^ k := by
  let a := MulDistribMulAction.toMulAut J N
  have hfg (x : K) : g.toFun ⟨x, trivial⟩ =
      n₀⁻¹ * f.toFun ⟨x, trivial⟩ * a x n₀ := hn₀ x
  letI := intertwiningAction f g
  let T := MulAction.fixedPoints K N
  have ht (n : N) : n ∈ T ↔ n * n₀⁻¹ ∈ cocycleCentralizer K f := by
    rw [mem_cocycleCentralizer]
    change (∀ x : K, f.toFun ⟨x, trivial⟩ * a x n * (g.toFun ⟨x, trivial⟩)⁻¹ = n) ↔
      ∀ x : K, f.toFun ⟨x, trivial⟩ * a x (n * n₀⁻¹) * (f.toFun ⟨x, trivial⟩)⁻¹ = n * n₀⁻¹
    simp only [map_mul, map_inv, hfg, mul_inv_rev, inv_inv]
    constructor
    · intro h x
      have he := congrArg (fun z => z * n₀⁻¹) (h x)
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using he
    · intro h x
      have he := congrArg (fun z => z * n₀) (h x)
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using he
  let e : T ≃ cocycleCentralizer K f :=
    { toFun := fun n => ⟨n.val * n₀⁻¹, (ht n.val).mp n.property⟩
      invFun := fun n => ⟨n.val * n₀, (ht _).mpr (by simpa using n.property)⟩
      left_inv := fun n => by apply Subtype.ext; simp
      right_inv := fun n => by apply Subtype.ext; simp }
  obtain ⟨k, hk⟩ := (hN.to_subgroup (cocycleCentralizer K f)).exists_card_eq
  exact ⟨k, (Nat.card_congr e).trans hk⟩



end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : TopologicalSpace.{u_2} N]
  [inst_4 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  {p : Nat} [Fact (Nat.Prime p)] [Finite.{u_2 + 1} N] (hN : @IsPGroup.{u_2} p N inst_1) (K : @Subgroup.{u_1} J inst)
  (f g :
    @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
  (n₀ : N)
  (hn₀ :
    ∀
      (x :
        @Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K x),
      @Eq.{u_2 + 1} N
        (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4
          (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) g
          (@Subtype.mk.{u_1 + 1} J
            (fun (x : J) =>
              @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst))
                (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) x)
            (@Subtype.val.{u_1 + 1} J
              (fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K
                  x)
              x)
            trivial))
        (@HMul.hMul.{u_2, u_2, u_2} N N N
          (@instHMul.{u_2} N
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
          (@HMul.hMul.{u_2, u_2, u_2} N N N
            (@instHMul.{u_2} N
              (@MulOne.toMul.{u_2} N
                (@MulOneClass.toMulOne.{u_2} N
                  (@Monoid.toMulOneClass.{u_2} N
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
            (@Inv.inv.{u_2} N
              (@InvOneClass.toInv.{u_2} N
                (@DivInvOneMonoid.toInvOneClass.{u_2} N
                  (@DivisionMonoid.toDivInvOneMonoid.{u_2} N (@Group.toDivisionMonoid.{u_2} N inst_1))))
              n₀)
            (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4
              (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) f
              (@Subtype.mk.{u_1 + 1} J
                (fun (x : J) =>
                  @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst))
                    (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) x)
                (@Subtype.val.{u_1 + 1} J
                  (fun (x : J) =>
                    @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J
                        (@Subgroup.instSetLike.{u_1} J inst))
                      K x)
                  x)
                trivial)))
          (@HSMul.hSMul.{u_1, u_2, u_2} J N N
            (@instHSMul.{u_1, u_2} J N
              (@SemigroupAction.toSMul.{u_1, u_2} J N
                (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
                (@MulAction.toSemigroupAction.{u_1, u_2} J N
                  (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                  (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
                    (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_4))))
            (@Subtype.val.{u_1 + 1} J
              (fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K
                  x)
              x)
            n₀))),
  @Exists.{1} Nat fun (k : Nat) =>
    @Eq.{1} Nat
      (Nat.card.{u_2}
        (@Set.Elem.{u_2} N
          (@MulAction.fixedPoints.{u_1, u_2}
            (@Subtype.{u_1 + 1} J fun (x : J) =>
              @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K
                x)
            N
            (@DivInvMonoid.toMonoid.{u_1}
              (@Subtype.{u_1 + 1} J fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K
                  x)
              (@Group.toDivInvMonoid.{u_1}
                (@Subtype.{u_1 + 1} J fun (x : J) =>
                  @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst))
                    K x)
                (@Subgroup.toGroup.{u_1} J inst K)))
            (@Subgroup.instMulAction.{u_1, u_2} J N inst
              (@LocalConjugacy.Proof.LocalConjugacy.intertwiningAction.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 f
                g)
              K))))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p k) :=
  @LocalConjugacy.Proof.LocalConjugacy.card_intertwiners_preparedProof
