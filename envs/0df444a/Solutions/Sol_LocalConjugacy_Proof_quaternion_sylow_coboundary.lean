-- Prove2me | solution 1 for LocalConjugacy.Proof.quaternion_sylow_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:37:24.375214+00:00
-- url     : https://prove2.me/submissions/7db198da-23fb-4b9f-886b-9c57e8e9f2fe

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
import Theorems.Thm_LocalConjugacy_Proof_QuaternionCohomology_proper_subgroup_coboundary

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section


/-!
The finite cohomology assertions for the quaternion counterexample. The original
cocycle calculation is promoted to the actual quotient H¹. A small subgroup
classification proves vanishing on every proper subgroup, hence every Sylow.
-/
namespace LocalConjugacy.Proof.QuaternionCohomology
open LocalConjugacy.QuaternionExample
set_option maxRecDepth 20000
set_option maxHeartbeats 0












/-- A group of order six cannot be a p-group for any prime p: both two and
three divide its cardinality, whereas a p-power has only one prime divisor. -/
private theorem not_pGroup_card_six {A : Type*} [Group A] [Finite A]
    (hc : Nat.card A = 6) (p : ℕ) (hp : p.Prime) : ¬ IsPGroup p A := by
  letI : Fact p.Prime := ⟨hp⟩
  intro h
  obtain ⟨k, hk⟩ := h.exists_card_eq
  have hd2 : 2 ∣ p ^ k := by rw [← hk, hc]; decide
  have hd3 : 3 ∣ p ^ k := by rw [← hk, hc]; decide
  have h2 := (Nat.dvd_prime hp).mp (Nat.prime_two.dvd_of_dvd_pow hd2)
  have h3 := (Nat.dvd_prime hp).mp ((by decide : Nat.Prime 3).dvd_of_dvd_pow hd3)
  omega

end LocalConjugacy.Proof.QuaternionCohomology

end

section


/-! Transport the explicit dihedral presentation to the draft's symmetric group.
The transport preserves the full cocycle quotient and all Sylow restrictions. -/
namespace LocalConjugacy.Proof

set_option maxRecDepth 20000
set_option maxHeartbeats 0













/-- Every cocycle on any Sylow subgroup is a coboundary. Pull back to a proper
subgroup of the dihedral model and apply the proved subgroup classification. -/
private theorem quaternion_sylow_coboundary_preparedProof (p : ℕ) (hp : p.Prime) (P : Sylow p S3)
    (f : FiniteCocycle (quaternionAction.comp P.toSubgroup.subtype)) :
    ∃ n : Q8, ∀ x : P, f.val x = n⁻¹ * quaternionAction x.val n := by
  letI : Fact p.Prime := ⟨hp⟩
  have hP : P.toSubgroup ≠ ⊤ := by
    intro he
    have h : IsPGroup p (⊤ : Subgroup S3) := he ▸ P.isPGroup'
    exact QuaternionCohomology.not_pGroup_card_six
      (by rw [Nat.card_eq_fintype_card]; decide) p hp (h.of_equiv Subgroup.topEquiv)
  let L : Subgroup (DihedralGroup 3) := P.toSubgroup.comap dihedralEquiv.toMonoidHom
  have hL : L ≠ ⊤ := by
    intro he
    apply hP
    apply top_unique
    intro x _
    have hx : dihedralEquiv.symm x ∈ L := he ▸ Subgroup.mem_top _
    simpa [L] using hx
  let fL : FiniteCocycle (LocalConjugacy.QuaternionExample.action.comp L.subtype) :=
    ⟨fun x => f.val ⟨dihedralEquiv x, x.property⟩, by
      intro x y
      have h := f.property ⟨dihedralEquiv x, x.property⟩ ⟨dihedralEquiv y, y.property⟩
      have he : (⟨dihedralEquiv ↑(x * y), (x * y).property⟩ : P.toSubgroup) =
          ⟨dihedralEquiv x, x.property⟩ * ⟨dihedralEquiv y, y.property⟩ :=
        Subtype.ext (dihedralEquiv.map_mul x.val y.val)
      dsimp only
      rw [he]
      change _ = _ * (LocalConjugacy.QuaternionExample.action x.val) _
      change _ = _ * (LocalConjugacy.QuaternionExample.action
        (dihedralEquiv.symm (dihedralEquiv x.val))) _ at h
      rwa [dihedralEquiv.symm_apply_apply] at h⟩
  obtain ⟨n, hn⟩ := QuaternionCohomology.proper_subgroup_coboundary L hL fL
  refine ⟨n, fun x => ?_⟩
  have hx : dihedralEquiv.symm x.val ∈ L := by simpa [L] using x.property
  have h := hn ⟨dihedralEquiv.symm x.val, hx⟩
  change f.val ⟨dihedralEquiv (dihedralEquiv.symm x.val), _⟩ =
    n⁻¹ * quaternionAction x.val n at h
  change f.val (⟨x.val, x.property⟩ : P.toSubgroup) = _
  simpa only [dihedralEquiv.apply_symm_apply] using h





end LocalConjugacy.Proof

end

theorem solution :
∀ (p : Nat) (hp : Nat.Prime p)
  (P :
    @Sylow.{0} p LocalConjugacy.S3
      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
  (f :
    @LocalConjugacy.FiniteCocycle.{0, 0}
      (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
        @Membership.mem.{0, 0} LocalConjugacy.S3
          (@Subgroup.{0} LocalConjugacy.S3
            (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@SetLike.instMembership.{0, 0}
            (@Subgroup.{0} LocalConjugacy.S3
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
            LocalConjugacy.S3
            (@Subgroup.instSetLike.{0} LocalConjugacy.S3
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
          (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
            (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
          x)
      LocalConjugacy.Q8
      (@Subgroup.toGroup.{0} LocalConjugacy.S3
        (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
          (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P))
      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@MonoidHom.comp.{0, 0, 0}
        (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
          @Membership.mem.{0, 0} LocalConjugacy.S3
            (@Subgroup.{0} LocalConjugacy.S3
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
            (@SetLike.instMembership.{0, 0}
              (@Subgroup.{0} LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              LocalConjugacy.S3
              (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
            (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
            x)
        LocalConjugacy.S3
        (@MulAut.{0} LocalConjugacy.Q8
          (@MulOne.toMul.{0} LocalConjugacy.Q8
            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
        (@MulOneClass.toMulOne.{0}
          (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
            @Membership.mem.{0, 0} LocalConjugacy.S3
              (@Subgroup.{0} LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                LocalConjugacy.S3
                (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
              (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
              x)
          (@Monoid.toMulOneClass.{0}
            (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
              @Membership.mem.{0, 0} LocalConjugacy.S3
                (@Subgroup.{0} LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                (@SetLike.instMembership.{0, 0}
                  (@Subgroup.{0} LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  LocalConjugacy.S3
                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
                x)
            (@DivInvMonoid.toMonoid.{0}
              (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                @Membership.mem.{0, 0} LocalConjugacy.S3
                  (@Subgroup.{0} LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    LocalConjugacy.S3
                    (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
                  x)
              (@Group.toDivInvMonoid.{0}
                (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                  @Membership.mem.{0, 0} LocalConjugacy.S3
                    (@Subgroup.{0} LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    (@SetLike.instMembership.{0, 0}
                      (@Subgroup.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                      LocalConjugacy.S3
                      (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                    (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
                    x)
                (@Subgroup.toGroup.{0} LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    P))))))
        (@MulOneClass.toMulOne.{0} LocalConjugacy.S3
          (@Monoid.toMulOneClass.{0} LocalConjugacy.S3
            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.S3
              (@Group.toDivInvMonoid.{0} LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
        (@MulOneClass.toMulOne.{0}
          (@MulAut.{0} LocalConjugacy.Q8
            (@MulOne.toMul.{0} LocalConjugacy.Q8
              (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
          (@Monoid.toMulOneClass.{0}
            (@MulAut.{0} LocalConjugacy.Q8
              (@MulOne.toMul.{0} LocalConjugacy.Q8
                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                        (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
            (@DivInvMonoid.toMonoid.{0}
              (@MulAut.{0} LocalConjugacy.Q8
                (@MulOne.toMul.{0} LocalConjugacy.Q8
                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                          (@QuaternionGroup.instGroup
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
              (@Group.toDivInvMonoid.{0}
                (@MulAut.{0} LocalConjugacy.Q8
                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                (@MulAut.instGroup.{0} LocalConjugacy.Q8
                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))))
        LocalConjugacy.Proof.quaternionAction
        (@Subgroup.subtype.{0} LocalConjugacy.S3
          (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
            (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)))),
  @Exists.{1} LocalConjugacy.Q8 fun (n : LocalConjugacy.Q8) =>
    ∀
      (x :
        @Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
          @Membership.mem.{0, 0} LocalConjugacy.S3
            (@Sylow.{0} p LocalConjugacy.S3
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
            (@SetLike.instMembership.{0, 0}
              (@Sylow.{0} p LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              LocalConjugacy.S3
              (@Sylow.instSetLike.{0} p LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
            P x),
      @Eq.{1} LocalConjugacy.Q8
        (@Subtype.val.{1}
          ((@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
              @Membership.mem.{0, 0} LocalConjugacy.S3
                (@Subgroup.{0} LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                (@SetLike.instMembership.{0, 0}
                  (@Subgroup.{0} LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  LocalConjugacy.S3
                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
                x) →
            LocalConjugacy.Q8)
          (fun
              (f :
                (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                    @Membership.mem.{0, 0} LocalConjugacy.S3
                      (@Subgroup.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                      (@SetLike.instMembership.{0, 0}
                        (@Subgroup.{0} LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        LocalConjugacy.S3
                        (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                      (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        P)
                      x) →
                  LocalConjugacy.Q8) =>
            ∀
              (x y :
                @Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                  @Membership.mem.{0, 0} LocalConjugacy.S3
                    (@Subgroup.{0} LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    (@SetLike.instMembership.{0, 0}
                      (@Subgroup.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                      LocalConjugacy.S3
                      (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                    (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
                    x),
              @Eq.{1} LocalConjugacy.Q8
                (f
                  (@HMul.hMul.{0, 0, 0}
                    (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                      @Membership.mem.{0, 0} LocalConjugacy.S3
                        (@Subgroup.{0} LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          LocalConjugacy.S3
                          (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                        (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          P)
                        x)
                    (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                      @Membership.mem.{0, 0} LocalConjugacy.S3
                        (@Subgroup.{0} LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          LocalConjugacy.S3
                          (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                        (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          P)
                        x)
                    (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                      @Membership.mem.{0, 0} LocalConjugacy.S3
                        (@Subgroup.{0} LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          LocalConjugacy.S3
                          (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                        (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          P)
                        x)
                    (@instHMul.{0}
                      (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                        @Membership.mem.{0, 0} LocalConjugacy.S3
                          (@Subgroup.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          (@SetLike.instMembership.{0, 0}
                            (@Subgroup.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            LocalConjugacy.S3
                            (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                          (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            P)
                          x)
                      (@MulOne.toMul.{0}
                        (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                          @Membership.mem.{0, 0} LocalConjugacy.S3
                            (@Subgroup.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              LocalConjugacy.S3
                              (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                            (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              P)
                            x)
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                            @Membership.mem.{0, 0} LocalConjugacy.S3
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                LocalConjugacy.S3
                                (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                              (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                P)
                              x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                              @Membership.mem.{0, 0} LocalConjugacy.S3
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  LocalConjugacy.S3
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  P)
                                x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                @Membership.mem.{0, 0} LocalConjugacy.S3
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    LocalConjugacy.S3
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P)
                                  x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.S3
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                      LocalConjugacy.S3
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                    (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      P)
                                    x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P))))))))
                    x y))
                (@HMul.hMul.{0, 0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8 LocalConjugacy.Q8
                  (@instHMul.{0} LocalConjugacy.Q8
                    (@MulOne.toMul.{0} LocalConjugacy.Q8
                      (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                        (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                          (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                            (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                              (@QuaternionGroup.instGroup
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                  (f x)
                  (@DFunLike.coe.{1, 1, 1}
                    (@MulEquiv.{0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8
                      (@MulOne.toMul.{0} LocalConjugacy.Q8
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                (@QuaternionGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                      (@MulOne.toMul.{0} LocalConjugacy.Q8
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                (@QuaternionGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                    LocalConjugacy.Q8 (fun (x : LocalConjugacy.Q8) => LocalConjugacy.Q8)
                    (@EquivLike.toFunLike.{1, 1, 1}
                      (@MulEquiv.{0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8
                        (@MulOne.toMul.{0} LocalConjugacy.Q8
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                        (@MulOne.toMul.{0} LocalConjugacy.Q8
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      LocalConjugacy.Q8 LocalConjugacy.Q8
                      (@MulEquiv.instEquivLike.{0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8
                        (@MulOne.toMul.{0} LocalConjugacy.Q8
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                        (@MulOne.toMul.{0} LocalConjugacy.Q8
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
                    (@DFunLike.coe.{1, 1, 1}
                      (@MonoidHom.{0, 0}
                        (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                          @Membership.mem.{0, 0} LocalConjugacy.S3
                            (@Subgroup.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              LocalConjugacy.S3
                              (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                            (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              P)
                            x)
                        (@MulAut.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                            @Membership.mem.{0, 0} LocalConjugacy.S3
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                LocalConjugacy.S3
                                (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                              (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                P)
                              x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                              @Membership.mem.{0, 0} LocalConjugacy.S3
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  LocalConjugacy.S3
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  P)
                                x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                @Membership.mem.{0, 0} LocalConjugacy.S3
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    LocalConjugacy.S3
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P)
                                  x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.S3
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                      LocalConjugacy.S3
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                    (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      P)
                                    x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P))))))
                        (@MulOneClass.toMulOne.{0}
                          (@MulAut.{0} LocalConjugacy.Q8
                            (@MulOne.toMul.{0} LocalConjugacy.Q8
                              (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                      (@QuaternionGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                          (@Monoid.toMulOneClass.{0}
                            (@MulAut.{0} LocalConjugacy.Q8
                              (@MulOne.toMul.{0} LocalConjugacy.Q8
                                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                        (@QuaternionGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                            (@DivInvMonoid.toMonoid.{0}
                              (@MulAut.{0} LocalConjugacy.Q8
                                (@MulOne.toMul.{0} LocalConjugacy.Q8
                                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                          (@QuaternionGroup.instGroup
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                              (@Group.toDivInvMonoid.{0}
                                (@MulAut.{0} LocalConjugacy.Q8
                                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                                (@MulAut.instGroup.{0} LocalConjugacy.Q8
                                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
                      (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                        @Membership.mem.{0, 0} LocalConjugacy.S3
                          (@Subgroup.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          (@SetLike.instMembership.{0, 0}
                            (@Subgroup.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            LocalConjugacy.S3
                            (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                          (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            P)
                          x)
                      (fun
                          (x :
                            @Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                              @Membership.mem.{0, 0} LocalConjugacy.S3
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  LocalConjugacy.S3
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  P)
                                x) =>
                        @MulAut.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      (@MonoidHom.instFunLike.{0, 0}
                        (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                          @Membership.mem.{0, 0} LocalConjugacy.S3
                            (@Subgroup.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              LocalConjugacy.S3
                              (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                            (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              P)
                            x)
                        (@MulAut.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                            @Membership.mem.{0, 0} LocalConjugacy.S3
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                LocalConjugacy.S3
                                (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                              (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                P)
                              x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                              @Membership.mem.{0, 0} LocalConjugacy.S3
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  LocalConjugacy.S3
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  P)
                                x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                @Membership.mem.{0, 0} LocalConjugacy.S3
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    LocalConjugacy.S3
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P)
                                  x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.S3
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                      LocalConjugacy.S3
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                    (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      P)
                                    x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P))))))
                        (@MulOneClass.toMulOne.{0}
                          (@MulAut.{0} LocalConjugacy.Q8
                            (@MulOne.toMul.{0} LocalConjugacy.Q8
                              (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                      (@QuaternionGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                          (@Monoid.toMulOneClass.{0}
                            (@MulAut.{0} LocalConjugacy.Q8
                              (@MulOne.toMul.{0} LocalConjugacy.Q8
                                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                        (@QuaternionGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                            (@DivInvMonoid.toMonoid.{0}
                              (@MulAut.{0} LocalConjugacy.Q8
                                (@MulOne.toMul.{0} LocalConjugacy.Q8
                                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                          (@QuaternionGroup.instGroup
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                              (@Group.toDivInvMonoid.{0}
                                (@MulAut.{0} LocalConjugacy.Q8
                                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                                (@MulAut.instGroup.{0} LocalConjugacy.Q8
                                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
                      (@MonoidHom.comp.{0, 0, 0}
                        (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                          @Membership.mem.{0, 0} LocalConjugacy.S3
                            (@Subgroup.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              LocalConjugacy.S3
                              (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                            (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              P)
                            x)
                        LocalConjugacy.S3
                        (@MulAut.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                            @Membership.mem.{0, 0} LocalConjugacy.S3
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                LocalConjugacy.S3
                                (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                              (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                P)
                              x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                              @Membership.mem.{0, 0} LocalConjugacy.S3
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  LocalConjugacy.S3
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  P)
                                x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                @Membership.mem.{0, 0} LocalConjugacy.S3
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    LocalConjugacy.S3
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P)
                                  x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.S3
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                      LocalConjugacy.S3
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                    (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      P)
                                    x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P))))))
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.S3
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.S3
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.S3
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@MulAut.{0} LocalConjugacy.Q8
                            (@MulOne.toMul.{0} LocalConjugacy.Q8
                              (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                      (@QuaternionGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                          (@Monoid.toMulOneClass.{0}
                            (@MulAut.{0} LocalConjugacy.Q8
                              (@MulOne.toMul.{0} LocalConjugacy.Q8
                                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                        (@QuaternionGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                            (@DivInvMonoid.toMonoid.{0}
                              (@MulAut.{0} LocalConjugacy.Q8
                                (@MulOne.toMul.{0} LocalConjugacy.Q8
                                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                          (@QuaternionGroup.instGroup
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                              (@Group.toDivInvMonoid.{0}
                                (@MulAut.{0} LocalConjugacy.Q8
                                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                                (@MulAut.instGroup.{0} LocalConjugacy.Q8
                                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))))
                        LocalConjugacy.Proof.quaternionAction
                        (@Subgroup.subtype.{0} LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            P)))
                      x)
                    (f y))))
          f x)
        (@HMul.hMul.{0, 0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8 LocalConjugacy.Q8
          (@instHMul.{0} LocalConjugacy.Q8
            (@MulOne.toMul.{0} LocalConjugacy.Q8
              (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
          (@Inv.inv.{0} LocalConjugacy.Q8
            (@InvOneClass.toInv.{0} LocalConjugacy.Q8
              (@DivInvOneMonoid.toInvOneClass.{0} LocalConjugacy.Q8
                (@DivisionMonoid.toDivInvOneMonoid.{0} LocalConjugacy.Q8
                  (@Group.toDivisionMonoid.{0} LocalConjugacy.Q8
                    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            n)
          (@DFunLike.coe.{1, 1, 1}
            (@MulEquiv.{0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8
              (@MulOne.toMul.{0} LocalConjugacy.Q8
                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                        (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@MulOne.toMul.{0} LocalConjugacy.Q8
                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                        (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
            LocalConjugacy.Q8 (fun (x : LocalConjugacy.Q8) => LocalConjugacy.Q8)
            (@EquivLike.toFunLike.{1, 1, 1}
              (@MulEquiv.{0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8
                (@MulOne.toMul.{0} LocalConjugacy.Q8
                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                          (@QuaternionGroup.instGroup
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@MulOne.toMul.{0} LocalConjugacy.Q8
                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                          (@QuaternionGroup.instGroup
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
              LocalConjugacy.Q8 LocalConjugacy.Q8
              (@MulEquiv.instEquivLike.{0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8
                (@MulOne.toMul.{0} LocalConjugacy.Q8
                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                          (@QuaternionGroup.instGroup
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@MulOne.toMul.{0} LocalConjugacy.Q8
                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                          (@QuaternionGroup.instGroup
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
            (@DFunLike.coe.{1, 1, 1}
              (@MonoidHom.{0, 0} LocalConjugacy.S3
                (@MulAut.{0} LocalConjugacy.Q8
                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                (@MulOneClass.toMulOne.{0} LocalConjugacy.S3
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.S3
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.S3
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
                (@MulOneClass.toMulOne.{0}
                  (@MulAut.{0} LocalConjugacy.Q8
                    (@MulOne.toMul.{0} LocalConjugacy.Q8
                      (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                        (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                          (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                            (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                              (@QuaternionGroup.instGroup
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                  (@Monoid.toMulOneClass.{0}
                    (@MulAut.{0} LocalConjugacy.Q8
                      (@MulOne.toMul.{0} LocalConjugacy.Q8
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                (@QuaternionGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                    (@DivInvMonoid.toMonoid.{0}
                      (@MulAut.{0} LocalConjugacy.Q8
                        (@MulOne.toMul.{0} LocalConjugacy.Q8
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      (@Group.toDivInvMonoid.{0}
                        (@MulAut.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulAut.instGroup.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
              LocalConjugacy.S3
              (fun (x : LocalConjugacy.S3) =>
                @MulAut.{0} LocalConjugacy.Q8
                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
              (@MonoidHom.instFunLike.{0, 0} LocalConjugacy.S3
                (@MulAut.{0} LocalConjugacy.Q8
                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                (@MulOneClass.toMulOne.{0} LocalConjugacy.S3
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.S3
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.S3
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
                (@MulOneClass.toMulOne.{0}
                  (@MulAut.{0} LocalConjugacy.Q8
                    (@MulOne.toMul.{0} LocalConjugacy.Q8
                      (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                        (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                          (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                            (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                              (@QuaternionGroup.instGroup
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                  (@Monoid.toMulOneClass.{0}
                    (@MulAut.{0} LocalConjugacy.Q8
                      (@MulOne.toMul.{0} LocalConjugacy.Q8
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                (@QuaternionGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                    (@DivInvMonoid.toMonoid.{0}
                      (@MulAut.{0} LocalConjugacy.Q8
                        (@MulOne.toMul.{0} LocalConjugacy.Q8
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      (@Group.toDivInvMonoid.{0}
                        (@MulAut.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulAut.instGroup.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
              LocalConjugacy.Proof.quaternionAction
              (@Subtype.val.{1} LocalConjugacy.S3
                (fun (x : LocalConjugacy.S3) =>
                  @Membership.mem.{0, 0} LocalConjugacy.S3
                    (@Sylow.{0} p LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    (@SetLike.instMembership.{0, 0}
                      (@Sylow.{0} p LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                      LocalConjugacy.S3
                      (@Sylow.instSetLike.{0} p LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                    P x)
                x))
            n)) :=
  @LocalConjugacy.Proof.quaternion_sylow_coboundary_preparedProof
