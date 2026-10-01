-- Prove2me | solution 1 for LocalConjugacy.counterexample_quaternion
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:48:23.788322+00:00
-- url     : https://prove2.me/submissions/ea786a95-b870-47f9-a118-36ae382b866b

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
import Theorems.Thm_LocalConjugacy_Proof_QuaternionCohomology_cohomology_card
import Theorems.Thm_LocalConjugacy_Proof_QuaternionComplements_locallyConjugate
import Theorems.Thm_LocalConjugacy_Proof_finiteH1_subsingleton_of_coboundaries
import Theorems.Thm_LocalConjugacy_Proof_quaternion_sylow_coboundary

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section


/-! Transport the explicit dihedral presentation to the draft's symmetric group.
The transport preserves the full cocycle quotient and all Sylow restrictions. -/
namespace LocalConjugacy.Proof

set_option maxRecDepth 20000
set_option maxHeartbeats 0











/-- Exactly two global classes survive the change of presentation. -/
private theorem quaternionH1_card : Nat.card (FiniteH1 quaternionAction) = 2 := by
  exact (Nat.card_congr (finiteH1DomainEquiv LocalConjugacy.QuaternionExample.action
    dihedralEquiv.symm)).symm.trans QuaternionCohomology.cohomology_card





/-- The restriction targets in the first counterexample are all singleton H¹ sets. -/
private theorem quaternion_sylow_H1 (p : ℕ) (hp : p.Prime) (P : Sylow p S3) :
    Subsingleton (FiniteH1 (quaternionAction.comp P.toSubgroup.subtype)) :=
  finiteH1_subsingleton_of_coboundaries _ (quaternion_sylow_coboundary p hp P)

end LocalConjugacy.Proof

end

section


/-! The two complements underlying the quaternion obstruction. Local conjugators
come from the Sylow coboundaries, while a finite certificate rules out a global
conjugator in the entire 48-element ambient group. -/
namespace LocalConjugacy.Proof.QuaternionComplements

set_option maxRecDepth 20000
set_option maxHeartbeats 0

















/-- The sign graph has trivial intersection with the quaternion kernel and,
with it, accounts for all 48 elements. -/
private theorem isComplement : (quaternionKernel quaternionAction).IsComplement' secondComplement := by
  apply Subgroup.isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide
  · apply disjoint_iff_inf_le.mpr
    exact (by decide : ∀ x : G,
      (x ∈ quaternionKernel quaternionAction ∧ x ∈ secondComplement) → x = 1)





/-- Exhaustion of all ambient conjugators rules out even inclusion of the
canonical complement in the sign graph. -/
private theorem no_global_conjugator : ¬ ∃ g : G, ∀ s : S3,
    g * SemidirectProduct.inr s * g⁻¹ ∈ secondComplement := by decide

/-- In particular the complements are not conjugate in the ambient group. -/
private theorem not_conjugate :
    ¬ Conjugate (quaternionComplement quaternionAction) secondComplement := by
  rintro ⟨g, hg⟩
  apply no_global_conjugator
  refine ⟨g, fun s => ?_⟩
  have hs : g * SemidirectProduct.inr s * g⁻¹ ∈
      conjugate g (quaternionComplement quaternionAction) :=
    ⟨SemidirectProduct.inr s, ⟨s, rfl⟩, rfl⟩
  rwa [hg] at hs

end LocalConjugacy.Proof.QuaternionComplements

end

section


/-! The first counterexample, including GL₂(F₃), the cohomology quotient, and
both the local and global claims about the concrete complements. -/
open LocalConjugacy

/-- The exact quaternion counterexample from the draft. -/
private theorem LocalConjugacy.counterexample_quaternion_preparedProof :
    ∃ a : S3 →* MulAut Q8,
      -- The action is realized in the matrix group named in the source.
      Nonempty ((Q8 ⋊[a] S3) ≃* GL (Fin 2) (ZMod 3)) ∧
      -- There are exactly two global cohomology classes.
      Nat.card (FiniteH1 a) = 2 ∧
      -- Every Sylow restriction has trivial first cohomology.
      (∀ (p : ℕ) (hp : p.Prime),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ P : Sylow p S3, Subsingleton (FiniteH1 (a.comp P.toSubgroup.subtype))) ∧
      -- The same action gives the locally conjugate, nonconjugate complements.
      ∃ J' : Subgroup (Q8 ⋊[a] S3),
        (quaternionKernel a).IsComplement' J' ∧
        FiniteLocallyConjugate (quaternionComplement a) J' ∧
        ¬ Conjugate (quaternionComplement a) J' := by
  -- All four assertions refer to the same explicitly constructed action.
  refine ⟨Proof.quaternionAction, ⟨Proof.quaternionGLEquiv⟩,
    Proof.quaternionH1_card, ?_, Proof.QuaternionComplements.secondComplement,
    Proof.QuaternionComplements.isComplement,
    Proof.QuaternionComplements.locallyConjugate,
    Proof.QuaternionComplements.not_conjugate⟩
  intro p hp
  exact Proof.quaternion_sylow_H1 p hp

end

theorem solution :
@Exists.{1}
  (@MonoidHom.{0, 0} LocalConjugacy.S3
    (@MulAut.{0} LocalConjugacy.Q8
      (@MulOne.toMul.{0} LocalConjugacy.Q8
        (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
          (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
              (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
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
                      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
          (@Group.toDivInvMonoid.{0}
            (@MulAut.{0} LocalConjugacy.Q8
              (@MulOne.toMul.{0} LocalConjugacy.Q8
                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                        (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
            (@MulAut.instGroup.{0} LocalConjugacy.Q8
              (@MulOne.toMul.{0} LocalConjugacy.Q8
                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                        (@QuaternionGroup.instGroup
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
  fun
    (a :
      @MonoidHom.{0, 0} LocalConjugacy.S3
        (@MulAut.{0} LocalConjugacy.Q8
          (@MulOne.toMul.{0} LocalConjugacy.Q8
            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
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
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))))) =>
  And
    (Nonempty.{1}
      (@MulEquiv.{0, 0}
        (@SemidirectProduct.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
          (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) a)
        (@Matrix.GeneralLinearGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@Semifield.toDivisionSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Nat.fact_prime_three)))))
        (@SemidirectProduct.instMul.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
          (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) a)
        (@Units.instMul.{0}
          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@Semiring.toMonoid.{0}
            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (@Matrix.semiring.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@Semifield.toDivisionSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      Nat.fact_prime_three))))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
    (And
      (@Eq.{1} Nat
        (Nat.card.{0}
          (@LocalConjugacy.FiniteH1.{0, 0} LocalConjugacy.S3 LocalConjugacy.Q8
            (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (And
        (∀ (p : Nat) (hp : Nat.Prime p)
          (P :
            @Sylow.{0} p LocalConjugacy.S3
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))),
          Subsingleton.{1}
            (@LocalConjugacy.FiniteH1.{0, 0}
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
                        (@Equiv.Perm.permGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
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
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                (@MulOneClass.toMulOne.{0}
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
                a
                (@Subgroup.subtype.{0} LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    P)))))
        (@Exists.{1}
          (@Subgroup.{0}
            (@SemidirectProduct.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
              (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) a)
            (@SemidirectProduct.instGroup.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
              (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) a))
          fun
            (J' :
              @Subgroup.{0}
                (@SemidirectProduct.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
                  (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) a)
                (@SemidirectProduct.instGroup.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
                  (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) a)) =>
          And
            (@Subgroup.IsComplement'.{0}
              (@SemidirectProduct.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
                (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) a)
              (@SemidirectProduct.instGroup.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
                (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) a)
              (LocalConjugacy.quaternionKernel a) J')
            (And
              (@LocalConjugacy.FiniteLocallyConjugate.{0}
                (@SemidirectProduct.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
                  (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) a)
                (@SemidirectProduct.instGroup.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
                  (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) a)
                (LocalConjugacy.quaternionComplement a) J')
              (Not
                (@LocalConjugacy.Conjugate.{0}
                  (@SemidirectProduct.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
                    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) a)
                  (@SemidirectProduct.instGroup.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
                    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) a)
                  (LocalConjugacy.quaternionComplement a) J')))))) :=
  @LocalConjugacy.counterexample_quaternion_preparedProof
