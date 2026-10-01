-- Prove2me | solution 1 for LocalConjugacy.Proof.QuaternionComplements.locallyConjugate
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:44:16.574344+00:00
-- url     : https://prove2.me/submissions/414898ef-955c-404b-bec2-36f4c6243c76

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
import Theorems.Thm_LocalConjugacy_Proof_quaternion_sylow_coboundary

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section


/-! The two complements underlying the quaternion obstruction. Local conjugators
come from the Sylow coboundaries, while a finite certificate rules out a global
conjugator in the entire 48-element ambient group. -/
namespace LocalConjugacy.Proof.QuaternionComplements

set_option maxRecDepth 20000
set_option maxHeartbeats 0



















/-- A coboundary coefficient conjugates the canonical section to the sign graph
on the subgroup where the coboundary equation holds. -/
private theorem conjugation_certificate : ∀ n : Q8, ∀ s : S3,
    signValue s = n⁻¹ * quaternionAction s n →
    (SemidirectProduct.inl (φ := quaternionAction) n⁻¹) * SemidirectProduct.inr s *
      (SemidirectProduct.inl (φ := quaternionAction) n⁻¹)⁻¹ = signSection s := by decide

/-- Every prime admits conjugate Sylow subgroups of the two complements. The
surjective range restrictions transport an arbitrary Sylow of S₃ to each graph. -/
private theorem locallyConjugate_preparedProof :
    FiniteLocallyConjugate (quaternionComplement quaternionAction) secondComplement := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p S3 := Classical.choice Sylow.nonempty
  let i : S3 →* G := SemidirectProduct.inr
  let P₀ := P.mapSurjective i.rangeRestrict_surjective
  let P₁ := P.mapSurjective signSection.rangeRestrict_surjective
  let f : FiniteCocycle (quaternionAction.comp P.toSubgroup.subtype) :=
    ⟨fun x => signValue x.val, by
      intro x y
      exact congrArg SemidirectProduct.left (signSection.map_mul x.val y.val)⟩
  obtain ⟨n, hn⟩ := quaternion_sylow_coboundary p hp P f
  refine ⟨P₀, P₁, SemidirectProduct.inl n⁻¹, ?_⟩
  have h₀ : (P.toSubgroup.map i.rangeRestrict).map i.range.subtype =
      P.toSubgroup.map i := by rw [Subgroup.map_map]; rfl
  have h₁ : (P.toSubgroup.map signSection.rangeRestrict).map signSection.range.subtype =
      P.toSubgroup.map signSection := by rw [Subgroup.map_map]; rfl
  change conjugate (SemidirectProduct.inl n⁻¹)
    ((P.toSubgroup.map i.rangeRestrict).map i.range.subtype) =
    (P.toSubgroup.map signSection.rangeRestrict).map signSection.range.subtype
  rw [h₀, h₁]
  change (P.toSubgroup.map i).map
    (MulAut.conj (SemidirectProduct.inl (φ := quaternionAction) n⁻¹)).toMonoidHom =
    P.toSubgroup.map signSection
  apply le_antisymm
  · rintro x ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, (conjugation_certificate n s (hn ⟨s, hs⟩)).symm⟩
  · rintro x ⟨s, hs, rfl⟩
    refine ⟨i s, ⟨s, hs, rfl⟩, ?_⟩
    exact conjugation_certificate n s (hn ⟨s, hs⟩)





end LocalConjugacy.Proof.QuaternionComplements

end

theorem solution :
@LocalConjugacy.FiniteLocallyConjugate.{0}
  (@SemidirectProduct.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    LocalConjugacy.Proof.quaternionAction)
  (@SemidirectProduct.instGroup.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    LocalConjugacy.Proof.quaternionAction)
  (LocalConjugacy.quaternionComplement LocalConjugacy.Proof.quaternionAction)
  LocalConjugacy.Proof.QuaternionComplements.secondComplement :=
  @LocalConjugacy.Proof.QuaternionComplements.locallyConjugate_preparedProof
