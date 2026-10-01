-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.relIndex_sup_dvd_card
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:23:00.317117+00:00
-- url     : https://prove2.me/submissions/ec26626c-52f6-4614-8fe2-aa8c94d8b426

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_index_eq_relIndex_of_supplements

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Algebra
variable {G F : Type*} [Group G] [Group F]

















end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [Profinite G] [TopologicalSpace F] [Finite F] [DiscreteTopology F]





end Topology

section Finite
variable {G : Type*} [Group G] [Finite G]



private theorem index_dvd_card_of_supplements (N H : Subgroup G) [N.Normal]
    (hs : Supplements N H) : H.index ∣ Nat.card N := by
  rw [index_eq_relIndex_of_supplements N H hs]
  exact H.relIndex_dvd_card N



end Finite
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open scoped Pointwise

section Algebra
variable {G F : Type*} [Group G] [Group F]













end Algebra

section Finite
variable {G : Type*} [Group G] [Finite G]



private theorem relIndex_sup_dvd_card_preparedProof (A H : Subgroup G) [A.Normal] :
    H.relIndex (A ⊔ H) ∣ Nat.card A := by
  let L := A ⊔ H
  have hs : Supplements (A.subgroupOf L) (H.subgroupOf L) := by
    intro x
    have hm : (x : G) ∈ (A : Set G) * (H : Set G) := by
      rw [← Subgroup.normal_mul]
      exact x.property
    obtain ⟨a, ha, h, hh, he⟩ := hm
    exact ⟨⟨a, (show A ≤ L from le_sup_left) ha⟩, ha,
      ⟨h, (show H ≤ L from le_sup_right) hh⟩, hh, Subtype.ext he⟩
  have hd := index_dvd_card_of_supplements (A.subgroupOf L) (H.subgroupOf L) hs
  have hc : Nat.card (A.subgroupOf L) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show A ≤ L from le_sup_left)).toEquiv
  rwa [hc] at hd











end Finite
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G] (A H : @Subgroup.{u_1} G inst)
  [@Subgroup.Normal.{u_1} G inst A],
  @Dvd.dvd.{0} Nat Nat.instDvd
    (@Subgroup.relIndex.{u_1} G inst H
      (@Max.max.{u_1} (@Subgroup.{u_1} G inst)
        (@SemilatticeSup.toMax.{u_1} (@Subgroup.{u_1} G inst)
          (@Lattice.toSemilatticeSup.{u_1} (@Subgroup.{u_1} G inst)
            (@ConditionallyCompleteLattice.toLattice.{u_1} (@Subgroup.{u_1} G inst)
              (@CompleteLattice.toConditionallyCompleteLattice.{u_1} (@Subgroup.{u_1} G inst)
                (@Subgroup.instCompleteLattice.{u_1} G inst)))))
        A H))
    (Nat.card.{u_1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) A x)) :=
  @LocalConjugacy.Proof.LocalConjugacy.relIndex_sup_dvd_card_preparedProof
