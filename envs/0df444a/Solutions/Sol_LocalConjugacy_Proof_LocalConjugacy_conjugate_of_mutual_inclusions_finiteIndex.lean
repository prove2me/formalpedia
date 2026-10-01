-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.conjugate_of_mutual_inclusions_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:45:54.453322+00:00
-- url     : https://prove2.me/submissions/fae1dafd-732f-425a-aa13-b2983c170edb

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

/-! The reductions needed to run Proposition 3.2's induction on `|N|`
while the ambient profinite group is allowed to be infinite. -/

namespace LocalConjugacy

section Algebra
variable {G : Type*} [Group G]







private theorem conjugate_of_mutual_inclusions_finiteIndex_preparedProof (H K : Subgroup G) [H.FiniteIndex]
    [K.FiniteIndex] (hHK : ∃ g : G, conjugate g H ≤ K)
    (hKH : ∃ g : G, conjugate g K ≤ H) : Conjugate H K := by
  obtain ⟨g, hg⟩ := hHK
  obtain ⟨k, hk⟩ := hKH
  have hgi : (conjugate g H).index = H.index := Subgroup.index_map_equiv H (MulAut.conj g)
  have hki : (conjugate k K).index = K.index := Subgroup.index_map_equiv K (MulAut.conj k)
  letI : (conjugate g H).FiniteIndex := ⟨hgi ▸ Subgroup.FiniteIndex.index_ne_zero⟩
  letI : (conjugate k K).FiniteIndex := ⟨hki ▸ Subgroup.FiniteIndex.index_ne_zero⟩
  refine ⟨g, eq_of_le_of_not_lt hg ?_⟩
  intro hlt
  have h₁ := Subgroup.index_strictAnti hlt
  have h₂ := Subgroup.index_antitone hk
  rw [hgi] at h₁
  rw [hki] at h₂
  omega

end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [Profinite G] [TopologicalSpace F] [Profinite F]







end Topology

section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]









end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] (H K : @Subgroup.{u_1} G inst) [@Subgroup.FiniteIndex.{u_1} G inst H]
  [@Subgroup.FiniteIndex.{u_1} G inst K]
  (hHK :
    @Exists.{u_1 + 1} G fun (g : G) =>
      @LE.le.{u_1} (@Subgroup.{u_1} G inst)
        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
        (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst g H) K)
  (hKH :
    @Exists.{u_1 + 1} G fun (g : G) =>
      @LE.le.{u_1} (@Subgroup.{u_1} G inst)
        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
        (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst g K) H),
  @LocalConjugacy.Proof.LocalConjugacy.Conjugate.{u_1} G inst H K :=
  @LocalConjugacy.Proof.LocalConjugacy.conjugate_of_mutual_inclusions_finiteIndex_preparedProof
