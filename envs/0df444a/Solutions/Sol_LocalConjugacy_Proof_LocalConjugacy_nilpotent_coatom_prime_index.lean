-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.nilpotent_coatom_prime_index
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:01:10.658713+00:00
-- url     : https://prove2.me/submissions/8e728d42-2bdc-4f88-941f-52bc744da688

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

/-- Maximal subgroups of a finite nilpotent group have prime index. This is
the finite induction step used in the nilpotent case of Lemma 1.2. -/
private theorem nilpotent_coatom_prime_index_preparedProof {J : Type*} [Group J] [Finite J]
    [Group.IsNilpotent J] (K : Subgroup J) (hK : IsCoatom K) :
    K.Normal ∧ K.index.Prime := by
  have hn : K.Normal := (Group.isNilpotent_of_finite_tfae.out 0 2 rfl rfl).mp
    inferInstance K hK
  letI := hn
  letI : Nontrivial (J ⧸ K) := QuotientGroup.nontrivial_iff.mpr hK.1
  let π := QuotientGroup.mk' K
  letI : IsSimpleGroup (J ⧸ K) :=
    { eq_bot_or_eq_top_of_normal := fun D _ => by
        have hle : K ≤ D.comap π := by
          simpa only [π, QuotientGroup.ker_mk'] using Subgroup.ker_le_comap π D
        rcases eq_or_lt_of_le hle with he | he
        · left
          apply Subgroup.comap_injective (QuotientGroup.mk'_surjective K)
          change D.comap π = π.ker
          simpa only [π, QuotientGroup.ker_mk'] using he.symm
        · right
          apply Subgroup.comap_injective (QuotientGroup.mk'_surjective K)
          rw [Subgroup.comap_top]
          exact hK.2 _ he }
  exact ⟨hn, IsSimpleGroup.prime_card (α := J ⧸ K)⟩



universe u v





end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {J : Type u_1} [inst : Group.{u_1} J] [Finite.{u_1 + 1} J] [@Group.IsNilpotent.{u_1} J inst]
  (K : @Subgroup.{u_1} J inst)
  (hK :
    @IsCoatom.{u_1} (@Subgroup.{u_1} J inst)
      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst))
      (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
        (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instCompleteLattice.{u_1} J inst)))
      K),
  And (@Subgroup.Normal.{u_1} J inst K) (Nat.Prime (@Subgroup.index.{u_1} J inst K)) :=
  @LocalConjugacy.Proof.LocalConjugacy.nilpotent_coatom_prime_index_preparedProof
