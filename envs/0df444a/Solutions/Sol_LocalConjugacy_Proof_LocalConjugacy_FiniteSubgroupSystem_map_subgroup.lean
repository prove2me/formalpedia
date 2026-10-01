-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.FiniteSubgroupSystem.map_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:32:25.552042+00:00
-- url     : https://prove2.me/submissions/9caea36f-7295-4f48-adb1-770e71e1424d

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

namespace FiniteSubgroupSystem
open FiniteSylowSystem
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
variable (S : (U : OpenNormalSubgroup G) → Subgroup (G ⧸ U.toSubgroup))
variable (hS : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (S U).map (transition h) = S V)







include hS

private theorem map_transition (U V : OpenNormalSubgroup G) (h : U ≤ V) :
    (S U : Subgroup _).map (transition h) = (S V : Subgroup _) := by
  exact hS U V h

private theorem mem_of_le {U V : OpenNormalSubgroup G} (h : U ≤ V) (x : G)
    (hx : QuotientGroup.mk' U.toSubgroup x ∈ S U) :
    QuotientGroup.mk' V.toSubgroup x ∈ S V := by
  have hy := Subgroup.mem_map_of_mem (transition h) hx
  rw [map_transition S hS U V h] at hy
  exact hy

private theorem map_subgroup_preparedProof (U : OpenNormalSubgroup G) :
    (subgroup S).map (QuotientGroup.mk' U.toSubgroup) = (S U : Subgroup _) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_subgroup S x).mp hx U
  · intro y hy
    let : Nonempty (OpenNormalSubgroup G) := ⟨U⟩
    let T : OpenNormalSubgroup G → Set G := fun V =>
      {x | QuotientGroup.mk' V.toSubgroup x ∈ S V ∧ QuotientGroup.mk' U.toSubgroup x = y}
    have hc : ∀ V, IsClosed (T V) := by
      intro V
      exact ((isClosed_discrete (S V).carrier).preimage
        (continuous_quotient_mk' : Continuous (QuotientGroup.mk' V.toSubgroup))).inter
        (isClosed_eq (continuous_quotient_mk' : Continuous (QuotientGroup.mk' U.toSubgroup))
          continuous_const)
    have hn : ∀ V, (T V).Nonempty := by
      intro V
      have hymap : y ∈ (S (U ⊓ V)).map
          (transition (show U ⊓ V ≤ U from inf_le_left)) := by
        rwa [map_transition S hS (U ⊓ V) U inf_le_left]
      obtain ⟨z, hz, hzy⟩ := hymap
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (U ⊓ V).toSubgroup z
      exact ⟨x, mem_of_le S hS inf_le_right x hz, hzy⟩
    have hd : Directed (· ⊇ ·) T := by
      intro V W
      refine ⟨V ⊓ W, ?_, ?_⟩
      · intro x hx
        exact ⟨mem_of_le S hS inf_le_left x hx.1, hx.2⟩
      · intro x hx
        exact ⟨mem_of_le S hS inf_le_right x hx.1, hx.2⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      T hd hn (fun V => (hc V).isCompact) hc
    have hx' : ∀ V, x ∈ T V := Set.mem_iInter.mp hx
    exact ⟨x, (mem_subgroup S x).mpr (fun V => (hx' V).1), (hx' U).2⟩


end FiniteSubgroupSystem

section ProfiniteHall
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
open FiniteSylowSystem
open scoped Pointwise





















namespace HallComplementSystem
open CategoryTheory
variable (hG : Prosupersolvable G) (n : ℕ) (P : Subgroup G)









end HallComplementSystem



end ProfiniteHall
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1]
  (S :
    (U : @OpenNormalSubgroup.{u_1} G inst inst_1) →
      @Subgroup.{u_1}
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
        (@QuotientGroup.Quotient.group.{u_1} G inst
          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
  (hS :
    ∀ (U V : @OpenNormalSubgroup.{u_1} G inst inst_1)
      (h :
        @LE.le.{u_1} (@OpenNormalSubgroup.{u_1} G inst inst_1)
          (@Preorder.toLE.{u_1} (@OpenNormalSubgroup.{u_1} G inst inst_1)
            (@PartialOrder.toPreorder.{u_1} (@OpenNormalSubgroup.{u_1} G inst inst_1)
              (@OpenNormalSubgroup.instPartialOrderOpenNormalSubgroup.{u_1} G inst inst_1)))
          U V),
      @Eq.{u_1 + 1}
        (@Subgroup.{u_1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
          (@QuotientGroup.Quotient.group.{u_1} G inst
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V)))
        (@Subgroup.map.{u_1, u_1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
          (@QuotientGroup.Quotient.group.{u_1} G inst
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
          (@QuotientGroup.Quotient.group.{u_1} G inst
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V))
          (@LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.transition.{u_1} G inst inst_1 U V h) (S U))
        (S V))
  (U : @OpenNormalSubgroup.{u_1} G inst inst_1),
  @Eq.{u_1 + 1}
    (@Subgroup.{u_1}
      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
      (@QuotientGroup.Quotient.group.{u_1} G inst
        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
    (@Subgroup.map.{u_1, u_1} G inst
      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
      (@QuotientGroup.Quotient.group.{u_1} G inst
        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
      (@QuotientGroup.mk'.{u_1} G inst
        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
      (@LocalConjugacy.Proof.LocalConjugacy.FiniteSubgroupSystem.subgroup.{u_1} G inst inst_1 S))
    (S U) :=
  @LocalConjugacy.Proof.LocalConjugacy.FiniteSubgroupSystem.map_subgroup_preparedProof
