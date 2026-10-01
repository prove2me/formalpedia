-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.map_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:32:26.6023+00:00
-- url     : https://prove2.me/submissions/f751c0cd-235e-4116-905c-e03a7a5680a3

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

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]











namespace FiniteSylowSystem
open CategoryTheory















variable {p : ℕ} [Fact p.Prime]
variable (P : (U : OpenNormalSubgroup G) → Sylow p (G ⧸ U.toSubgroup))
variable (hP : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (P U).mapSurjective (transition_surjective h) = P V)



private theorem mem_subgroup (x : G) :
    x ∈ subgroup P ↔ ∀ U, QuotientGroup.mk' U.toSubgroup x ∈ P U := by
  simp only [subgroup, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl



include hP

private theorem map_transition (U V : OpenNormalSubgroup G) (h : U ≤ V) :
    (P U : Subgroup _).map (transition h) = (P V : Subgroup _) := by
  exact congrArg Sylow.toSubgroup (hP U V h)

private theorem mem_of_le {U V : OpenNormalSubgroup G} (h : U ≤ V) (x : G)
    (hx : QuotientGroup.mk' U.toSubgroup x ∈ P U) :
    QuotientGroup.mk' V.toSubgroup x ∈ P V := by
  have hy := Subgroup.mem_map_of_mem (transition h) hx
  rw [map_transition P hP U V h] at hy
  exact hy

private theorem map_subgroup_preparedProof (U : OpenNormalSubgroup G) :
    (subgroup P).map (QuotientGroup.mk' U.toSubgroup) = (P U : Subgroup _) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_subgroup P x).mp hx U
  · intro y hy
    let : Nonempty (OpenNormalSubgroup G) := ⟨U⟩
    let T : OpenNormalSubgroup G → Set G := fun V =>
      {x | QuotientGroup.mk' V.toSubgroup x ∈ P V ∧ QuotientGroup.mk' U.toSubgroup x = y}
    have hc : ∀ V, IsClosed (T V) := by
      intro V
      exact ((isClosed_discrete (P V).toSubgroup.carrier).preimage
        (continuous_quotient_mk' : Continuous (QuotientGroup.mk' V.toSubgroup))).inter
        (isClosed_eq (continuous_quotient_mk' : Continuous (QuotientGroup.mk' U.toSubgroup))
          continuous_const)
    have hn : ∀ V, (T V).Nonempty := by
      intro V
      have hymap : y ∈ (P (U ⊓ V)).toSubgroup.map
          (transition (show U ⊓ V ≤ U from inf_le_left)) := by
        rwa [map_transition P hP (U ⊓ V) U inf_le_left]
      obtain ⟨z, hz, hzy⟩ := hymap
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (U ⊓ V).toSubgroup z
      exact ⟨x, mem_of_le P hP inf_le_right x hz, hzy⟩
    have hd : Directed (· ⊇ ·) T := by
      intro V W
      refine ⟨V ⊓ W, ?_, ?_⟩
      · intro x hx
        exact ⟨mem_of_le P hP inf_le_left x hx.1, hx.2⟩
      · intro x hx
        exact ⟨mem_of_le P hP inf_le_right x hx.1, hx.2⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      T hd hn (fun V => (hc V).isCompact) hc
    have hx' : ∀ V, x ∈ T V := Set.mem_iInter.mp hx
    exact ⟨x, (mem_subgroup P x).mpr (fun V => (hx' V).1), (hx' U).2⟩

end FiniteSylowSystem





























end LocalConjugacy

end LocalConjugacy.Proof

end

universe u

theorem solution :
∀ {G : Type u} [inst : Group.{u} G] [inst_1 : TopologicalSpace.{u} G]
  [inst_2 : @LocalConjugacy.Proof.LocalConjugacy.Profinite.{u} G inst inst_1] {p : Nat} [inst_3 : Fact (Nat.Prime p)]
  (P :
    (U : @OpenNormalSubgroup.{u} G inst inst_1) →
      @Sylow.{u} p
        (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
          (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
        (@QuotientGroup.Quotient.group.{u} G inst
          (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
          (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U)))
  (hP :
    ∀ (U V : @OpenNormalSubgroup.{u} G inst inst_1)
      (h :
        @LE.le.{u} (@OpenNormalSubgroup.{u} G inst inst_1)
          (@Preorder.toLE.{u} (@OpenNormalSubgroup.{u} G inst inst_1)
            (@PartialOrder.toPreorder.{u} (@OpenNormalSubgroup.{u} G inst inst_1)
              (@OpenNormalSubgroup.instPartialOrderOpenNormalSubgroup.{u} G inst inst_1)))
          U V),
      @Eq.{u + 1}
        (@Sylow.{u} p
          (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 V)))
          (@QuotientGroup.Quotient.group.{u} G inst
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 V))
            (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 V)))
        (@Sylow.mapSurjective.{u, u} p
          (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
          (@QuotientGroup.Quotient.group.{u} G inst
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
            (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
          (@Subgroup.instFiniteQuotientOfSeparatelyContinuousMulOfCompactSpace.{u} G inst inst_1
            (@instSeparatelyContinuousMulOfContinuousMul.{u} G inst_1
              (@MulOne.toMul.{u} G
                (@MulOneClass.toMulOne.{u} G
                  (@Monoid.toMulOneClass.{u} G (@DivInvMonoid.toMonoid.{u} G (@Group.toDivInvMonoid.{u} G inst)))))
              (@IsTopologicalGroup.toContinuousMul.{u} G inst_1 inst
                (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u} G inst inst_1 inst_2)))
            (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toCompactSpace.{u} G inst inst_1 inst_2)
            (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
          (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 V)))
          (@QuotientGroup.Quotient.group.{u} G inst
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 V))
            (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 V))
          (@LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.transition.{u} G inst inst_1 U V h)
          (@LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.transition_surjective.{u} G inst inst_1 inst_2 U V h)
          inst_3 (P U))
        (P V))
  (U : @OpenNormalSubgroup.{u} G inst inst_1),
  @Eq.{u + 1}
    (@Subgroup.{u}
      (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
      (@QuotientGroup.Quotient.group.{u} G inst
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U)))
    (@Subgroup.map.{u, u} G inst
      (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
      (@QuotientGroup.Quotient.group.{u} G inst
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
      (@QuotientGroup.mk'.{u} G inst
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
      (@LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.subgroup.{u} G inst inst_1 p P))
    (@Sylow.toSubgroup.{u} p
      (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
      (@QuotientGroup.Quotient.group.{u} G inst
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
      (P U)) :=
  @LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.map_subgroup_preparedProof
