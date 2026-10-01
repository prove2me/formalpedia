-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.procyclic_zpowers_closure
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:49:17.377043+00:00
-- url     : https://prove2.me/submissions/0049474f-8724-4def-a0d2-e927db30f75d

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

variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

private theorem procyclic_zpowers_closure_preparedProof (x : G) :
    Procyclic (Subgroup.zpowers x).topologicalClosure := by
  let Q := (Subgroup.zpowers x).topologicalClosure
  let y : Q := ⟨x, (Subgroup.zpowers x).le_topologicalClosure (Subgroup.mem_zpowers x)⟩
  refine ⟨y, ?_⟩
  rw [Subtype.dense_iff]
  have he : Subtype.val '' (Subgroup.zpowers y : Set Q) = (Subgroup.zpowers x : Set G) := by
    change ((Subgroup.zpowers y).map Q.subtype : Set G) = _
    rw [MonoidHom.map_zpowers]
    rfl
  change (Q : Set G) ⊆ closure (Subtype.val '' (Subgroup.zpowers y : Set Q))
  rw [he]
  exact fun _ hx => hx



end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [inst_2 : @LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (x : G),
  @LocalConjugacy.Proof.LocalConjugacy.Procyclic.{u_1}
    (@Subtype.{u_1 + 1} G fun (x_1 : G) =>
      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
        (@Subgroup.topologicalClosure.{u_1} G inst_1 inst
          (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u_1} G inst inst_1 inst_2)
          (@Subgroup.zpowers.{u_1} G inst x))
        x_1)
    (@Subgroup.toGroup.{u_1} G inst
      (@Subgroup.topologicalClosure.{u_1} G inst_1 inst
        (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u_1} G inst inst_1 inst_2)
        (@Subgroup.zpowers.{u_1} G inst x)))
    (@instTopologicalSpaceSubtype.{u_1} G
      (fun (x_1 : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
          (@Subgroup.topologicalClosure.{u_1} G inst_1 inst
            (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u_1} G inst inst_1 inst_2)
            (@Subgroup.zpowers.{u_1} G inst x))
          x_1)
      inst_1) :=
  @LocalConjugacy.Proof.LocalConjugacy.procyclic_zpowers_closure_preparedProof
