-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.supersolvable_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:04:47.969722+00:00
-- url     : https://prove2.me/submissions/b918f2a2-95d2-46f7-aa71-ebc2f59c4556

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_cyclic_step_comap

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy



/-- Supersolvability passes to subgroups by intersecting the invariant series. -/
private theorem supersolvable_subgroup_preparedProof {G : Type*} [Group G] (hG : Supersolvable G)
    (H : Subgroup G) : Supersolvable H := by
  obtain ⟨n, s, h0, hn, hm, hnormal, hstep⟩ := hG
  refine ⟨n, fun i => (s i).comap H.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [h0]
    exact H.subtype.ker_eq_bot Subtype.val_injective
  · simp only [hn, Subgroup.comap_top]
  · exact fun i j hij => Subgroup.comap_mono (hm hij)
  · intro i
    letI := hnormal i
    infer_instance
  · intro i hi
    letI := hnormal i
    obtain ⟨g, hg⟩ := hstep i hi
    exact cyclic_step_comap H.subtype (s i) (s (i + 1)) g hg





universe u







end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] (hG : @LocalConjugacy.Proof.LocalConjugacy.Supersolvable.{u_1} G inst)
  (H : @Subgroup.{u_1} G inst),
  @LocalConjugacy.Proof.LocalConjugacy.Supersolvable.{u_1}
    (@Subtype.{u_1 + 1} G fun (x : G) =>
      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H x)
    (@Subgroup.toGroup.{u_1} G inst H) :=
  @LocalConjugacy.Proof.LocalConjugacy.supersolvable_subgroup_preparedProof
