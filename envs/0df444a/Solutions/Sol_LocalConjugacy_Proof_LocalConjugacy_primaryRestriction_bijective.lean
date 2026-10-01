-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.primaryRestriction_bijective
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:22:47.432894+00:00
-- url     : https://prove2.me/submissions/7b6c6fff-63fa-4304-8ac4-e83a8bb696e8

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

/-! The numbered cohomology statements, expressed on the actual quotient `H¹`.
The representative-level arguments supply the proofs, without changing the
restriction maps or weakening surjectivity to separate local extension claims. -/

namespace LocalConjugacy

section QuotientMaps
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]



private theorem primaryRestriction_bijective_preparedProof (P : PrimeDivisor J → Subgroup J)
    (h : PrimaryDecomposition (N := N) P) :
    Function.Bijective (primaryRestriction (N := N) P) := by
  classical
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h f =>
      induction b using Quotient.inductionOn with
      | h g =>
        apply Quotient.sound
        apply h.2.1 f g
        intro p
        exact Quotient.exact (congrArg Subtype.val (congrFun hab p))
  · intro a
    let f (p : PrimeDivisor J) := (a p).property.choose
    have hf (p : PrimeDivisor J) : InvariantUnder ⊤ (P p) (f p) :=
      (a p).property.choose_spec.2
    obtain ⟨g, hg⟩ := h.2.2 f hf
    refine ⟨Quotient.mk _ g, funext (fun p => Subtype.ext ?_)⟩
    exact (Quotient.sound (hg p)).trans (a p).property.choose_spec.1

end QuotientMaps

section Numbered
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]





end Numbered
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : TopologicalSpace.{u_2} N]
  [inst_4 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  (P : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_2 → @Subgroup.{u_1} J inst)
  (h : @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 P),
  @Function.Bijective.{max (u_1 + 1) (u_2 + 1), max (u_1 + 1) (u_2 + 1)}
    (@LocalConjugacy.Proof.LocalConjugacy.H1.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
    ((p : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_2) →
      @LocalConjugacy.Proof.LocalConjugacy.InvariantH1.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4
        (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) (P p))
    (@LocalConjugacy.Proof.LocalConjugacy.primaryRestriction.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 P) :=
  @LocalConjugacy.Proof.LocalConjugacy.primaryRestriction_bijective_preparedProof
