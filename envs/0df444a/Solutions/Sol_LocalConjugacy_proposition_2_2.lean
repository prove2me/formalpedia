-- Prove2me | solution 1 for LocalConjugacy.proposition_2_2
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:34:12.637773+00:00
-- url     : https://prove2.me/submissions/1d64f4e5-46a6-48c1-9d13-9b34d7bf2753

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_coprime_prime_index_restriction_locallyFinite

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [DiscreteTopology N] [MulDistribMulAction J N] [ContinuousSMul J N]







end

section Statements
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]



set_option linter.unusedVariables false in
/-- Proposition 2.2 for the manuscript's locally finite discrete coefficients. -/
private theorem coprime_restriction_isomorphism [Profinite J] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N)
    (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hJ : Prosolvable J) (hN : IsPGroup p N) (J₀ : Subgroup J) [J₀.Normal]
    (hJ₀ : IsClosed (J₀ : Set J)) (hindex : J₀.index = p₀) :
    RestrictionIsomorphism (N := N) ⊤ J₀ le_top := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact p₀.Prime := ⟨hp₀⟩
  exact coprime_prime_index_restriction_locallyFinite hfinite hne hN J₀ hJ₀ hindex

end Statements
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! The numbered cohomology statements, expressed on the actual quotient `H¹`.
The representative-level arguments supply the proofs, without changing the
restriction maps or weakening surjectivity to separate local extension claims. -/

namespace LocalConjugacy

section QuotientMaps
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

private theorem stableRestriction_bijective (K : Subgroup J)
    (h : RestrictionIsomorphism (N := N) ⊤ K le_top) :
    Function.Bijective (stableRestriction (N := N) K) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h f =>
      induction b using Quotient.inductionOn with
      | h g =>
        exact Quotient.sound (h.1 f g (Quotient.exact (congrArg Subtype.val hab)))
  · rintro ⟨a, f, rfl, hf⟩
    obtain ⟨g, hg⟩ := h.2 f hf
    exact ⟨Quotient.mk _ g, Subtype.ext (Quotient.sound hg)⟩



end QuotientMaps

section Numbered
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]



/-- Proposition 2.2 (`prop:coprime_iso`), with possibly infinite locally finite
discrete coefficients and the actual restriction map on cohomology classes. -/
private theorem proposition_2_2 [Profinite J] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N)
    (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hJ : Prosolvable J) (hN : IsPGroup p N) (J₀ : Subgroup J) [J₀.Normal]
    (hJ₀ : IsClosed (J₀ : Set J)) (hindex : J₀.index = p₀) :
    Function.Bijective (stableRestriction (N := N) J₀) :=
  stableRestriction_bijective J₀
    (coprime_restriction_isomorphism hfinite p p₀ hp hp₀ hne hJ hN J₀ hJ₀ hindex)

end Numbered
end LocalConjugacy

end LocalConjugacy.Proof

end

section


/-!
Proofs of the eleven numbered results in the public draft. Each statement is
copied at Lean syntax offsets from the submitted target. The proofs invoke the
ported arguments through proved interface conversions; the pointed cohomology
claims include preservation of the identity class explicitly.
-/
universe u v
open LocalConjugacy







/-- The exact draft statement, proved by the corresponding ported paper argument. -/
private theorem LocalConjugacy.proposition_2_2_preparedProof {J : ProfiniteGrp.{u}} {N : Type v} [Group N]
    [TopologicalSpace N] [MulDistribMulAction J N] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N) (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hJ : Prosolvable J) (hN : IsPGroup p N) (J₀ : Subgroup J) [J₀.Normal]
    (hJ₀ : IsClosed (J₀ : Set J)) (hindex : J₀.index = p₀) :
    Function.Bijective (stableRestriction (N := N) J₀) ∧
      (stableRestriction (N := N) J₀) default = default := by
  exact ⟨Proof.LocalConjugacy.proposition_2_2 hfinite p p₀ hp hp₀ hne hJ hN J₀
    hJ₀ hindex, stableRestriction_distinguished J₀⟩















end

universe u v

theorem solution :
∀ {J : ProfiniteGrp.{u}} {N : Type v} [inst : Group.{v} N] [inst_1 : TopologicalSpace.{v} N]
  [inst_2 :
    @MulDistribMulAction.{u, v}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      N
      (@DivInvMonoid.toMonoid.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (@Group.toDivInvMonoid.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          (ProfiniteGrp.group.{u} J)))
      (@DivInvMonoid.toMonoid.{v} N (@Group.toDivInvMonoid.{v} N inst))]
  [@IsTopologicalGroup.{v} N inst_1 inst] [@DiscreteTopology.{v} N inst_1]
  [@ContinuousSMul.{u, v}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      N
      (@SemigroupAction.toSMul.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N
        (@Monoid.toSemigroup.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          (@DivInvMonoid.toMonoid.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (@Group.toDivInvMonoid.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J))))
        (@MulAction.toSemigroupAction.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          N
          (@DivInvMonoid.toMonoid.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (@Group.toDivInvMonoid.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J)))
          (@MulDistribMulAction.toMulAction.{u, v}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            N
            (@DivInvMonoid.toMonoid.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (@Group.toDivInvMonoid.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J)))
            (@DivInvMonoid.toMonoid.{v} N (@Group.toDivInvMonoid.{v} N inst)) inst_2)))
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      inst_1]
  (hfinite : @LocalConjugacy.LocallyFiniteGroup.{v} N inst) (p p₀ : Nat) (hp : Nat.Prime p) (hp₀ : Nat.Prime p₀)
  (hne : @Ne.{1} Nat p₀ p)
  (hJ :
    @LocalConjugacy.Prosolvable.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      (ProfiniteGrp.group.{u} J)
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J))))
  (hN : @IsPGroup.{v} p N inst)
  (J₀ :
    @Subgroup.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      (ProfiniteGrp.group.{u} J))
  [@Subgroup.Normal.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      (ProfiniteGrp.group.{u} J) J₀]
  (hJ₀ :
    @IsClosed.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      (@SetLike.coe.{u, u}
        (@Subgroup.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          (ProfiniteGrp.group.{u} J))
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (@Subgroup.instSetLike.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          (ProfiniteGrp.group.{u} J))
        J₀))
  (hindex :
    @Eq.{1} Nat
      (@Subgroup.index.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (ProfiniteGrp.group.{u} J) J₀)
      p₀),
  And
    (@Function.Bijective.{max (u + 1) (v + 1), max (u + 1) (v + 1)}
      (@LocalConjugacy.H1.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst_1 inst_2
        (@Top.top.{u}
          (@Subgroup.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J))
          (@Subgroup.instTop.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J))))
      (@LocalConjugacy.InvariantH1.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst_1 inst_2
        (@Top.top.{u}
          (@Subgroup.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J))
          (@Subgroup.instTop.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J)))
        J₀)
      (@LocalConjugacy.stableRestriction.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst_1 inst_2 J₀))
    (@Eq.{max (u + 1) (v + 1)}
      (@LocalConjugacy.InvariantH1.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst_1 inst_2
        (@Top.top.{u}
          (@Subgroup.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J))
          (@Subgroup.instTop.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J)))
        J₀)
      (@LocalConjugacy.stableRestriction.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst_1 inst_2 J₀
        (@Inhabited.default.{max (u + 1) (v + 1)}
          (@LocalConjugacy.H1.{u, v}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            N (ProfiniteGrp.group.{u} J) inst
            (TopCat.str.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            inst_1 inst_2
            (@Top.top.{u}
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@Subgroup.instTop.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))))
          (@LocalConjugacy.instInhabitedH1.{u, v}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            N (ProfiniteGrp.group.{u} J) inst
            (TopCat.str.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            inst_1 inst_2
            (@Top.top.{u}
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@Subgroup.instTop.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))))))
      (@Inhabited.default.{max (u + 1) (v + 1)}
        (@LocalConjugacy.InvariantH1.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          N (ProfiniteGrp.group.{u} J) inst
          (TopCat.str.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          inst_1 inst_2
          (@Top.top.{u}
            (@Subgroup.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J))
            (@Subgroup.instTop.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J)))
          J₀)
        (@LocalConjugacy.invariantH1Inhabited.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          N (ProfiniteGrp.group.{u} J) inst
          (TopCat.str.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          inst_1 inst_2
          (@Top.top.{u}
            (@Subgroup.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J))
            (@Subgroup.instTop.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J)))
          J₀))) :=
  @LocalConjugacy.proposition_2_2_preparedProof
