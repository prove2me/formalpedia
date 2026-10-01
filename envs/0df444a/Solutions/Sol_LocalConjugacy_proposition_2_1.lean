-- Prove2me | solution 1 for LocalConjugacy.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:34:11.831445+00:00
-- url     : https://prove2.me/submissions/b914b59e-4d07-4e07-af63-023e520c82ac

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_fixed_cocycle_of_locallyFinite
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_fixed_cocycle_trivial_on_intersection

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
/-- Proposition 2.1 for the manuscript's locally finite discrete coefficients. -/
private theorem proposition_2_1 [Profinite J] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N)
    (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hN : IsPGroup p N) (J₀ Q : Subgroup J) [J₀.Normal]
    (hJ₀ : IsClosed (J₀ : Set J)) (hQ : IsClosed (Q : Set J))
    (hcyclic : Procyclic Q) (hpro : IsProP p₀ Q)
    (f : Cocycle (N := N) J₀) (hinv : InvariantUnder Q J₀ f) :
    ∃ g : Cocycle (N := N) J₀, Cohomologous f g ∧
      (∀ (q : J) (hq : q ∈ Q) (x : J) (hx : x ∈ J₀)
        (hqx : q⁻¹ * x * q ∈ J₀),
        q • g.toFun ⟨q⁻¹ * x * q, hqx⟩ = g.toFun ⟨x, hx⟩) ∧
      ∀ (q : J) (hq : q ∈ Q) (hq₀ : q ∈ J₀), g.toFun ⟨q, hq₀⟩ = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact p₀.Prime := ⟨hp₀⟩
  obtain ⟨g, hfg, hg⟩ := fixed_cocycle_of_locallyFinite hfinite hne hN hJ₀
    Q hcyclic hpro f hinv
  refine ⟨g, hfg, ?_, ?_⟩
  · intro q hq x hx hqx
    exact congrArg (fun f : Cocycle (N := N) J₀ => f.toFun ⟨x, hx⟩) (hg ⟨q, hq⟩)
  · exact fixed_cocycle_trivial_on_intersection (hp.coprime_iff_not_dvd.mpr
      (fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hp₀).mp h).symm)) hN J₀ Q hcyclic hpro g hg



end Statements
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
private theorem LocalConjugacy.proposition_2_1_preparedProof {J : ProfiniteGrp.{u}} {N : Type v} [Group N]
    [TopologicalSpace N] [MulDistribMulAction J N] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N) (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
    (hN : IsPGroup p N) (J₀ Q : Subgroup J) [J₀.Normal]
    (hJ₀ : IsClosed (J₀ : Set J)) (hQ : IsClosed (Q : Set J))
    (hcyclic : Procyclic Q) (hpro : IsProP p₀ Q)
    (f : Cocycle (N := N) J₀) (hinv : InvariantUnder Q J₀ f) :
    ∃ g : Cocycle (N := N) J₀, Cohomologous f g ∧
      (∀ (q : J) (hq : q ∈ Q) (x : J) (hx : x ∈ J₀)
        (hqx : q⁻¹ * x * q ∈ J₀),
        q • g.toFun ⟨q⁻¹ * x * q, hqx⟩ = g.toFun ⟨x, hx⟩) ∧
      ∀ (q : J) (hq : q ∈ Q) (hq₀ : q ∈ J₀), g.toFun ⟨q, hq₀⟩ = 1 := by
  exact Proof.LocalConjugacy.proposition_2_1 hfinite p p₀ hp hp₀ hne hN J₀ Q
    hJ₀ hQ hcyclic hpro f hinv

















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
  (hne : @Ne.{1} Nat p₀ p) (hN : @IsPGroup.{v} p N inst)
  (J₀ Q :
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
  (hQ :
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
        Q))
  (hcyclic :
    @LocalConjugacy.Procyclic.{u}
      (@Subtype.{u + 1}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        fun
          (x :
            TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J))) =>
        @Membership.mem.{u, u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          (@Subgroup.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J))
          (@SetLike.instMembership.{u, u}
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
              (ProfiniteGrp.group.{u} J)))
          Q x)
      (@Subgroup.toGroup.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (ProfiniteGrp.group.{u} J) Q)
      (@instTopologicalSpaceSubtype.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (fun
            (x :
              TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J))) =>
          @Membership.mem.{u, u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (@Subgroup.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J))
            (@SetLike.instMembership.{u, u}
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
                (ProfiniteGrp.group.{u} J)))
            Q x)
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))))
  (hpro :
    @LocalConjugacy.IsProP.{u} p₀
      (@Subtype.{u + 1}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        fun
          (x :
            TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J))) =>
        @Membership.mem.{u, u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          (@Subgroup.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J))
          (@SetLike.instMembership.{u, u}
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
              (ProfiniteGrp.group.{u} J)))
          Q x)
      (@Subgroup.toGroup.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (ProfiniteGrp.group.{u} J) Q)
      (@instTopologicalSpaceSubtype.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (fun
            (x :
              TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J))) =>
          @Membership.mem.{u, u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (@Subgroup.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J))
            (@SetLike.instMembership.{u, u}
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
                (ProfiniteGrp.group.{u} J)))
            Q x)
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))))
  (f :
    @LocalConjugacy.Cocycle.{u, v}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      N (ProfiniteGrp.group.{u} J) inst
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      inst_1 inst_2 J₀)
  (hinv :
    @LocalConjugacy.InvariantUnder.{u, v}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      N (ProfiniteGrp.group.{u} J) inst
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      inst_1 inst_2 Q J₀ f),
  @Exists.{max (u + 1) (v + 1)}
    (@LocalConjugacy.Cocycle.{u, v}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      N (ProfiniteGrp.group.{u} J) inst
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      inst_1 inst_2 J₀)
    fun
      (g :
        @LocalConjugacy.Cocycle.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          N (ProfiniteGrp.group.{u} J) inst
          (TopCat.str.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          inst_1 inst_2 J₀) =>
    And
      (@LocalConjugacy.Cohomologous.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst_1 inst_2 J₀ f g)
      (And
        (∀
          (q :
            TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
          (hq :
            @Membership.mem.{u, u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@SetLike.instMembership.{u, u}
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
                  (ProfiniteGrp.group.{u} J)))
              Q q)
          (x :
            TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
          (hx :
            @Membership.mem.{u, u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@SetLike.instMembership.{u, u}
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
                  (ProfiniteGrp.group.{u} J)))
              J₀ x)
          (hqx :
            @Membership.mem.{u, u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@SetLike.instMembership.{u, u}
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
                  (ProfiniteGrp.group.{u} J)))
              J₀
              (@HMul.hMul.{u, u, u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (@instHMul.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (@MulOne.toMul.{u}
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (@MulOneClass.toMulOne.{u}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (@Monoid.toMulOneClass.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (@DivInvMonoid.toMonoid.{u}
                          (TopCat.carrier.{u}
                            (@CompHausLike.toTop.{u}
                              (fun (X : TopCat.{u}) =>
                                @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                              (ProfiniteGrp.toProfinite.{u} J)))
                          (@Group.toDivInvMonoid.{u}
                            (TopCat.carrier.{u}
                              (@CompHausLike.toTop.{u}
                                (fun (X : TopCat.{u}) =>
                                  @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                (ProfiniteGrp.toProfinite.{u} J)))
                            (ProfiniteGrp.group.{u} J)))))))
                (@HMul.hMul.{u, u, u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (@instHMul.{u}
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (@MulOne.toMul.{u}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (@MulOneClass.toMulOne.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (@Monoid.toMulOneClass.{u}
                          (TopCat.carrier.{u}
                            (@CompHausLike.toTop.{u}
                              (fun (X : TopCat.{u}) =>
                                @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                              (ProfiniteGrp.toProfinite.{u} J)))
                          (@DivInvMonoid.toMonoid.{u}
                            (TopCat.carrier.{u}
                              (@CompHausLike.toTop.{u}
                                (fun (X : TopCat.{u}) =>
                                  @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                (ProfiniteGrp.toProfinite.{u} J)))
                            (@Group.toDivInvMonoid.{u}
                              (TopCat.carrier.{u}
                                (@CompHausLike.toTop.{u}
                                  (fun (X : TopCat.{u}) =>
                                    @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                  (ProfiniteGrp.toProfinite.{u} J)))
                              (ProfiniteGrp.group.{u} J)))))))
                  (@Inv.inv.{u}
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (@InvOneClass.toInv.{u}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (@DivInvOneMonoid.toInvOneClass.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (@DivisionMonoid.toDivInvOneMonoid.{u}
                          (TopCat.carrier.{u}
                            (@CompHausLike.toTop.{u}
                              (fun (X : TopCat.{u}) =>
                                @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                              (ProfiniteGrp.toProfinite.{u} J)))
                          (@Group.toDivisionMonoid.{u}
                            (TopCat.carrier.{u}
                              (@CompHausLike.toTop.{u}
                                (fun (X : TopCat.{u}) =>
                                  @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                (ProfiniteGrp.toProfinite.{u} J)))
                            (ProfiniteGrp.group.{u} J)))))
                    q)
                  x)
                q)),
          @Eq.{v + 1} N
            (@HSMul.hSMul.{u, v, v}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              N N
              (@instHSMul.{u, v}
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
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (@DivInvMonoid.toMonoid.{u}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (@Group.toDivInvMonoid.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (ProfiniteGrp.group.{u} J))))
                  (@MulAction.toSemigroupAction.{u, v}
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    N
                    (@DivInvMonoid.toMonoid.{u}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (@Group.toDivInvMonoid.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (ProfiniteGrp.group.{u} J)))
                    (@MulDistribMulAction.toMulAction.{u, v}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      N
                      (@DivInvMonoid.toMonoid.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (@Group.toDivInvMonoid.{u}
                          (TopCat.carrier.{u}
                            (@CompHausLike.toTop.{u}
                              (fun (X : TopCat.{u}) =>
                                @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                              (ProfiniteGrp.toProfinite.{u} J)))
                          (ProfiniteGrp.group.{u} J)))
                      (@DivInvMonoid.toMonoid.{v} N (@Group.toDivInvMonoid.{v} N inst)) inst_2))))
              q
              (@LocalConjugacy.Cocycle.toFun.{u, v}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                N (ProfiniteGrp.group.{u} J) inst
                (TopCat.str.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                inst_1 inst_2 J₀ g
                (@Subtype.mk.{u + 1}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (fun
                      (x :
                        TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J))) =>
                    @Membership.mem.{u, u}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (@Subgroup.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (ProfiniteGrp.group.{u} J))
                      (@SetLike.instMembership.{u, u}
                        (@Subgroup.{u}
                          (TopCat.carrier.{u}
                            (@CompHausLike.toTop.{u}
                              (fun (X : TopCat.{u}) =>
                                @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                              (ProfiniteGrp.toProfinite.{u} J)))
                          (ProfiniteGrp.group.{u} J))
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (@Subgroup.instSetLike.{u}
                          (TopCat.carrier.{u}
                            (@CompHausLike.toTop.{u}
                              (fun (X : TopCat.{u}) =>
                                @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                              (ProfiniteGrp.toProfinite.{u} J)))
                          (ProfiniteGrp.group.{u} J)))
                      J₀ x)
                  (@HMul.hMul.{u, u, u}
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (@instHMul.{u}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (@MulOne.toMul.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (@MulOneClass.toMulOne.{u}
                          (TopCat.carrier.{u}
                            (@CompHausLike.toTop.{u}
                              (fun (X : TopCat.{u}) =>
                                @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                              (ProfiniteGrp.toProfinite.{u} J)))
                          (@Monoid.toMulOneClass.{u}
                            (TopCat.carrier.{u}
                              (@CompHausLike.toTop.{u}
                                (fun (X : TopCat.{u}) =>
                                  @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                (ProfiniteGrp.toProfinite.{u} J)))
                            (@DivInvMonoid.toMonoid.{u}
                              (TopCat.carrier.{u}
                                (@CompHausLike.toTop.{u}
                                  (fun (X : TopCat.{u}) =>
                                    @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                  (ProfiniteGrp.toProfinite.{u} J)))
                              (@Group.toDivInvMonoid.{u}
                                (TopCat.carrier.{u}
                                  (@CompHausLike.toTop.{u}
                                    (fun (X : TopCat.{u}) =>
                                      @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                    (ProfiniteGrp.toProfinite.{u} J)))
                                (ProfiniteGrp.group.{u} J)))))))
                    (@HMul.hMul.{u, u, u}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (@instHMul.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (@MulOne.toMul.{u}
                          (TopCat.carrier.{u}
                            (@CompHausLike.toTop.{u}
                              (fun (X : TopCat.{u}) =>
                                @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                              (ProfiniteGrp.toProfinite.{u} J)))
                          (@MulOneClass.toMulOne.{u}
                            (TopCat.carrier.{u}
                              (@CompHausLike.toTop.{u}
                                (fun (X : TopCat.{u}) =>
                                  @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                (ProfiniteGrp.toProfinite.{u} J)))
                            (@Monoid.toMulOneClass.{u}
                              (TopCat.carrier.{u}
                                (@CompHausLike.toTop.{u}
                                  (fun (X : TopCat.{u}) =>
                                    @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                  (ProfiniteGrp.toProfinite.{u} J)))
                              (@DivInvMonoid.toMonoid.{u}
                                (TopCat.carrier.{u}
                                  (@CompHausLike.toTop.{u}
                                    (fun (X : TopCat.{u}) =>
                                      @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                    (ProfiniteGrp.toProfinite.{u} J)))
                                (@Group.toDivInvMonoid.{u}
                                  (TopCat.carrier.{u}
                                    (@CompHausLike.toTop.{u}
                                      (fun (X : TopCat.{u}) =>
                                        @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                      (ProfiniteGrp.toProfinite.{u} J)))
                                  (ProfiniteGrp.group.{u} J)))))))
                      (@Inv.inv.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (@InvOneClass.toInv.{u}
                          (TopCat.carrier.{u}
                            (@CompHausLike.toTop.{u}
                              (fun (X : TopCat.{u}) =>
                                @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                              (ProfiniteGrp.toProfinite.{u} J)))
                          (@DivInvOneMonoid.toInvOneClass.{u}
                            (TopCat.carrier.{u}
                              (@CompHausLike.toTop.{u}
                                (fun (X : TopCat.{u}) =>
                                  @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                (ProfiniteGrp.toProfinite.{u} J)))
                            (@DivisionMonoid.toDivInvOneMonoid.{u}
                              (TopCat.carrier.{u}
                                (@CompHausLike.toTop.{u}
                                  (fun (X : TopCat.{u}) =>
                                    @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                  (ProfiniteGrp.toProfinite.{u} J)))
                              (@Group.toDivisionMonoid.{u}
                                (TopCat.carrier.{u}
                                  (@CompHausLike.toTop.{u}
                                    (fun (X : TopCat.{u}) =>
                                      @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                                    (ProfiniteGrp.toProfinite.{u} J)))
                                (ProfiniteGrp.group.{u} J)))))
                        q)
                      x)
                    q)
                  hqx)))
            (@LocalConjugacy.Cocycle.toFun.{u, v}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              N (ProfiniteGrp.group.{u} J) inst
              (TopCat.str.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              inst_1 inst_2 J₀ g
              (@Subtype.mk.{u + 1}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (fun
                    (x :
                      TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J))) =>
                  @Membership.mem.{u, u}
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (@Subgroup.{u}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (ProfiniteGrp.group.{u} J))
                    (@SetLike.instMembership.{u, u}
                      (@Subgroup.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (ProfiniteGrp.group.{u} J))
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (@Subgroup.instSetLike.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (ProfiniteGrp.group.{u} J)))
                    J₀ x)
                x hx)))
        (∀
          (q :
            TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
          (hq :
            @Membership.mem.{u, u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@SetLike.instMembership.{u, u}
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
                  (ProfiniteGrp.group.{u} J)))
              Q q)
          (hq₀ :
            @Membership.mem.{u, u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@SetLike.instMembership.{u, u}
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
                  (ProfiniteGrp.group.{u} J)))
              J₀ q),
          @Eq.{v + 1} N
            (@LocalConjugacy.Cocycle.toFun.{u, v}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              N (ProfiniteGrp.group.{u} J) inst
              (TopCat.str.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              inst_1 inst_2 J₀ g
              (@Subtype.mk.{u + 1}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (fun
                    (x :
                      TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J))) =>
                  @Membership.mem.{u, u}
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (@Subgroup.{u}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (ProfiniteGrp.group.{u} J))
                    (@SetLike.instMembership.{u, u}
                      (@Subgroup.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (ProfiniteGrp.group.{u} J))
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (@Subgroup.instSetLike.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (ProfiniteGrp.group.{u} J)))
                    J₀ x)
                q hq₀))
            (@OfNat.ofNat.{v} N (nat_lit 1)
              (@One.toOfNat1.{v} N
                (@InvOneClass.toOne.{v} N
                  (@DivInvOneMonoid.toInvOneClass.{v} N
                    (@DivisionMonoid.toDivInvOneMonoid.{v} N (@Group.toDivisionMonoid.{v} N inst)))))))) :=
  @LocalConjugacy.proposition_2_1_preparedProof
