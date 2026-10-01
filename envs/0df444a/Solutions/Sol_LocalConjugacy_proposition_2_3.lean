-- Prove2me | solution 1 for LocalConjugacy.proposition_2_3
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:38:41.300826+00:00
-- url     : https://prove2.me/submissions/2bac45b6-2677-433d-9142-1f3d4c4a4a7f

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_proposition_2_3

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

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
private theorem LocalConjugacy.proposition_2_3_preparedProof {J : ProfiniteGrp.{u}} {N : Type v} [Group N]
    [TopologicalSpace N] [MulDistribMulAction J N] [DiscreteTopology N] [Finite N]
    [ContinuousSMul J N] (p : ℕ) (hp : p.Prime) (hN : IsPGroup p N)
    (hG : Prosupersolvable (ActionProduct J N))
    (Q : Subgroup J) (hQ : IsHallPro {r | r ≤ p} Q) :
    Function.Bijective (restrictH1 (N := N) (show Q ≤ ⊤ from le_top)) ∧
      (restrictH1 (N := N) (show Q ≤ ⊤ from le_top)) default = default := by
  exact ⟨Proof.LocalConjugacy.proposition_2_3 p hp hN hG Q hQ,
    restrictH1_distinguished le_top⟩













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
  [@DiscreteTopology.{v} N inst_1] [Finite.{v + 1} N]
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
  (p : Nat) (hp : Nat.Prime p) (hN : @IsPGroup.{v} p N inst)
  (hG :
    @LocalConjugacy.Prosupersolvable.{max v u}
      (@LocalConjugacy.ActionProduct.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst inst_2)
      (@SemidirectProduct.instGroup.{v, u} N
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst (ProfiniteGrp.group.{u} J)
        (@MulDistribMulAction.toMulAut.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          N (ProfiniteGrp.group.{u} J) (@DivInvMonoid.toMonoid.{v} N (@Group.toDivInvMonoid.{v} N inst)) inst_2))
      (@LocalConjugacy.Proof.LocalConjugacy.semidirectTopology.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst_1
        (@MulDistribMulAction.toMulAut.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          N (ProfiniteGrp.group.{u} J) (@DivInvMonoid.toMonoid.{v} N (@Group.toDivInvMonoid.{v} N inst)) inst_2)))
  (Q :
    @Subgroup.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      (ProfiniteGrp.group.{u} J))
  (hQ :
    @LocalConjugacy.IsHallPro.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      (ProfiniteGrp.group.{u} J)
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r p) Q),
  And
    (@Function.Bijective.{max (v + 1) (u + 1), max (v + 1) (u + 1)}
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
        inst_1 inst_2 Q)
      (@LocalConjugacy.restrictH1.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst_1 inst_2 Q
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
        (have this :
          @LE.le.{u}
            (@Subgroup.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J))
            (@Preorder.toLE.{u}
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@PartialOrder.toPreorder.{u}
                (@Subgroup.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))
                (@Subgroup.instPartialOrder.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))))
            Q
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
                (ProfiniteGrp.group.{u} J))) :=
          @le_top.{u}
            (@Subgroup.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J))
            (@Preorder.toLE.{u}
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@PartialOrder.toPreorder.{u}
                (@Subgroup.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))
                (@Subgroup.instPartialOrder.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))))
            (@BoundedOrder.toOrderTop.{u}
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@Preorder.toLE.{u}
                (@Subgroup.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))
                (@PartialOrder.toPreorder.{u}
                  (@Subgroup.{u}
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (ProfiniteGrp.group.{u} J))
                  (@Subgroup.instPartialOrder.{u}
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (ProfiniteGrp.group.{u} J))))
              (@CompleteLattice.toBoundedOrder.{u}
                (@Subgroup.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))
                (@Subgroup.instCompleteLattice.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))))
            Q;
        this)))
    (@Eq.{max (u + 1) (v + 1)}
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
        inst_1 inst_2 Q)
      (@LocalConjugacy.restrictH1.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst_1 inst_2 Q
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
        (have this :
          @LE.le.{u}
            (@Subgroup.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J))
            (@Preorder.toLE.{u}
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@PartialOrder.toPreorder.{u}
                (@Subgroup.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))
                (@Subgroup.instPartialOrder.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))))
            Q
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
                (ProfiniteGrp.group.{u} J))) :=
          @le_top.{u}
            (@Subgroup.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J))
            (@Preorder.toLE.{u}
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@PartialOrder.toPreorder.{u}
                (@Subgroup.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))
                (@Subgroup.instPartialOrder.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))))
            (@BoundedOrder.toOrderTop.{u}
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@Preorder.toLE.{u}
                (@Subgroup.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))
                (@PartialOrder.toPreorder.{u}
                  (@Subgroup.{u}
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (ProfiniteGrp.group.{u} J))
                  (@Subgroup.instPartialOrder.{u}
                    (TopCat.carrier.{u}
                      (@CompHausLike.toTop.{u}
                        (fun (X : TopCat.{u}) =>
                          @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                        (ProfiniteGrp.toProfinite.{u} J)))
                    (ProfiniteGrp.group.{u} J))))
              (@CompleteLattice.toBoundedOrder.{u}
                (@Subgroup.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))
                (@Subgroup.instCompleteLattice.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))))
            Q;
        this)
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
          inst_1 inst_2 Q)
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
          inst_1 inst_2 Q))) :=
  @LocalConjugacy.proposition_2_3_preparedProof
