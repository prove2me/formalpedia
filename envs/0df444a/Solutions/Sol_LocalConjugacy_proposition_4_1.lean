-- Prove2me | solution 1 for LocalConjugacy.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:43:13.361352+00:00
-- url     : https://prove2.me/submissions/98c00004-a81c-4b1c-b7eb-af302ff09f72

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_proposition_4_1

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
private theorem LocalConjugacy.proposition_4_1_preparedProof {G : ProfiniteGrp.{u}} (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) [IsMulCommutative N]
    (hHN : Supplements N H) (hKN : Supplements N K)
    (hlocal : LocallyContains H K) : ∃ g : G, conjugate g K ≤ H := by
  exact Proof.LocalConjugacy.proposition_4_1 N H K hN hH hK
    (fun n m => mul_comm' n m) hHN hKN hlocal







end

universe u

theorem solution :
∀ {G : ProfiniteGrp.{u}}
  (N H K :
    @Subgroup.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (ProfiniteGrp.group.{u} G))
  [@Subgroup.Normal.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (ProfiniteGrp.group.{u} G) N]
  (hN :
    @IsClosed.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (@SetLike.coe.{u, u}
        (@Subgroup.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          (ProfiniteGrp.group.{u} G))
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        (@Subgroup.instSetLike.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          (ProfiniteGrp.group.{u} G))
        N))
  (hH :
    @IsClosed.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (@SetLike.coe.{u, u}
        (@Subgroup.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          (ProfiniteGrp.group.{u} G))
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        (@Subgroup.instSetLike.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          (ProfiniteGrp.group.{u} G))
        H))
  (hK :
    @IsClosed.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (@SetLike.coe.{u, u}
        (@Subgroup.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          (ProfiniteGrp.group.{u} G))
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        (@Subgroup.instSetLike.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          (ProfiniteGrp.group.{u} G))
        K))
  [@IsMulCommutative.{u}
      (@Subtype.{u + 1}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        fun
          (x :
            TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} G))) =>
        @Membership.mem.{u, u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          (@Subgroup.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} G)))
            (ProfiniteGrp.group.{u} G))
          (@SetLike.instMembership.{u, u}
            (@Subgroup.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} G)))
              (ProfiniteGrp.group.{u} G))
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} G)))
            (@Subgroup.instSetLike.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} G)))
              (ProfiniteGrp.group.{u} G)))
          N x)
      (@Subgroup.mul.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        (ProfiniteGrp.group.{u} G) N)]
  (hHN :
    @LocalConjugacy.Supplements.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (ProfiniteGrp.group.{u} G) N H)
  (hKN :
    @LocalConjugacy.Supplements.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (ProfiniteGrp.group.{u} G) N K)
  (hlocal :
    @LocalConjugacy.LocallyContains.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (ProfiniteGrp.group.{u} G)
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      H K),
  @Exists.{u + 1}
    (TopCat.carrier.{u}
      (@CompHausLike.toTop.{u}
        (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
        (ProfiniteGrp.toProfinite.{u} G)))
    fun
      (g :
        TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G))) =>
    @LE.le.{u}
      (@Subgroup.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        (ProfiniteGrp.group.{u} G))
      (@Preorder.toLE.{u}
        (@Subgroup.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          (ProfiniteGrp.group.{u} G))
        (@PartialOrder.toPreorder.{u}
          (@Subgroup.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} G)))
            (ProfiniteGrp.group.{u} G))
          (@Subgroup.instPartialOrder.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} G)))
            (ProfiniteGrp.group.{u} G))))
      (@LocalConjugacy.conjugate.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        (ProfiniteGrp.group.{u} G) g K)
      H :=
  @LocalConjugacy.proposition_4_1_preparedProof
