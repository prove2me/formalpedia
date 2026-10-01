-- Prove2me | solution 1 for LocalConjugacy.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:43:14.335834+00:00
-- url     : https://prove2.me/submissions/dc3fa54a-edd6-4e51-bf43-5226821d0d89

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_supplements_of_locallyContains

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section


/-!
The mission uses Mathlib's standard public interfaces.  These elementary bridges
connect them to the equivalent internal interfaces of the existing proof corpus.
Every conversion is proved; no extra assumption is added to a paper statement.
-/
namespace LocalConjugacy









/-- A point of Mathlib's fixed-point set is a point fixed by every group element. -/
private theorem hasFixedPoint_iff_internal {G Ω : Type*} [Group G] [MulAction G Ω]
    (H : Subgroup G) :
    HasFixedPoint (Ω := Ω) H ↔ Proof.LocalConjugacy.HasFixedPoint (Ω := Ω) H := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun h hh => hx ⟨h, hh⟩⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, fun h => hx h h.property⟩

/-- Local fixed-point data uses the same Sylow subgroups on both sides. -/
private theorem sylowFixedPoints_iff_internal {G Ω : Type*} [Group G] [TopologicalSpace G]
    [MulAction G Ω] (H : Subgroup G) :
    SylowFixedPoints (Ω := Ω) H ↔ Proof.LocalConjugacy.SylowFixedPoints (Ω := Ω) H := by
  constructor <;> intro h p hp <;> obtain ⟨P, hP, hx⟩ := h p hp
  · exact ⟨P, hP, (hasFixedPoint_iff_internal P).mp hx⟩
  · exact ⟨P, hP, (hasFixedPoint_iff_internal P).mpr hx⟩

end LocalConjugacy

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- The geometric step in Corollary 1.4 and Proposition 4.2. -/
private theorem fixedPoint_of_conjugate_le_stabilizer (J : Subgroup G) (x : Ω)
    (g : G) (h : conjugate g J ≤ MulAction.stabilizer G x) :
    HasFixedPoint (Ω := Ω) J := by
  refine ⟨g⁻¹ • x, ?_⟩
  intro j hj
  have hf : (g * j * g⁻¹) • x = x := h (Subgroup.mem_map_of_mem _ hj)
  have ht := congrArg (fun y : Ω => g⁻¹ • y) hf
  simpa [mul_smul] using ht

/-- Transitivity takes a fixed point to conjugate subgroup inclusion in a
chosen point stabilizer. -/
private theorem conjugate_le_stabilizer_of_fixedPoint (htrans : Transitive (G := G) (Ω := Ω))
    (J : Subgroup G) (x : Ω) (hfix : HasFixedPoint (Ω := Ω) J) :
    ∃ g : G, conjugate g J ≤ MulAction.stabilizer G x := by
  obtain ⟨y, hy⟩ := hfix
  obtain ⟨g, hg⟩ := htrans y x
  refine ⟨g, ?_⟩
  rintro _ ⟨j, hj, rfl⟩
  change (g * j * g⁻¹) • x = x
  rw [← hg]
  simp [mul_smul, hy j hj]



private theorem locallyContains_stabilizer_of_sylowFixedPoints [TopologicalSpace G]
    (htrans : Transitive (G := G) (Ω := Ω)) (J : Subgroup G) (x : Ω)
    (hlocal : SylowFixedPoints (Ω := Ω) J) :
    LocallyContains (MulAction.stabilizer G x) J := by
  intro p hp
  obtain ⟨P, hP, hf⟩ := hlocal p hp
  exact ⟨P, hP, conjugate_le_stabilizer_of_fixedPoint htrans P x hf⟩



end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

/-- Proposition 4.2, `thm:fix_pt_ab`. -/
private theorem proposition_4_2 {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    {Ω : Type*} [MulAction G Ω] [Nonempty Ω]
    (N H : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))
    (hH : IsClosed (H : Set G)) (hcomm : ∀ n m : N, n * m = m * n)
    (hHN : Supplements N H) (htrans : Transitive (G := G) (Ω := Ω))
    (hclosed : ∀ x : Ω, IsClosed (MulAction.stabilizer G x : Set G))
    (hlocal : SylowFixedPoints (Ω := Ω) H) : HasFixedPoint (Ω := Ω) H := by
  obtain ⟨x⟩ := ‹Nonempty Ω›
  have hl := locallyContains_stabilizer_of_sylowFixedPoints htrans H x hlocal
  have hs := supplements_of_locallyContains N (MulAction.stabilizer G x) H
    hN (hclosed x) hH hHN hl
  obtain ⟨g, hg⟩ := proposition_4_1 N (MulAction.stabilizer G x) H
    hN (hclosed x) hH hcomm hs hHN hl
  exact fixedPoint_of_conjugate_le_stabilizer H x g hg

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
private theorem LocalConjugacy.proposition_4_2_preparedProof {G : ProfiniteGrp.{u}} {Ω : Type v} [MulAction G Ω] [Nonempty Ω]
    (N H : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))
    (hH : IsClosed (H : Set G)) [IsMulCommutative N]
    (hHN : Supplements N H) (htrans : MulAction.IsPretransitive G Ω)
    (hclosed : ∀ x : Ω, IsClosed (MulAction.stabilizer G x : Set G))
    (hlocal : SylowFixedPoints (Ω := Ω) H) : HasFixedPoint (Ω := Ω) H := by
  apply (hasFixedPoint_iff_internal H).mpr
  exact Proof.LocalConjugacy.proposition_4_2 N H hN hH (fun n m => mul_comm' n m)
    hHN htrans.exists_smul_eq hclosed ((sylowFixedPoints_iff_internal H).mp hlocal)

end

universe u v

theorem solution :
∀ {G : ProfiniteGrp.{u}} {Ω : Type v}
  [inst :
    @MulAction.{u, v}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      Ω
      (@DivInvMonoid.toMonoid.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        (@Group.toDivInvMonoid.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          (ProfiniteGrp.group.{u} G)))]
  [Nonempty.{v + 1} Ω]
  (N H :
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
  (htrans :
    @MulAction.IsPretransitive.{u, v}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      Ω
      (@SemigroupAction.toSMul.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        Ω
        (@Monoid.toSemigroup.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          (@DivInvMonoid.toMonoid.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} G)))
            (@Group.toDivInvMonoid.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} G)))
              (ProfiniteGrp.group.{u} G))))
        (@MulAction.toSemigroupAction.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          Ω
          (@DivInvMonoid.toMonoid.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} G)))
            (@Group.toDivInvMonoid.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} G)))
              (ProfiniteGrp.group.{u} G)))
          inst)))
  (hclosed :
    ∀ (x : Ω),
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
          (@MulAction.stabilizer.{u, v}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} G)))
            Ω (ProfiniteGrp.group.{u} G) inst x)))
  (hlocal :
    @LocalConjugacy.SylowFixedPoints.{u, v}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      Ω (ProfiniteGrp.group.{u} G)
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      inst H),
  @LocalConjugacy.HasFixedPoint.{u, v}
    (TopCat.carrier.{u}
      (@CompHausLike.toTop.{u}
        (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
        (ProfiniteGrp.toProfinite.{u} G)))
    Ω (ProfiniteGrp.group.{u} G) inst H :=
  @LocalConjugacy.proposition_4_2_preparedProof
