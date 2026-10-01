-- Prove2me | solution 1 for LocalConjugacy.corollary_1_4
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T18:21:28.483453+00:00
-- url     : https://prove2.me/submissions/0ad78ffd-d6ff-40f0-95c9-476edae1b414

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_pronilpotent_local_inclusion
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_supplements_of_locallyContains

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section


/-!
The mission uses Mathlib's standard public interfaces.  These elementary bridges
connect them to the equivalent internal interfaces of the existing proof corpus.
Every conversion is proved; no extra assumption is added to a paper statement.
-/
namespace LocalConjugacy



/-- Surjectivity of the unique-product map supplies a setwise supplement. -/
private theorem supplement_of_complement {G : Type*} [Group G] {N H : Subgroup G}
    (h : N.IsComplement' H) : Supplements N H := by
  intro g
  obtain ⟨⟨n, x⟩, he⟩ := h.2 g
  exact ⟨n, n.property, x, x.property, he⟩

/-- The two formulations of an internal semidirect product are equivalent:
unique factorization is exactly existence together with trivial intersection. -/
private theorem splits_iff_internal {G : Type*} [Group G] (N J : Subgroup G) :
    Splits N J ↔ Proof.LocalConjugacy.Splits N J := by
  constructor
  · rintro ⟨hn, hc⟩
    exact ⟨hn, supplement_of_complement hc, hc.disjoint.eq_bot⟩
  · rintro ⟨hn, hs, hd⟩
    refine ⟨hn, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      (disjoint_iff.mpr hd) ?_⟩
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨n, hn, j, hj, he⟩ := hs g
    exact ⟨n, hn, j, hj, he⟩

/-- Normality inside N says that conjugation by each element of N preserves
its intersection with H.  The subtype formulation keeps the ambient group clear. -/
private theorem intersectionNormal_iff_internal {G : Type*} [Group G] (N H : Subgroup G) :
    IntersectionNormal N H ↔ Proof.LocalConjugacy.IntersectionNormal N H := by
  constructor
  · intro h n hn d hd
    exact h.conj_mem ⟨d, hd.1⟩ hd ⟨n, hn⟩
  · intro h
    constructor
    intro d hd n
    exact h n n.property d hd

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

/-- This is the proved reduction used by Corollary 1.4. `inclusion` is an
explicit input, not an axiom or a claimed proof of Corollary 1.3. -/
private theorem fixedPoint_of_local_inclusion [TopologicalSpace G]
    (htrans : Transitive (G := G) (Ω := Ω)) (J : Subgroup G) (x : Ω)
    (hlocal : SylowFixedPoints (Ω := Ω) J)
    (inclusion : LocallyContains (MulAction.stabilizer G x) J →
      ∃ g : G, conjugate g J ≤ MulAction.stabilizer G x) :
    HasFixedPoint (Ω := Ω) J := by
  obtain ⟨g, hg⟩ := inclusion (locallyContains_stabilizer_of_sylowFixedPoints htrans J x hlocal)
  exact fixedPoint_of_conjugate_le_stabilizer J x g hg

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Algebra
variable {G F : Type*} [Group G] [Group F]





end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]

/-- A continuous discrete quotient of a pronilpotent group is nilpotent. -/
private theorem nilpotent_of_pronilpotent_surjective (hG : Pronilpotent G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Group.IsNilpotent F := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  letI := hG U
  exact Group.nilpotent_of_surjective (QuotientGroup.kerLift f)
    (QuotientGroup.lift_surjective_of_surjective _ f hs le_rfl)





end Topology

section Discrete
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]





end Discrete
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Maps
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [IsTopologicalGroup F]

private theorem pronilpotent_of_continuous_surjective (hG : Pronilpotent G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Pronilpotent F := by
  intro U
  exact nilpotent_of_pronilpotent_surjective hG
    ((QuotientGroup.mk' U.toSubgroup).comp f)
    (continuous_quotient_mk'.comp hf) ((QuotientGroup.mk'_surjective U.toSubgroup).comp hs)



end Maps

section Algebra
variable {G : Type*} [Group G]









end Algebra

section Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]







end Topology
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Maps
variable {G F : Type*} [Group G] [Group F] [TopologicalSpace G] [TopologicalSpace F]
  [IsTopologicalGroup G] [IsTopologicalGroup F]



private theorem supplement_quotient_surjective (N H : Subgroup G) [N.Normal]
    (hs : Supplements N H) : Function.Surjective ((QuotientGroup.mk' N).comp H.subtype) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
  obtain ⟨n, hn, h, hh, rfl⟩ := hs x
  refine ⟨⟨h, hh⟩, ?_⟩
  change QuotientGroup.mk' N h = QuotientGroup.mk' N (n * h)
  have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  rw [map_mul, hn1, one_mul]



private theorem pronilpotent_quotient_of_supplement (N H : Subgroup G) [N.Normal]
    (hs : Supplements N H) (hH : Pronilpotent H) : Pronilpotent (G ⧸ N) :=
  pronilpotent_of_continuous_surjective hH ((QuotientGroup.mk' N).comp H.subtype)
    (continuous_quotient_mk'.comp continuous_subtype_val) (supplement_quotient_surjective N H hs)



end Maps

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy


section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]





/-- Corollary 1.3, with the unchanged normal-intersection hypothesis. -/
private theorem corollary_1_3 (N J H : Subgroup G)
    (hN : IsClosed (N : Set G)) (hJ : IsClosed (J : Set G))
    (hH : IsClosed (H : Set G)) (hsplit : Splits N J)
    (hpron : Pronilpotent N) (hcase : Prosupersolvable G ∨ Pronilpotent J)
    (hnormal : IntersectionNormal N H) (hlocal : LocallyContains H J) :
    ∃ g : G, conjugate g J ≤ H := by
  letI := hsplit.1
  have hsH := supplements_of_locallyContains N H J hN hH hJ hsplit.2.1 hlocal
  have hcase' : Prosupersolvable G ∨ Pronilpotent (G ⧸ N) := by
    rcases hcase with h | h
    · exact Or.inl h
    · exact Or.inr (pronilpotent_quotient_of_supplement N J hsplit.2.1 h)
  exact pronilpotent_local_inclusion N H J hN hH hJ hpron hcase' hsH hsplit.2.1 hnormal hlocal

end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

/-- Corollary 1.4. Closedness of each point stabilizer supplies the closed
subgroup required by Corollary 1.3; no topology on the acted-on set is used. -/
private theorem corollary_1_4 {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    {Ω : Type*} [MulAction G Ω] [Nonempty Ω]
    (N J : Subgroup G) (hN : IsClosed (N : Set G)) (hJ : IsClosed (J : Set G))
    (hsplit : Splits N J) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent J)
    (htrans : Transitive (G := G) (Ω := Ω))
    (hclosed : ∀ x : Ω, IsClosed (MulAction.stabilizer G x : Set G))
    (hnormal : ∃ x : Ω, IntersectionNormal N (MulAction.stabilizer G x))
    (hlocal : SylowFixedPoints (Ω := Ω) J) : HasFixedPoint (Ω := Ω) J := by
  obtain ⟨x, hx⟩ := hnormal
  apply fixedPoint_of_local_inclusion htrans J x hlocal
  exact corollary_1_3 N J (MulAction.stabilizer G x) hN hJ (hclosed x)
    hsplit hpron hcase hx

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
private theorem LocalConjugacy.corollary_1_4_preparedProof {G : ProfiniteGrp.{u}} {Ω : Type v} [MulAction G Ω] [Nonempty Ω]
    (N J : Subgroup G) (hN : IsClosed (N : Set G)) (hJ : IsClosed (J : Set G))
    (hsplit : Splits N J) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent J)
    (htrans : MulAction.IsPretransitive G Ω)
    (hclosed : ∀ x : Ω, IsClosed (MulAction.stabilizer G x : Set G))
    (hnormal : ∃ x : Ω, IntersectionNormal N (MulAction.stabilizer G x))
    (hlocal : SylowFixedPoints (Ω := Ω) J) : HasFixedPoint (Ω := Ω) J := by
  apply (hasFixedPoint_iff_internal J).mpr
  exact Proof.LocalConjugacy.corollary_1_4 N J hN hJ
    ((splits_iff_internal N J).mp hsplit) hpron hcase htrans.exists_smul_eq hclosed
    (hnormal.imp fun x hx => (intersectionNormal_iff_internal N _).mp hx)
    ((sylowFixedPoints_iff_internal J).mp hlocal)



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
  (N J :
    @Subgroup.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (ProfiniteGrp.group.{u} G))
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
  (hJ :
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
        J))
  (hsplit :
    @LocalConjugacy.Splits.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (ProfiniteGrp.group.{u} G) N J)
  (hpron :
    @LocalConjugacy.Pronilpotent.{u}
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
      (@Subgroup.toGroup.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        (ProfiniteGrp.group.{u} G) N)
      (@instTopologicalSpaceSubtype.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        (fun
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
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))))
  (hcase :
    Or
      (@LocalConjugacy.Prosupersolvable.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        (ProfiniteGrp.group.{u} G)
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G))))
      (@LocalConjugacy.Pronilpotent.{u}
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
            J x)
        (@Subgroup.toGroup.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          (ProfiniteGrp.group.{u} G) J)
        (@instTopologicalSpaceSubtype.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          (fun
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
              J x)
          (TopCat.str.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G))))))
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
  (hnormal :
    @Exists.{v + 1} Ω fun (x : Ω) =>
      @LocalConjugacy.IntersectionNormal.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} G)))
        (ProfiniteGrp.group.{u} G) N
        (@MulAction.stabilizer.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} G)))
          Ω (ProfiniteGrp.group.{u} G) inst x))
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
      inst J),
  @LocalConjugacy.HasFixedPoint.{u, v}
    (TopCat.carrier.{u}
      (@CompHausLike.toTop.{u}
        (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
        (ProfiniteGrp.toProfinite.{u} G)))
    Ω (ProfiniteGrp.group.{u} G) inst J :=
  @LocalConjugacy.corollary_1_4_preparedProof
