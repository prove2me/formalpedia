-- Prove2me | solution 1 for LocalConjugacy.corollary_1_3
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T18:21:27.547406+00:00
-- url     : https://prove2.me/submissions/4903e007-50eb-42d1-92f5-19e7f711d005

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





end LocalConjugacy

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


/-!
Proofs of the eleven numbered results in the public draft. Each statement is
copied at Lean syntax offsets from the submitted target. The proofs invoke the
ported arguments through proved interface conversions; the pointed cohomology
claims include preservation of the identity class explicitly.
-/
universe u v
open LocalConjugacy

















/-- The exact draft statement, proved by the corresponding ported paper argument. -/
private theorem LocalConjugacy.corollary_1_3_preparedProof {G : ProfiniteGrp.{u}} (N J H : Subgroup G)
    (hN : IsClosed (N : Set G)) (hJ : IsClosed (J : Set G))
    (hH : IsClosed (H : Set G)) (hsplit : Splits N J)
    (hpron : Pronilpotent N) (hcase : Prosupersolvable G ∨ Pronilpotent J)
    (hnormal : IntersectionNormal N H) (hlocal : LocallyContains H J) :
    ∃ g : G, conjugate g J ≤ H := by
  exact Proof.LocalConjugacy.corollary_1_3 N J H hN hJ hH
    ((splits_iff_internal N J).mp hsplit) hpron hcase
    ((intersectionNormal_iff_internal N H).mp hnormal) hlocal





end

universe u

theorem solution :
∀ {G : ProfiniteGrp.{u}}
  (N J H :
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
  (hnormal :
    @LocalConjugacy.IntersectionNormal.{u}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} G)))
      (ProfiniteGrp.group.{u} G) N H)
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
      H J),
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
        (ProfiniteGrp.group.{u} G) g J)
      H :=
  @LocalConjugacy.corollary_1_3_preparedProof
