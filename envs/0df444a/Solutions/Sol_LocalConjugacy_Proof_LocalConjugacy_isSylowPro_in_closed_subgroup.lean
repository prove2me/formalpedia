-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.isSylowPro_in_closed_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:14:54.430705+00:00
-- url     : https://prove2.me/submissions/b0419adb-9597-42b3-a70d-b5880bb51b67

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isProP_of_quotient_images

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy



/-- A continuous homomorphism into a discrete group sends pro-`p` elements
to elements of finite `p`-power order. No finiteness of the codomain is needed. -/
private theorem image_pow {G F : Type*} [Group G] [Group F]
    [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]
    {p : ℕ} (h : IsProP p G) (f : G →* F) (hf : Continuous f) (x : G) :
    ∃ k : ℕ, f x ^ p ^ k = 1 := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  obtain ⟨k, hk⟩ := h U (QuotientGroup.mk' U.toSubgroup x)
  refine ⟨k, ?_⟩
  have he := congrArg (QuotientGroup.lift U.toSubgroup f (by rfl)) hk
  simpa using he



private theorem isPGroup_map_of_continuous {G F : Type*} [Group G] [Group F]
    [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]
    {p : ℕ} (H : Subgroup G) (hH : IsProP p H) (f : G →* F) (hf : Continuous f) :
    IsPGroup p (H.map f) := by
  intro z
  obtain ⟨x, hx, he⟩ := z.property
  obtain ⟨k, hk⟩ := image_pow hH (f.comp H.subtype)
    (hf.comp continuous_subtype_val) ⟨x, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  change z.val ^ p ^ k = 1
  change f x ^ p ^ k = 1 at hk
  rwa [he] at hk

/-- Continuous surjective homomorphisms preserve the pro-`p` property. -/
private theorem isProP_of_continuous_surjective {G F : Type*} [Group G] [Group F]
    [TopologicalSpace G] [TopologicalSpace F] [IsTopologicalGroup F]
    {p : ℕ} (hG : IsProP p G) (f : G →* F) (hf : Continuous f)
    (hs : Function.Surjective f) : IsProP p F := by
  intro U z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup z
  obtain ⟨x, rfl⟩ := hs y
  exact image_pow hG ((QuotientGroup.mk' U.toSubgroup).comp f)
    (continuous_quotient_mk'.comp hf) x

private theorem isProP_subgroupOf {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {p : ℕ} {P H : Subgroup G}
    (hP : IsProP p P) (hPH : P ≤ H) : IsProP p (P.subgroupOf H) := by
  let e := (Subgroup.subgroupOfEquivOfLe hPH).symm
  apply isProP_of_continuous_surjective hP e.toMonoidHom _ e.surjective
  exact (continuous_subtype_val.subtype_mk (fun x => hPH x.property)).subtype_mk
    (fun x => x.property)

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]











namespace FiniteSylowSystem
open CategoryTheory















variable {p : ℕ} [Fact p.Prime]
variable (P : (U : OpenNormalSubgroup G) → Sylow p (G ⧸ U.toSubgroup))
variable (hP : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (P U).mapSurjective (transition_surjective h) = P V)







include hP







end FiniteSylowSystem

















private theorem isProP_map {F : Type*} [Group F] [TopologicalSpace F]
    {p : ℕ} (H : Subgroup F) (hH : IsProP p H) (f : F →* G) (hf : Continuous f) :
    IsProP p (H.map f) := by
  apply isProP_of_quotient_images
  intro U
  rw [Subgroup.map_map]
  exact isPGroup_map_of_continuous H hH _ (continuous_quotient_mk'.comp hf)











end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]









private theorem isSylowPro_in_closed_subgroup_preparedProof {p : ℕ} {H P L : Subgroup G}
    (hL : IsClosed (L : Set G)) (hP : IsSylowPro p H P) (hHL : H ≤ L) :
    IsSylowPro p (H.subgroupOf L) (P.subgroupOf L) := by
  letI := profinite_closed_subgroup L hL
  refine ⟨fun _ hx => hP.1 hx, hP.2.1.preimage continuous_subtype_val,
    isProP_subgroupOf hP.2.2.1 (hP.1.trans hHL), ?_⟩
  intro Q hQH hQc hQp hPQ
  have he : Q.map L.subtype = P := hP.2.2.2 _
    (by rintro _ ⟨x, hx, rfl⟩; exact hQH hx)
    (hQc.isCompact.image continuous_subtype_val).isClosed
    (isProP_map Q hQp L.subtype continuous_subtype_val)
    (by simpa only [Subgroup.map_subgroupOf_eq_of_le (hP.1.trans hHL)] using
      (Subgroup.map_mono hPQ : (P.subgroupOf L).map L.subtype ≤ Q.map L.subtype))
  apply Subgroup.map_injective L.subtype_injective
  rwa [Subgroup.map_subgroupOf_eq_of_le (hP.1.trans hHL)]



end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] {p : Nat} {H P L : @Subgroup.{u_1} G inst}
  (hL :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) L))
  (hP : @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p G inst inst_1 H P)
  (hHL :
    @LE.le.{u_1} (@Subgroup.{u_1} G inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
      H L),
  @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p
    (@Subtype.{u_1 + 1} G fun (x : G) =>
      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) L x)
    (@Subgroup.toGroup.{u_1} G inst L)
    (@instTopologicalSpaceSubtype.{u_1} G
      (fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) L x)
      inst_1)
    (@Subgroup.subgroupOf.{u_1} G inst H L) (@Subgroup.subgroupOf.{u_1} G inst P L) :=
  @LocalConjugacy.Proof.LocalConjugacy.isSylowPro_in_closed_subgroup_preparedProof
