-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T18:06:53.044359+00:00
-- url     : https://prove2.me/submissions/0b2be9f0-bf99-414c-9be7-c7de65aaaccb

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_FiniteSylowSystem_map_subgroup
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_card_map_quotient_lt_finite_kernel
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_card_subgroupOf_lt_finite_kernel
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_conjugate_of_mutual_inclusions_finiteIndex
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_conjugate_of_normal_intersection_quotients
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_finite_complement_conjugacy
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_finite_normal_intersection_image
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isProP_of_quotient_images
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_of_full_images
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_locallyConjugate_generated_profinite
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_nilpotent_coprime_split
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_normal_inf_of_common_sylow_profinite
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_profinite_conjugacy_case_subgroup
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_profinite_quotient
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_relIndex_sup_dvd_card
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_sylowPro_map

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

variable {G F : Type*} [Group G] [Group F]

private theorem conjugate_comp (g h : G) (H : Subgroup G) :
    conjugate g (conjugate h H) = conjugate (g * h) H := by
  unfold conjugate
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

@[simp] private theorem conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  unfold conjugate
  have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  change H.map (MulAut.conj (1 : G)).toMonoidHom = H
  rw [he, Subgroup.map_id]

@[simp] private theorem conjugate_inv_cancel (g : G) (H : Subgroup G) :
    conjugate g⁻¹ (conjugate g H) = H := by
  rw [conjugate_comp, inv_mul_cancel, conjugate_one]

private theorem conjugate_mono (g : G) {H K : Subgroup G} (h : H ≤ K) :
    conjugate g H ≤ conjugate g K := Subgroup.map_mono h

private theorem conjugate_map (f : G →* F) (g : G) (H : Subgroup G) :
    (conjugate g H).map f = conjugate (f g) (H.map f) := by
  unfold conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

private theorem conjugate_le_iff (g : G) (H K : Subgroup G) :
    conjugate g H ≤ K ↔ H ≤ conjugate g⁻¹ K := by
  constructor
  · intro h
    simpa using conjugate_mono g⁻¹ h
  · intro h
    simpa only [conjugate_comp, mul_inv_cancel, conjugate_one] using conjugate_mono g h



end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

/-- Closed subgroups are separated by their images in finite continuous
quotients. This supplies the separation step of the compactness argument. -/
private theorem mem_of_mem_sup_openNormal (H : Subgroup G) (hH : IsClosed (H : Set G))
    (x : G) (hx : ∀ U : OpenNormalSubgroup G, x ∈ H ⊔ U.toSubgroup) : x ∈ H := by
  let HC : ClosedSubgroup G := { toSubgroup := H, isClosed' := hH }
  change x ∈ HC.toSubgroup
  rw [ProfiniteGrp.closedSubgroup_eq_sInf_open HC]
  apply Subgroup.mem_sInf.mpr
  intro V hV
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hV.1 V.one_mem
  exact (sup_le hV.2 hU) (hx U)





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













private theorem exists_compatible (p : ℕ) [Fact p.Prime] :
    ∃ P : (U : OpenNormalSubgroup G) → Sylow p (G ⧸ U.toSubgroup),
      ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
        (P U).mapSurjective (transition_surjective h) = P V := by
  let : ∀ U, Finite ((functor (G := G) p).obj U) := fun U =>
    inferInstanceAs (Finite (Sylow p (G ⧸ U.toSubgroup)))
  let : ∀ U, Nonempty ((functor (G := G) p).obj U) := fun U =>
    inferInstanceAs (Nonempty (Sylow p (G ⧸ U.toSubgroup)))
  obtain ⟨P, hP⟩ := nonempty_sections_of_finite_cofiltered_system (functor (G := G) p)
  exact ⟨P, fun U V h => hP (homOfLE h)⟩

variable {p : ℕ} [Fact p.Prime]
variable (P : (U : OpenNormalSubgroup G) → Sylow p (G ⧸ U.toSubgroup))
variable (hP : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (P U).mapSurjective (transition_surjective h) = P V)



private theorem mem_subgroup (x : G) :
    x ∈ subgroup P ↔ ∀ U, QuotientGroup.mk' U.toSubgroup x ∈ P U := by
  simp only [subgroup, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

private theorem subgroup_closed : IsClosed (subgroup P : Set G) := by
  rw [show (subgroup P : Set G) = ⋂ U : OpenNormalSubgroup G,
    (QuotientGroup.mk' U.toSubgroup) ⁻¹' (P U).toSubgroup.carrier by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact mem_subgroup P x]
  apply isClosed_iInter
  intro U
  have hc : IsClosed (P U).toSubgroup.carrier := isClosed_discrete _
  exact hc.preimage (continuous_quotient_mk' : Continuous (QuotientGroup.mk' U.toSubgroup))

include hP







end FiniteSylowSystem

/-- A profinite group has a closed pro-`p` subgroup whose image in every
continuous finite quotient is a Sylow subgroup. -/
private theorem exists_full_sylow (p : ℕ) [Fact p.Prime] :
    ∃ P : Subgroup G, IsClosed (P : Set G) ∧ IsProP p P ∧
      ∀ U : OpenNormalSubgroup G, ∃ S : Sylow p (G ⧸ U.toSubgroup),
        P.map (QuotientGroup.mk' U.toSubgroup) = (S : Subgroup _) := by
  obtain ⟨S, hS⟩ := FiniteSylowSystem.exists_compatible (G := G) p
  refine ⟨FiniteSylowSystem.subgroup S, FiniteSylowSystem.subgroup_closed S, ?_, ?_⟩
  · apply isProP_of_quotient_images
    intro U
    rw [FiniteSylowSystem.map_subgroup S hS U]
    exact (S U).isPGroup'
  · intro U
    exact ⟨S U, FiniteSylowSystem.map_subgroup S hS U⟩





private theorem exists_sylowPro (p : ℕ) [Fact p.Prime] :
    ∃ P : Subgroup G, IsSylowPro p ⊤ P := by
  obtain ⟨P, hc, _, hf⟩ := exists_full_sylow (G := G) p
  exact ⟨P, isSylowPro_of_full_images P hc hf⟩

private theorem conjugate_closed (g : G) (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    IsClosed (conjugate g H : Set G) := by
  have hc : Continuous (fun x : G => g * x * g⁻¹) :=
    (continuous_const.mul continuous_id).mul continuous_const
  exact (hH.isCompact.image hc).isClosed

private theorem conjugate_isProP {p : ℕ} (g : G) (H : Subgroup G) (hH : IsProP p H) :
    IsProP p (conjugate g H) := by
  apply isProP_of_quotient_images
  intro U
  unfold conjugate
  rw [Subgroup.map_map]
  apply isPGroup_map_of_continuous H hH
  exact continuous_quotient_mk'.comp
    ((continuous_const.mul continuous_id).mul continuous_const)





private theorem isProP_map {F : Type*} [Group F] [TopologicalSpace F]
    {p : ℕ} (H : Subgroup F) (hH : IsProP p H) (f : F →* G) (hf : Continuous f) :
    IsProP p (H.map f) := by
  apply isProP_of_quotient_images
  intro U
  rw [Subgroup.map_map]
  exact isPGroup_map_of_continuous H hH _ (continuous_quotient_mk'.comp hf)

private theorem isSylowPro_map_subtype {p : ℕ} (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (P : Subgroup H) (hP : IsSylowPro p ⊤ P) :
    IsSylowPro p H (P.map H.subtype) := by
  letI := profinite_closed_subgroup H hH
  refine ⟨?_, ?_, isProP_map P hP.2.2.1 H.subtype continuous_subtype_val, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.property
  · exact (hP.2.1.isCompact.image continuous_subtype_val).isClosed
  · intro Q hQH hQc hQp hPQ
    have he : Q.subgroupOf H = P := hP.2.2.2 _ le_top
      (hQc.preimage continuous_subtype_val) (isProP_subgroupOf hQp hQH)
      (Subgroup.map_le_iff_le_comap.mp hPQ)
    rw [← he, Subgroup.map_subgroupOf_eq_of_le hQH]



private theorem exists_sylowPro_subgroup (p : ℕ) [Fact p.Prime] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) : ∃ P : Subgroup G, IsSylowPro p H P := by
  letI := profinite_closed_subgroup H hH
  obtain ⟨P, hP⟩ := exists_sylowPro (G := H) p
  exact ⟨P.map H.subtype, isSylowPro_map_subtype H hH P hP⟩

private theorem isSylowPro_conjugate {p : ℕ} (g : G) (H P : Subgroup G)
    (hP : IsSylowPro p H P) : IsSylowPro p (conjugate g H) (conjugate g P) := by
  refine ⟨conjugate_mono g hP.1, conjugate_closed g P hP.2.1,
    conjugate_isProP g P hP.2.2.1, ?_⟩
  intro Q hQH hQc hQp hPQ
  have he : conjugate g⁻¹ Q = P := hP.2.2.2 _
    (by simpa only [conjugate_inv_cancel] using conjugate_mono g⁻¹ hQH)
    (conjugate_closed g⁻¹ Q hQc) (conjugate_isProP g⁻¹ Q hQp)
    ((conjugate_le_iff g P Q).mp hPQ)
  rw [← he, conjugate_comp, mul_inv_cancel, conjugate_one]

private theorem locallyConjugate_of_conjugate (H K : Subgroup G)
    (hH : IsClosed (H : Set G)) (hconj : Conjugate H K) : LocallyConjugate H K := by
  obtain ⟨g, rfl⟩ := hconj
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := exists_sylowPro_subgroup p H hH
  exact ⟨P, conjugate g P, hP, isSylowPro_conjugate g H P hP, g, rfl⟩

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

/-- A continuous discrete quotient of a prosupersolvable group is
supersolvable, with the actual normal cyclic series transported. -/
private theorem supersolvable_of_prosupersolvable_surjective (hG : Prosupersolvable G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Supersolvable F := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  exact supersolvable_of_surjective (hG U) (QuotientGroup.kerLift f)
    (QuotientGroup.lift_surjective_of_surjective _ f hs le_rfl)



end Topology

section Discrete
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

private theorem pronilpotent_iff_nilpotent : Pronilpotent G ↔ Group.IsNilpotent G := by
  constructor
  · intro h
    exact nilpotent_of_pronilpotent_surjective h (MonoidHom.id G) continuous_id Function.surjective_id
  · intro h
    letI := h
    intro U
    infer_instance



end Discrete
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open scoped Pointwise

section Algebra
variable {G F : Type*} [Group G] [Group F]

private theorem sup_eq_top_of_supplements (N H : Subgroup G) (h : Supplements N H) :
    N ⊔ H = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n, hn, y, hy, rfl⟩ := h x
  exact (N ⊔ H).mul_mem ((show N ≤ N ⊔ H from le_sup_left) hn)
    ((show H ≤ N ⊔ H from le_sup_right) hy)



private theorem supplements_map (N H : Subgroup G) (h : Supplements N H)
    (f : G →* F) (hf : Function.Surjective f) : Supplements (N.map f) (H.map f) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨n, hn, z, hz, rfl⟩ := h x
  exact ⟨f n, Subgroup.mem_map_of_mem f hn, f z, Subgroup.mem_map_of_mem f hz,
    (map_mul f n z).symm⟩







end Algebra

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Descent
variable {J F N : Type*} [Group J] [Group F] [Group N]
  [TopologicalSpace J] [TopologicalSpace F] [TopologicalSpace N]
  [MulDistribMulAction J N] [MulDistribMulAction F N]



private theorem subgroupImageHom_surjective (P : Subgroup J) (π : J →* F) :
    Function.Surjective (subgroupImageHom P π) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

namespace Cocycle


variable (P : Subgroup J) (π : J →* F)
  (ha : ∀ (j : J) (n : N), π j • n = j • n) (f : Cocycle (N := N) P)
  (hf : ∀ x y : P, π x = π y → f.toFun x = f.toFun y)











end Cocycle
end Descent

section OpenNormal
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N] [Finite N]





end OpenNormal
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

namespace FiniteSubgroupSystem
open FiniteSylowSystem
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
variable (S : (U : OpenNormalSubgroup G) → Subgroup (G ⧸ U.toSubgroup))
variable (hS : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (S U).map (transition h) = S V)







include hS








end FiniteSubgroupSystem

section ProfiniteHall
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
open FiniteSylowSystem
open scoped Pointwise

private theorem subgroup_le_of_finite_images (H K : Subgroup G) (hK : IsClosed (K : Set G))
    (h : ∀ U : OpenNormalSubgroup G,
      H.map (QuotientGroup.mk' U.toSubgroup) ≤ K.map (QuotientGroup.mk' U.toSubgroup)) :
    H ≤ K := by
  intro x hx
  apply mem_of_mem_sup_openNormal K hK x
  intro U
  have hm := h U (Subgroup.mem_map_of_mem (QuotientGroup.mk' U.toSubgroup) hx)
  change x ∈ (K.map (QuotientGroup.mk' U.toSubgroup)).comap (QuotientGroup.mk' U.toSubgroup) at hm
  simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using hm



















namespace HallComplementSystem
open CategoryTheory
variable (hG : Prosupersolvable G) (n : ℕ) (P : Subgroup G)









end HallComplementSystem



end ProfiniteHall
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

private theorem prosupersolvable_of_continuous_surjective (hG : Prosupersolvable G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Prosupersolvable F := by
  intro U
  exact supersolvable_of_prosupersolvable_surjective hG
    ((QuotientGroup.mk' U.toSubgroup).comp f)
    (continuous_quotient_mk'.comp hf) ((QuotientGroup.mk'_surjective U.toSubgroup).comp hs)

end Maps

section Algebra
variable {G : Type*} [Group G]



private theorem supplements_conjugate (N H : Subgroup G) [N.Normal]
    (hs : Supplements N H) (g : G) : Supplements N (conjugate g H) := by
  intro x
  obtain ⟨n, hn, h, hh, he⟩ := hs (g⁻¹ * x * g)
  refine ⟨g * n * g⁻¹, (inferInstance : N.Normal).conj_mem n hn g,
    g * h * g⁻¹, Subgroup.mem_map_of_mem _ hh, ?_⟩
  calc
    (g * n * g⁻¹) * (g * h * g⁻¹) = g * (n * h) * g⁻¹ := by group
    _ = x := by rw [he]; group





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

section Algebra
variable {G F : Type*} [Group G] [Group F]

private theorem Conjugate.symm {H K : Subgroup G} (h : Conjugate H K) : Conjugate K H := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨g⁻¹, conjugate_inv_cancel g H⟩

private theorem Conjugate.trans {H K L : Subgroup G} (h : Conjugate H K)
    (h' : Conjugate K L) : Conjugate H L := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨k, hk⟩ := h'
  exact ⟨k * g, (conjugate_comp k g H).symm.trans hk⟩

private theorem conjugate_eq_self_of_mem (H : Subgroup G) {g : G} (hg : g ∈ H) :
    conjugate g H = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
  · intro x hx
    refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

private theorem normal_conjugator (N H K : Subgroup G) (hs : Supplements N H)
    (hc : Conjugate H K) : ∃ n : N, conjugate (n : G) H = K := by
  obtain ⟨g, hg⟩ := hc
  obtain ⟨n, hn, h, hh, rfl⟩ := hs g
  refine ⟨⟨n, hn⟩, ?_⟩
  rw [← conjugate_comp, conjugate_eq_self_of_mem H hh] at hg
  exact hg

private theorem conjugate_of_map_eq (D H K : Subgroup G) [D.Normal]
    (hDH : D ≤ H) (hDK : D ≤ K)
    (hc : Conjugate (H.map (QuotientGroup.mk' D)) (K.map (QuotientGroup.mk' D))) :
    Conjugate H K := by
  obtain ⟨q, hq⟩ := hc
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D q
  refine ⟨g, ?_⟩
  have he := congrArg (Subgroup.comap (QuotientGroup.mk' D)) hq
  rw [← conjugate_map, Subgroup.comap_map_eq, Subgroup.comap_map_eq,
    QuotientGroup.ker_mk', sup_eq_left.mpr hDK] at he
  have hDg : D ≤ conjugate g H := by
    rw [← Subgroup.Normal.map_conj_eq D g]
    exact Subgroup.map_mono hDH
  rwa [sup_eq_left.mpr hDg] at he

private theorem nilpotent_of_injective_hom (f : G →* F) (hi : Function.Injective f)
    [Group.IsNilpotent F] : Group.IsNilpotent G := by
  let e : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hi (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  exact Group.nilpotent_of_mulEquiv e.symm





end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [Profinite G] [TopologicalSpace F] [Finite F] [DiscreteTopology F]



private theorem LocallyConjugate.conjugate_left {H K : Subgroup G}
    (h : LocallyConjugate H K) (g : G) : LocallyConjugate (conjugate g H) K := by
  intro p hp
  obtain ⟨P, Q, hP, hQ, k, hk⟩ := h p hp
  refine ⟨conjugate g P, Q, isSylowPro_conjugate g H P hP, hQ, k * g⁻¹, ?_⟩
  rw [conjugate_comp, inv_mul_cancel_right]
  exact hk

end Topology

section Finite
variable {G : Type*} [Group G] [Finite G]







end Finite
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open scoped Pointwise

section Algebra
variable {G F : Type*} [Group G] [Group F]

private theorem Conjugate.map {H K : Subgroup G} (h : Conjugate H K) (f : G →* F) :
    Conjugate (H.map f) (K.map f) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨f g, (conjugate_map f g H).symm.trans (congrArg (Subgroup.map f) hg)⟩

private theorem supplements_subgroupOf (N H L : Subgroup G) (hs : Supplements N H) (hHL : H ≤ L) :
    Supplements (N.subgroupOf L) (H.subgroupOf L) := by
  intro x
  obtain ⟨n, hn, h, hh, he⟩ := hs x
  have hnL : n ∈ L := by
    have he' : n = (x : G) * h⁻¹ := by rw [← he]; group
    rw [he']
    exact L.mul_mem x.property (L.inv_mem (hHL hh))
  exact ⟨⟨n, hnL⟩, hn, ⟨h, hHL hh⟩, hh, Subtype.ext he⟩

private theorem nilpotent_subgroupOf (N L : Subgroup G) [Group.IsNilpotent N] :
    Group.IsNilpotent (N.subgroupOf L) := by
  let f : N.subgroupOf L →* N :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  apply nilpotent_of_injective_hom f
  intro x y h
  have hv : x.val.val = y.val.val := congrArg (fun z : N => (z : G)) h
  exact Subtype.ext (Subtype.ext hv)

private theorem nilpotent_subgroup_map (N : Subgroup G) [Group.IsNilpotent N] (f : G →* F) :
    Group.IsNilpotent (N.map f) := by
  let φ : N →* N.map f := (f.comp N.subtype).codRestrict _
    (fun x => Subgroup.mem_map_of_mem f x.property)
  apply Group.nilpotent_of_surjective φ
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩





end Algebra

section Finite
variable {G : Type*} [Group G] [Finite G]





/-- Coprimeness supplies the intersection identity used in the paper's
reduction to a single coefficient prime. -/
private theorem inf_sup_eq_of_coprime (A B H : Subgroup G) [A.Normal] [B.Normal]
    (hcop : (Nat.card A).Coprime (Nat.card B)) : (A ⊔ H) ⊓ (B ⊔ H) = H := by
  let D := (A ⊔ H) ⊓ (B ⊔ H)
  have hHD : H ≤ D := le_inf le_sup_right le_sup_right
  have hA : H.relIndex D ∣ Nat.card A :=
    (dvd_of_mul_right_eq _ (Subgroup.relIndex_mul_relIndex H D (A ⊔ H) hHD inf_le_left)).trans
      (relIndex_sup_dvd_card A H)
  have hB : H.relIndex D ∣ Nat.card B :=
    (dvd_of_mul_right_eq _ (Subgroup.relIndex_mul_relIndex H D (B ⊔ H) hHD inf_le_right)).trans
      (relIndex_sup_dvd_card B H)
  exact le_antisymm (Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop hA hB)) hHD

omit [Finite G] in
private theorem conjugate_le_sup_of_quotient (D H K : Subgroup G) [D.Normal]
    (n : G) (he : conjugate (QuotientGroup.mk' D n) (H.map (QuotientGroup.mk' D)) ≤
      K.map (QuotientGroup.mk' D)) : conjugate n H ≤ D ⊔ K := by
  have h := Subgroup.comap_mono (f := QuotientGroup.mk' D) he
  rw [← conjugate_map, Subgroup.comap_map_eq, Subgroup.comap_map_eq,
    QuotientGroup.ker_mk', sup_comm K D] at h
  exact le_sup_left.trans h





omit [Finite G] in
private theorem quotient_conjugator_from_factor (A B N H K : Subgroup G) [A.Normal]
    (hs : Supplements N H) (hAB : A ⊔ B = N)
    (hc : Conjugate (H.map (QuotientGroup.mk' A)) (K.map (QuotientGroup.mk' A))) :
    ∃ b : B, conjugate (QuotientGroup.mk' A b) (H.map (QuotientGroup.mk' A)) =
      K.map (QuotientGroup.mk' A) := by
  let π := QuotientGroup.mk' A
  have ha : A.map π = ⊥ := QuotientGroup.map_mk'_self A
  have hn : N.map π = B.map π := by rw [← hAB, Subgroup.map_sup, ha, bot_sup_eq]
  have hs' := supplements_map N H hs π (QuotientGroup.mk'_surjective A)
  rw [hn] at hs'
  obtain ⟨⟨_, b, hb, rfl⟩, he⟩ := normal_conjugator (B.map π) (H.map π) (K.map π) hs' hc
  exact ⟨⟨b, hb⟩, he⟩

end Finite
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Maps
variable {G F : Type*} [Group G] [Group F] [TopologicalSpace G] [TopologicalSpace F]
  [IsTopologicalGroup G] [IsTopologicalGroup F]

private theorem pronilpotent_subgroup_image (N : Subgroup G) (hN : Pronilpotent N)
    (f : G →* F) (hf : Continuous f) : Pronilpotent (N.map f) :=
  pronilpotent_of_continuous_surjective hN (subgroupImageHom N f)
    ((hf.comp continuous_subtype_val).subtype_mk _) (subgroupImageHom_surjective N f)







private theorem pronilpotent_quotient_image (N : Subgroup G) [N.Normal]
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) [(N.map f).Normal]
    (h : Pronilpotent (G ⧸ N)) : Pronilpotent (F ⧸ N.map f) := by
  let φ := QuotientGroup.map N (N.map f) f (Subgroup.le_comap_map f N)
  apply pronilpotent_of_continuous_surjective h φ
  · apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    exact continuous_quotient_mk'.comp hf
  · intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (N.map f) y
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨QuotientGroup.mk' N x, rfl⟩

end Maps

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! The reductions needed to run Proposition 3.2's induction on `|N|`
while the ambient profinite group is allowed to be infinite. -/

namespace LocalConjugacy

section Algebra
variable {G : Type*} [Group G]

private theorem finiteIndex_of_finite_supplement (N H : Subgroup G) [Finite N]
    (hs : Supplements N H) : H.FiniteIndex := by
  let f : N → G ⧸ H := fun n => QuotientGroup.mk (n : G)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn, h, hh, rfl⟩ := hs x
    refine ⟨⟨n, hn⟩, QuotientGroup.eq.mpr ?_⟩
    simpa only [inv_mul_cancel_left] using hh
  letI : Finite (G ⧸ H) := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient







end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [Profinite G] [TopologicalSpace F] [Profinite F]

private theorem locallyConjugate_map (H K : Subgroup G)
    (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (h : LocallyConjugate H K) (f : G →* F) (hf : Continuous f) :
    LocallyConjugate (H.map f) (K.map f) := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, Q, hP, hQ, g, hg⟩ := h p hp
  exact ⟨P.map f, Q.map f, sylowPro_map H P hH hP f hf,
    sylowPro_map K Q hK hQ f hf, f g,
    (conjugate_map f g P).symm.trans (congrArg (Subgroup.map f) hg)⟩



private theorem profinite_conjugacy_case_map (N : Subgroup G) [N.Normal]
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) [(N.map f).Normal]
    (h : Prosupersolvable G ∨ Pronilpotent (G ⧸ N)) :
    Prosupersolvable F ∨ Pronilpotent (F ⧸ N.map f) := by
  rcases h with h | h
  · exact Or.inl (prosupersolvable_of_continuous_surjective h f hf hs)
  · exact Or.inr (pronilpotent_quotient_image N f hf hs h)

end Topology

section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]





/-- The coprime intersection identity, without finiteness of the ambient group. -/
private theorem inf_sup_eq_of_coprime_profinite (A B H : Subgroup G) [A.Normal] [B.Normal]
    (hH : IsClosed (H : Set G)) (hcop : (Nat.card A).Coprime (Nat.card B)) :
    (A ⊔ H) ⊓ (B ⊔ H) = H := by
  apply le_antisymm _ (le_inf le_sup_right le_sup_right)
  apply subgroup_le_of_finite_images _ H hH
  intro U
  let π := QuotientGroup.mk' U.toSubgroup
  have hc : (Nat.card (A.map π)).Coprime (Nat.card (B.map π)) :=
    hcop.of_dvd (A.card_map_dvd π) (B.card_map_dvd π)
  rw [← inf_sup_eq_of_coprime (A.map π) (B.map π) (H.map π) hc]
  simpa only [Subgroup.map_sup] using
    (le_inf (Subgroup.map_mono (show (A ⊔ H) ⊓ (B ⊔ H) ≤ A ⊔ H from inf_le_left))
      (Subgroup.map_mono (show (A ⊔ H) ⊓ (B ⊔ H) ≤ B ⊔ H from inf_le_right)))

private theorem merge_coprime_conjugators_profinite (A B H K : Subgroup G) [A.Normal] [B.Normal]
    (hK : IsClosed (K : Set G)) (hcop : (Nat.card A).Coprime (Nat.card B))
    (hdis : Disjoint A B) (a : A) (b : B)
    (hA : conjugate (b : G) H ≤ A ⊔ K) (hB : conjugate (a : G) H ≤ B ⊔ K) :
    conjugate ((a : G) * b) H ≤ K := by
  rw [← inf_sup_eq_of_coprime_profinite A B K hK hcop]
  apply le_inf
  · rw [← conjugate_comp]
    exact (conjugate_mono (a : G) hA).trans_eq
      (conjugate_eq_self_of_mem (A ⊔ K) ((show A ≤ A ⊔ K from le_sup_left) a.property))
  · have hc := Subgroup.commute_of_normal_of_disjoint A B inferInstance inferInstance hdis
      a b a.property b.property
    rw [hc.eq, ← conjugate_comp]
    exact (conjugate_mono (b : G) hB).trans_eq
      (conjugate_eq_self_of_mem (B ⊔ K) ((show B ≤ B ⊔ K from le_sup_left) b.property))

end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! Proposition 3.2's induction on the order of the finite normal subgroup.
The ambient group is profinite throughout, as in the current manuscript. -/

namespace LocalConjugacy
universe u

private theorem finite_kernel_conjugacy_aux (n : ℕ) :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]
      (N H K : Subgroup G) [N.Normal] [Finite N] [Group.IsNilpotent N],
      Nat.card N = n → IsClosed (N : Set G) → IsClosed (H : Set G) →
      IsClosed (K : Set G) →
      (Prosupersolvable G ∨ Pronilpotent (G ⧸ N)) →
      Supplements N H → Supplements N K → LocallyConjugate H K → Conjugate H K := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ N H K _ _ _ hcard hN hH hK hcase hsH hsK hlocal
    have hquot (X Y D : Subgroup G) [D.Normal] (hDN : D ≤ N) (hD : D ≠ ⊥)
        (hX : IsClosed (X : Set G)) (hY : IsClosed (Y : Set G))
        (hsX : Supplements N X) (hsY : Supplements N Y) (hl : LocallyConjugate X Y) :
        Conjugate (X.map (QuotientGroup.mk' D)) (Y.map (QuotientGroup.mk' D)) := by
      letI : Finite D := Finite.of_injective (Subgroup.inclusion hDN)
        (Subgroup.inclusion_injective hDN)
      have hDc : IsClosed (D : Set G) :=
        (Set.finite_coe_iff.mp (inferInstance : Finite D)).isClosed
      letI := profinite_quotient D hDc
      let π := QuotientGroup.mk' D
      letI := nilpotent_subgroup_map N π
      letI : Finite (N.map π) := Finite.of_surjective (subgroupImageHom N π)
        (subgroupImageHom_surjective N π)
      exact ih _ (hcard ▸ card_map_quotient_lt_finite_kernel N D hDN hD)
        (N.map π) (X.map π) (Y.map π) rfl
        (hN.isCompact.image continuous_quotient_mk').isClosed
        (hX.isCompact.image continuous_quotient_mk').isClosed
        (hY.isCompact.image continuous_quotient_mk').isClosed
        (profinite_conjugacy_case_map N π continuous_quotient_mk'
          (QuotientGroup.mk'_surjective D) hcase)
        (supplements_map N X hsX π (QuotientGroup.mk'_surjective D))
        (supplements_map N Y hsY π (QuotientGroup.mk'_surjective D))
        (locallyConjugate_map X Y hX hY hl π continuous_quotient_mk')
    by_cases hpgroup : ∃ p : ℕ, p.Prime ∧ IsPGroup p N
    · obtain ⟨p, hp, hNp⟩ := hpgroup
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨P, Q, hP, hQ, g, hg⟩ := hlocal p hp
      let H' := conjugate g H
      have hH' : IsClosed (H' : Set G) := conjugate_closed g H hH
      have hsH' : Supplements N H' := supplements_conjugate N H hsH g
      have hlocal' : LocallyConjugate H' K := hlocal.conjugate_left g
      have hQH : IsSylowPro p H' Q := by
        rw [← hg]
        exact isSylowPro_conjugate g H P hP
      apply Conjugate.trans (show Conjugate H H' from ⟨g, rfl⟩)
      by_cases hgen : H' ⊔ K = ⊤
      · obtain ⟨he, hn⟩ := normal_inf_of_common_sylow_profinite N H' K Q hH' hK hNp hQH hQ hgen
        let D := N ⊓ H'
        letI : D.Normal := hn
        by_cases hD : D = ⊥
        · exact (finite_complement_conjugacy N H' K hN hH' hK
            (pronilpotent_iff_nilpotent.mpr inferInstance) hcase
            hsH' hsK hD (he ▸ hD)).mpr hlocal'
        · have hDK : D ≤ K := by rw [show D = N ⊓ K from he]; exact inf_le_right
          exact conjugate_of_map_eq D H' K inf_le_right hDK
            (hquot H' K D inf_le_left hD hH' hK hsH' hsK hlocal')
      · let L := H' ⊔ K
        letI := finiteIndex_of_finite_supplement N H' hsH'
        have hL : IsClosed (L : Set G) := Subgroup.isClosed_of_isOpen _
          (Subgroup.isOpen_mono le_sup_left (H'.isOpen_of_isClosed_of_finiteIndex hH'))
        letI := profinite_closed_subgroup L hL
        have hNL : ¬ N ≤ L := by
          intro hle
          apply hgen
          apply top_unique
          rw [← sup_eq_top_of_supplements N H' hsH']
          exact sup_le hle le_sup_left
        letI := nilpotent_subgroupOf N L
        let f : N.subgroupOf L → N := fun x => ⟨x.val.val, x.property⟩
        letI : Finite (N.subgroupOf L) := Finite.of_injective f (by
          intro x y he
          have hv : x.val.val = y.val.val := congrArg (fun z : N => (z : G)) he
          exact Subtype.ext (Subtype.ext hv))
        have hl := locallyConjugate_generated_profinite N H' K Q hH' hK hL hNp hsH' hsK hQH hQ
        have hc := ih _ (hcard ▸ card_subgroupOf_lt_finite_kernel N L hNL)
          (N.subgroupOf L) (H'.subgroupOf L) (K.subgroupOf L) rfl
          (hN.preimage continuous_subtype_val) (hH'.preimage continuous_subtype_val)
          (hK.preimage continuous_subtype_val) (profinite_conjugacy_case_subgroup N L hN hL hcase)
          (supplements_subgroupOf N H' L hsH' le_sup_left)
          (supplements_subgroupOf N K L hsK le_sup_right) hl
        have hm := hc.map L.subtype
        simpa only [Subgroup.map_subgroupOf_eq_of_le (show H' ≤ L from le_sup_left),
          Subgroup.map_subgroupOf_eq_of_le (show K ≤ L from le_sup_right)] using hm
    · obtain ⟨A₀, B₀, hAc, hBc, hc, hcop, hA₀, hB₀⟩ := nilpotent_coprime_split hpgroup
      letI := hAc
      letI := hBc
      let A := A₀.map N.subtype
      let B := B₀.map N.subtype
      letI : A.Normal := inferInstance
      letI : B.Normal := inferInstance
      have hAN : A ≤ N := by
        simpa only [N.range_subtype] using A₀.map_le_range N.subtype
      have hBN : B ≤ N := by
        simpa only [N.range_subtype] using B₀.map_le_range N.subtype
      have hAB : A ⊔ B = N := by
        change A₀.map N.subtype ⊔ B₀.map N.subtype = N
        rw [← Subgroup.map_sup, hc.sup_eq_top, ← MonoidHom.range_eq_map, N.range_subtype]
      have hA : A ≠ ⊥ := by
        intro h
        apply hA₀
        apply Subgroup.map_injective N.subtype_injective
        simpa only [Subgroup.map_bot] using h
      have hB : B ≠ ⊥ := by
        intro h
        apply hB₀
        apply Subgroup.map_injective N.subtype_injective
        simpa only [Subgroup.map_bot] using h
      have hcop' : (Nat.card A).Coprime (Nat.card B) := by
        simpa only [A, B, Subgroup.card_map_of_injective N.subtype_injective] using hcop
      have hd : Disjoint A B := Subgroup.disjoint_of_coprime_natCard hcop'
      have hqA := hquot H K A hAN hA hH hK hsH hsK hlocal
      have hqB := hquot H K B hBN hB hH hK hsH hsK hlocal
      have inclusion (X Y : Subgroup G) (hY : IsClosed (Y : Set G)) (hsX : Supplements N X)
          (hAq : Conjugate (X.map (QuotientGroup.mk' A)) (Y.map (QuotientGroup.mk' A)))
          (hBq : Conjugate (X.map (QuotientGroup.mk' B)) (Y.map (QuotientGroup.mk' B))) :
          ∃ g : G, conjugate g X ≤ Y := by
        obtain ⟨b, hb⟩ := quotient_conjugator_from_factor A B N X Y hsX hAB hAq
        obtain ⟨a, ha⟩ := quotient_conjugator_from_factor B A N X Y hsX
          ((sup_comm B A).trans hAB) hBq
        exact ⟨(a : G) * b, merge_coprime_conjugators_profinite A B X Y hY hcop' hd a b
          (conjugate_le_sup_of_quotient A X Y b hb.le)
          (conjugate_le_sup_of_quotient B X Y a ha.le)⟩
      letI := finiteIndex_of_finite_supplement N H hsH
      letI := finiteIndex_of_finite_supplement N K hsK
      exact conjugate_of_mutual_inclusions_finiteIndex H K (inclusion H K hK hsH hqA hqB)
        (inclusion K H hH hsK hqA.symm hqB.symm)

/-- Proposition 3.2 (`prop:thm_main_n_nilpotent`): Theorem 1.1 for finite `N`.
Only the normal subgroup is assumed finite; the ambient profinite group is arbitrary. -/
private theorem proposition_3_2 {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]
    (N H K : Subgroup G) [N.Normal] [Finite N]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K) :
    Conjugate H K ↔ LocallyConjugate H K := by
  letI := pronilpotent_iff_nilpotent.mp hpron
  exact ⟨locallyConjugate_of_conjugate H K hH,
    finite_kernel_conjugacy_aux (Nat.card N) N H K rfl hN hH hK hcase hHN hKN⟩

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! The precise compactness system in Theorem 1.1: the quotients are by
`N ∩ U`, and their normal subgroups have finite order, although the quotients
themselves need not be finite. -/

namespace LocalConjugacy
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]





/-- Theorem 1.1 (`thm:loc_conj`), using Proposition 3.2 in each quotient by
`N ∩ U`, followed by the manuscript's compactness argument. -/
private theorem theorem_1_1_preparedProof (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K) :
    Conjugate H K ↔ LocallyConjugate H K := by
  refine ⟨locallyConjugate_of_conjugate H K hH, fun hlocal => ?_⟩
  apply conjugate_of_normal_intersection_quotients N H K hN hH hK
  intro U
  let D := N ⊓ U.toSubgroup
  letI := profinite_quotient D (hN.inter U.isClosed)
  let π := QuotientGroup.mk' D
  letI : Finite (N.map π) := finite_normal_intersection_image N U
  exact (proposition_3_2 (N.map π) (H.map π) (K.map π)
    (hN.isCompact.image continuous_quotient_mk').isClosed
    (hH.isCompact.image continuous_quotient_mk').isClosed
    (hK.isCompact.image continuous_quotient_mk').isClosed
    (pronilpotent_subgroup_image N hpron π continuous_quotient_mk')
    (profinite_conjugacy_case_map N π continuous_quotient_mk'
      (QuotientGroup.mk'_surjective D) hcase)
    (supplements_map N H hHN π (QuotientGroup.mk'_surjective D))
    (supplements_map N K hKN π (QuotientGroup.mk'_surjective D))).mpr
      (locallyConjugate_map H K hH hK hlocal π continuous_quotient_mk')

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N H K : @Subgroup.{u_1} G inst)
  [inst_3 : @Subgroup.Normal.{u_1} G inst N]
  (hN :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) N))
  (hH :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) H))
  (hK :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) K))
  (hpron :
    @LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
      (@Subgroup.toGroup.{u_1} G inst N)
      (@instTopologicalSpaceSubtype.{u_1} G
        (fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
        inst_1))
  (hcase :
    Or (@LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{u_1} G inst inst_1)
      (@LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1}
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
        (@QuotientGroup.Quotient.group.{u_1} G inst N inst_3)
        (@QuotientGroup.instTopologicalSpace.{u_1} G inst_1 inst N)))
  (hHN : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N H)
  (hKN : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N K),
  Iff (@LocalConjugacy.Proof.LocalConjugacy.Conjugate.{u_1} G inst H K)
    (@LocalConjugacy.Proof.LocalConjugacy.LocallyConjugate.{u_1} G inst inst_1 H K) :=
  @LocalConjugacy.Proof.LocalConjugacy.theorem_1_1_preparedProof
