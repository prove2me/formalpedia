-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.locallyConjugate_of_locallyContains_complement
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:27:11.609634+00:00
-- url     : https://prove2.me/submissions/44c9fa1e-7f51-49a5-9553-68c6d30e2228

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_complement_quotient_bijective
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isProP_of_quotient_images
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_profinite_quotient
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



end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Maps
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [IsTopologicalGroup F]





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
open Topology



section Images
variable {G F : Type*} [Group G] [Group F] [TopologicalSpace G] [TopologicalSpace F]
  [Profinite G] [Profinite F]







private theorem sylowPro_of_injective_map {p : ℕ} (P : Subgroup G)
    (hP : IsClosed (P : Set G)) (hp : IsProP p P)
    (f : G →* F) (hf : Continuous f) (hi : Function.Injective f)
    (hmap : IsSylowPro p ⊤ (P.map f)) : IsSylowPro p ⊤ P := by
  refine ⟨le_top, hP, hp, ?_⟩
  intro Q _ hQ hQp hPQ
  apply Subgroup.map_injective hi
  exact hmap.2.2.2 _ le_top (hQ.isCompact.image hf).isClosed
    (isProP_map Q hQp f hf) (Subgroup.map_mono hPQ)

end Images
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

private theorem supplement_image_quotient_eq_top (N H : Subgroup G) [N.Normal]
    (hs : Supplements N H) : H.map (QuotientGroup.mk' N) = ⊤ := by
  rw [← H.range_subtype, ← MonoidHom.range_comp]
  exact MonoidHom.range_eq_top_of_surjective _ (supplement_quotient_surjective N H hs)





end Maps

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy


section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

/-- Local containment in a complement is local conjugacy: the quotient by
N maps a Sylow of the supplement onto a Sylow, and is injective on H. -/
private theorem locallyConjugate_of_locallyContains_complement_preparedProof (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hc : N.IsComplement' H) (hsK : Supplements N K) (hloc : LocallyContains H K) :
    LocallyConjugate K H := by
  letI := profinite_quotient N hN
  letI := profinite_closed_subgroup H hH
  let π := QuotientGroup.mk' N
  let φ := π.comp H.subtype
  have hsH : Supplements N H := fun g => by
    obtain ⟨⟨n, h⟩, he⟩ := hc.surjective g
    exact ⟨n, n.property, h, h.property, he⟩
  have hφ := (complement_quotient_bijective N H hsH hc.disjoint.eq_bot).1
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, g, hg⟩ := hloc p hp
  let Q := conjugate g P
  have hQ := isSylowPro_conjugate g K P hP
  have himage := sylowPro_map (conjugate g K) Q (conjugate_closed g K hK) hQ
    π continuous_quotient_mk'
  rw [supplement_image_quotient_eq_top N (conjugate g K) (supplements_conjugate N K hsK g)] at himage
  have he : (Q.subgroupOf H).map φ = Q.map π := by
    rw [show φ = π.comp H.subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hg]
  rw [← he] at himage
  have hs := sylowPro_of_injective_map (Q.subgroupOf H)
    (hQ.2.1.preimage continuous_subtype_val) (isProP_subgroupOf hQ.2.2.1 hg)
    φ (continuous_quotient_mk'.comp continuous_subtype_val) hφ himage
  have hQH := isSylowPro_map_subtype H hH _ hs
  rw [Subgroup.map_subgroupOf_eq_of_le hg] at hQH
  exact ⟨P, Q, hP, hQH, g, rfl⟩





end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N H K : @Subgroup.{u_1} G inst)
  [@Subgroup.Normal.{u_1} G inst N]
  (hN :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) N))
  (hH :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) H))
  (hK :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) K))
  (hc : @Subgroup.IsComplement'.{u_1} G inst N H)
  (hsK : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N K)
  (hloc : @LocalConjugacy.Proof.LocalConjugacy.LocallyContains.{u_1} G inst inst_1 H K),
  @LocalConjugacy.Proof.LocalConjugacy.LocallyConjugate.{u_1} G inst inst_1 K H :=
  @LocalConjugacy.Proof.LocalConjugacy.locallyConjugate_of_locallyContains_complement_preparedProof
