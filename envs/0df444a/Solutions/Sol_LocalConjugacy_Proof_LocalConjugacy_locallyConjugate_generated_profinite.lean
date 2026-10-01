-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.locallyConjugate_generated_profinite
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:24:06.0241+00:00
-- url     : https://prove2.me/submissions/6ea61dc9-8bce-446e-852e-23eaf2f262f1

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_conjugate_le_full_sylow
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_index_eq_relIndex_of_supplements
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isProP_of_quotient_images
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_in_closed_subgroup
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_of_full_images
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_of_index
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_subgroupOf
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_sylowPro_map_finite

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

private theorem proP_of_isPGroup {G : Type*} [Group G] [TopologicalSpace G]
    {p : ℕ} (h : IsPGroup p G) : IsProP p G :=
  fun U => h.to_quotient U.toSubgroup

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

/-- In a discrete group, the profinite condition reduces to the ordinary
torsion definition of a `p`-group. -/
private theorem isProP_iff_isPGroup {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (p : ℕ) : IsProP p G ↔ IsPGroup p G :=
  ⟨fun h x => image_pow h (MonoidHom.id G) continuous_id x,
   proP_of_isPGroup⟩





private theorem sylow_of_isSylowPro {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] {p : ℕ} (P : Subgroup G) (hP : IsSylowPro p ⊤ P) :
    ∃ S : Sylow p G, S.toSubgroup = P := by
  exact ⟨⟨P, (isProP_iff_isPGroup p).mp hP.2.2.1,
    fun hQ hPQ => hP.2.2.2 _ le_top (isClosed_discrete _) (proP_of_isPGroup hQ) hPQ⟩, rfl⟩

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

private theorem sylow_smul_toSubgroup (p : ℕ) (g : G) (P : Sylow p G) :
    (g • P).toSubgroup = conjugate g P.toSubgroup := by
  simp only [Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.pointwise_smul_def, conjugate]
  congr 1

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

private theorem sylowPro_full_images {p : ℕ} [Fact p.Prime] (P : Subgroup G)
    (hP : IsSylowPro p ⊤ P) (U : OpenNormalSubgroup G) :
    ∃ S : Sylow p (G ⧸ U.toSubgroup),
      P.map (QuotientGroup.mk' U.toSubgroup) = (S : Subgroup _) := by
  obtain ⟨Q, hc, hp, hf⟩ := exists_full_sylow (G := G) p
  obtain ⟨g, hg⟩ := conjugate_le_full_sylow P Q hP.2.2.1 hc hf
  have he : conjugate g⁻¹ Q = P := hP.2.2.2 _ le_top
    (conjugate_closed g⁻¹ Q hc) (conjugate_isProP g⁻¹ Q hp)
    ((conjugate_le_iff g P Q).mp hg)
  obtain ⟨S, hS⟩ := hf U
  let π := QuotientGroup.mk' U.toSubgroup
  refine ⟨(π g⁻¹) • S, ?_⟩
  rw [← he, conjugate_map, hS]
  exact (sylow_smul_toSubgroup p (π g⁻¹) S).symm

private theorem sylowPro_conjugate {p : ℕ} [Fact p.Prime] (P Q : Subgroup G)
    (hP : IsSylowPro p ⊤ P) (hQ : IsSylowPro p ⊤ Q) : Conjugate P Q := by
  obtain ⟨g, hg⟩ := conjugate_le_full_sylow P Q hP.2.2.1 hQ.2.1
    (sylowPro_full_images Q hQ)
  have he : conjugate g⁻¹ Q = P := hP.2.2.2 _ le_top
    (conjugate_closed g⁻¹ Q hQ.2.1) (conjugate_isProP g⁻¹ Q hQ.2.2.1)
    ((conjugate_le_iff g P Q).mp hg)
  refine ⟨g, ?_⟩
  rw [← he, conjugate_comp, mul_inv_cancel, conjugate_one]

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





end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open scoped Pointwise

section Algebra
variable {G F : Type*} [Group G] [Group F]





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

/-- A chosen Sylow subgroup remains Sylow in every intermediate subgroup. -/
private theorem isSylowPro_of_intermediate {J : Type*} [Group J] [TopologicalSpace J]
    {p : ℕ} {H L P : Subgroup J} (hP : IsSylowPro p H P)
    (hPL : P ≤ L) (hLH : L ≤ H) : IsSylowPro p L P :=
  ⟨hPL, hP.2.1, hP.2.2.1,
    fun Q hQL hQclosed hQpro hPQ => hP.2.2.2 Q (hQL.trans hLH) hQclosed hQpro hPQ⟩

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]





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
  [TopologicalSpace G] [Profinite G] [TopologicalSpace F] [Finite F] [DiscreteTopology F]





end Topology

section Finite
variable {G : Type*} [Group G] [Finite G]



private theorem index_dvd_card_of_supplements (N H : Subgroup G) [N.Normal]
    (hs : Supplements N H) : H.index ∣ Nat.card N := by
  rw [index_eq_relIndex_of_supplements N H hs]
  exact H.relIndex_dvd_card N



end Finite
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {G : Type*} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]

private theorem sylowPro_relIndex_not_dvd {p : ℕ} [Fact p.Prime]
    {H P : Subgroup G} (hP : IsSylowPro p H P) : ¬ p ∣ P.relIndex H := by
  letI : Profinite G := ⟨⟩
  obtain ⟨S, hS⟩ := sylow_of_isSylowPro (P.subgroupOf H)
    (isSylowPro_subgroupOf H P (isClosed_discrete _) hP)
  change ¬ p ∣ (P.subgroupOf H).index
  rw [← hS]
  exact S.not_dvd_index



private theorem sylowPro_top_of_not_dvd_index {p : ℕ} [hp : Fact p.Prime]
    {H P : Subgroup G} (hP : IsSylowPro p H P) (hH : ¬ p ∣ H.index) :
    IsSylowPro p ⊤ P := by
  apply isSylowPro_of_index _ _ le_top ((isProP_iff_isPGroup p).mp hP.2.2.1)
  change ¬ p ∣ P.relIndex ⊤
  rw [Subgroup.relIndex_top_right, ← Subgroup.relIndex_mul_index hP.1]
  exact fun hd => (hp.out.dvd_mul.mp hd).elim (sylowPro_relIndex_not_dvd hP) hH

private theorem sylowPro_top_of_pGroup_supplement (N H P : Subgroup G) [N.Normal]
    {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime] (hne : q ≠ p)
    (hN : IsPGroup p N) (hs : Supplements N H) (hP : IsSylowPro q H P) :
    IsSylowPro q ⊤ P := by
  apply sylowPro_top_of_not_dvd_index hP
  intro hd
  obtain ⟨k, hk⟩ := hN.exists_card_eq
  have hdiv : q ∣ p ^ k := hk ▸ hd.trans (index_dvd_card_of_supplements N H hs)
  exact hne ((Nat.prime_dvd_prime_iff_eq hq.out Fact.out).mp (hq.out.dvd_of_dvd_pow hdiv))







end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]







private theorem sylowPro_top_of_pGroup_supplement_profinite (N H P : Subgroup G) [N.Normal]
    (hH : IsClosed (H : Set G)) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hne : q ≠ p)
    (hN : IsPGroup p N) (hs : Supplements N H) (hP : IsSylowPro q H P) :
    IsSylowPro q ⊤ P := by
  apply isSylowPro_of_full_images P hP.2.1
  intro U
  let π := QuotientGroup.mk' U.toSubgroup
  have hNu : IsPGroup p (N.map π) :=
    hN.of_surjective (subgroupImageHom N π) (subgroupImageHom_surjective N π)
  obtain ⟨S, hS⟩ := sylow_of_isSylowPro (P.map π)
    (sylowPro_top_of_pGroup_supplement (N.map π) (H.map π) (P.map π) hne hNu
      (supplements_map N H hs π (QuotientGroup.mk'_surjective U.toSubgroup))
      (sylowPro_map_finite H P hH hP π continuous_quotient_mk'))
  exact ⟨S, hS.symm⟩



/-- Once the p-Sylows coincide, local conjugacy holds inside the generated
subgroup: the other Sylows are already Sylows of the ambient group. -/
private theorem locallyConjugate_generated_profinite_preparedProof (N H K P : Subgroup G) [N.Normal]
    (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hL : IsClosed ((H ⊔ K : Subgroup G) : Set G))
    {p : ℕ} [Fact p.Prime] (hN : IsPGroup p N)
    (hsH : Supplements N H) (hsK : Supplements N K)
    (hPH : IsSylowPro p H P) (hPK : IsSylowPro p K P) :
    LocallyConjugate (H.subgroupOf (H ⊔ K)) (K.subgroupOf (H ⊔ K)) := by
  let L := H ⊔ K
  letI := profinite_closed_subgroup L hL
  intro q hq
  letI : Fact q.Prime := ⟨hq⟩
  by_cases he : q = p
  · subst q
    exact ⟨P.subgroupOf L, P.subgroupOf L,
      isSylowPro_in_closed_subgroup hL hPH le_sup_left,
      isSylowPro_in_closed_subgroup hL hPK le_sup_right, 1, conjugate_one _⟩
  · obtain ⟨A, hA⟩ := exists_sylowPro_subgroup q H hH
    obtain ⟨B, hB⟩ := exists_sylowPro_subgroup q K hK
    have hAG := sylowPro_top_of_pGroup_supplement_profinite N H A hH he hN hsH hA
    have hBG := sylowPro_top_of_pGroup_supplement_profinite N K B hK he hN hsK hB
    have hAL := isSylowPro_subgroupOf L A hL
      (isSylowPro_of_intermediate hAG (hA.1.trans le_sup_left) le_top)
    have hBL := isSylowPro_subgroupOf L B hL
      (isSylowPro_of_intermediate hBG (hB.1.trans le_sup_right) le_top)
    exact ⟨A.subgroupOf L, B.subgroupOf L,
      isSylowPro_in_closed_subgroup hL hA le_sup_left,
      isSylowPro_in_closed_subgroup hL hB le_sup_right, sylowPro_conjugate _ _ hAL hBL⟩

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N H K P : @Subgroup.{u_1} G inst)
  [@Subgroup.Normal.{u_1} G inst N]
  (hH :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) H))
  (hK :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) K))
  (hL :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)
        (@Max.max.{u_1} (@Subgroup.{u_1} G inst)
          (@SemilatticeSup.toMax.{u_1} (@Subgroup.{u_1} G inst)
            (@Lattice.toSemilatticeSup.{u_1} (@Subgroup.{u_1} G inst)
              (@ConditionallyCompleteLattice.toLattice.{u_1} (@Subgroup.{u_1} G inst)
                (@CompleteLattice.toConditionallyCompleteLattice.{u_1} (@Subgroup.{u_1} G inst)
                  (@Subgroup.instCompleteLattice.{u_1} G inst)))))
          H K)))
  {p : Nat} [Fact (Nat.Prime p)]
  (hN :
    @IsPGroup.{u_1} p
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
      (@Subgroup.toGroup.{u_1} G inst N))
  (hsH : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N H)
  (hsK : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N K)
  (hPH : @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p G inst inst_1 H P)
  (hPK : @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p G inst inst_1 K P),
  @LocalConjugacy.Proof.LocalConjugacy.LocallyConjugate.{u_1}
    (@Subtype.{u_1 + 1} G fun (x : G) =>
      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
        (@Max.max.{u_1} (@Subgroup.{u_1} G inst)
          (@SemilatticeSup.toMax.{u_1} (@Subgroup.{u_1} G inst)
            (@Lattice.toSemilatticeSup.{u_1} (@Subgroup.{u_1} G inst)
              (@ConditionallyCompleteLattice.toLattice.{u_1} (@Subgroup.{u_1} G inst)
                (@CompleteLattice.toConditionallyCompleteLattice.{u_1} (@Subgroup.{u_1} G inst)
                  (@Subgroup.instCompleteLattice.{u_1} G inst)))))
          H K)
        x)
    (@Subgroup.toGroup.{u_1} G inst
      (@Max.max.{u_1} (@Subgroup.{u_1} G inst)
        (@SemilatticeSup.toMax.{u_1} (@Subgroup.{u_1} G inst)
          (@Lattice.toSemilatticeSup.{u_1} (@Subgroup.{u_1} G inst)
            (@ConditionallyCompleteLattice.toLattice.{u_1} (@Subgroup.{u_1} G inst)
              (@CompleteLattice.toConditionallyCompleteLattice.{u_1} (@Subgroup.{u_1} G inst)
                (@Subgroup.instCompleteLattice.{u_1} G inst)))))
        H K))
    (@instTopologicalSpaceSubtype.{u_1} G
      (fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
          (@Max.max.{u_1} (@Subgroup.{u_1} G inst)
            (@SemilatticeSup.toMax.{u_1} (@Subgroup.{u_1} G inst)
              (@Lattice.toSemilatticeSup.{u_1} (@Subgroup.{u_1} G inst)
                (@ConditionallyCompleteLattice.toLattice.{u_1} (@Subgroup.{u_1} G inst)
                  (@CompleteLattice.toConditionallyCompleteLattice.{u_1} (@Subgroup.{u_1} G inst)
                    (@Subgroup.instCompleteLattice.{u_1} G inst)))))
            H K)
          x)
      inst_1)
    (@Subgroup.subgroupOf.{u_1} G inst H
      (@Max.max.{u_1} (@Subgroup.{u_1} G inst)
        (@SemilatticeSup.toMax.{u_1} (@Subgroup.{u_1} G inst)
          (@Lattice.toSemilatticeSup.{u_1} (@Subgroup.{u_1} G inst)
            (@ConditionallyCompleteLattice.toLattice.{u_1} (@Subgroup.{u_1} G inst)
              (@CompleteLattice.toConditionallyCompleteLattice.{u_1} (@Subgroup.{u_1} G inst)
                (@Subgroup.instCompleteLattice.{u_1} G inst)))))
        H K))
    (@Subgroup.subgroupOf.{u_1} G inst K
      (@Max.max.{u_1} (@Subgroup.{u_1} G inst)
        (@SemilatticeSup.toMax.{u_1} (@Subgroup.{u_1} G inst)
          (@Lattice.toSemilatticeSup.{u_1} (@Subgroup.{u_1} G inst)
            (@ConditionallyCompleteLattice.toLattice.{u_1} (@Subgroup.{u_1} G inst)
              (@CompleteLattice.toConditionallyCompleteLattice.{u_1} (@Subgroup.{u_1} G inst)
                (@Subgroup.instCompleteLattice.{u_1} G inst)))))
        H K)) :=
  @LocalConjugacy.Proof.LocalConjugacy.locallyConjugate_generated_profinite_preparedProof
