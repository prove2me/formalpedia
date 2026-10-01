-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:35:46.534041+00:00
-- url     : https://prove2.me/submissions/0ff0df07-1a30-4d03-8db9-af670c9dc56e

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_abelian_complement_inclusion_finite_kernel
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_card_map_quotient_lt_finite_kernel
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_conjugate_le_full_sylow
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_conjugate_le_of_normal_intersection_quotients
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_eq_of_supplements_le
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_finite_normal_intersection_image
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isProP_of_quotient_images
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_subgroupOf
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_nilpotent_coprime_split
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_profinite_quotient
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_relIndex_sup_dvd_card
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_sylowPro_map

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







private theorem isPGroup_quotient_image {p : ℕ} (H : Subgroup G) (hH : IsProP p H)
    (U : OpenNormalSubgroup G) : IsPGroup p (H.map (QuotientGroup.mk' U.toSubgroup)) := by
  let π := QuotientGroup.mk' U.toSubgroup
  let f : H →* G ⧸ U.toSubgroup := π.comp H.subtype
  have hf : Continuous f := continuous_quotient_mk'.comp continuous_subtype_val
  intro x
  obtain ⟨y, hy, he⟩ := x.property
  obtain ⟨k, hk⟩ := image_pow hH f hf ⟨y, hy⟩
  refine ⟨k, Subtype.ext ?_⟩
  change x.val ^ p ^ k = 1
  change π y ^ p ^ k = 1 at hk
  rwa [show π y = x.val from he] at hk



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















end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! Algebraic quotient reduction from the earlier local development, rechecked here. -/

namespace LocalConjugacy

open Subgroup QuotientGroup

variable {G : Type*} [Group G]



/-- **Step 1.** If `H` supplements the normal subgroup `N` and `N ⊓ H` is normalised by `N`,
then `N ⊓ H` is normal in the whole group.  (`N ⊓ H` is always normalised by `H`; the new
hypothesis supplies the other half, and `N ⊔ H = ⊤` glues them.) -/
private theorem inf_normal_of_stabNormal (N H : Subgroup G) [hN : N.Normal]
    (hsup : N ⊔ H = ⊤) (hstab : StabNormal N H) : (N ⊓ H).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← hsup]
  refine sup_le (le_normalizer_iff.mpr hstab) (le_normalizer_iff.mpr ?_)
  intro h hh d hd
  exact ⟨hN.conj_mem d hd.1 h, H.mul_mem (H.mul_mem hh hd.2) (H.inv_mem hh)⟩







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

private theorem commutative_map (N : Subgroup G) (hcomm : ∀ n m : N, n * m = m * n)
    (f : G →* F) : ∀ n m : N.map f, n * m = m * n := by
  rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
  apply Subtype.ext
  change f x * f y = f y * f x
  rw [← map_mul, ← map_mul]
  exact congrArg f (congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩))

private theorem intersectionNormal_of_commutative (N H : Subgroup G)
    (hcomm : ∀ n m : N, n * m = m * n) : IntersectionNormal N H := by
  intro n hn d hd
  have he := congrArg Subtype.val (hcomm ⟨n, hn⟩ ⟨d, hd.1⟩)
  change n * d = d * n at he
  rw [he, mul_inv_cancel_right]
  exact hd

private theorem conjugate_le_of_quotient (D H K : Subgroup G) [D.Normal] (hDH : D ≤ H)
    (q : G ⧸ D) (hq : conjugate q (K.map (QuotientGroup.mk' D)) ≤
      H.map (QuotientGroup.mk' D)) : ∃ g : G, conjugate g K ≤ H := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D q
  refine ⟨g, ?_⟩
  intro x hx
  let π := QuotientGroup.mk' D
  have hm : π x ∈ H.map π := by
    apply hq
    rw [← conjugate_map]
    exact Subgroup.mem_map_of_mem π hx
  change x ∈ (H.map π).comap π at hm
  simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk', sup_eq_left.mpr hDH] using hm

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





end Maps

section Algebra
variable {G : Type*} [Group G]

private theorem isComplement'_of_supplements_inf (N H : Subgroup G)
    (hs : Supplements N H) (hd : N ⊓ H = ⊥) : Subgroup.IsComplement' N H := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hd)
  apply Set.eq_univ_of_forall
  intro g
  exact hs g

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





private theorem conjugate_eq_self_of_mem (H : Subgroup G) {g : G} (hg : g ∈ H) :
    conjugate g H = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
  · intro x hx
    refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group











end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [Profinite G] [TopologicalSpace F] [Finite F] [DiscreteTopology F]





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







end Finite
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





private theorem locallyContains_map (H K : Subgroup G) (hK : IsClosed (K : Set G))
    (hlocal : LocallyContains H K) (f : G →* F) (hf : Continuous f) :
    LocallyContains (H.map f) (K.map f) := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, g, hg⟩ := hlocal p hp
  refine ⟨P.map f, sylowPro_map K P hK hP f hf, f g, ?_⟩
  rw [← conjugate_map]
  exact Subgroup.map_mono hg



end Images
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









end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [Profinite G] [TopologicalSpace F] [Profinite F]







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

namespace LocalConjugacy
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

private theorem normal_proP_le_sylowPro (D P : Subgroup G) [D.Normal]
    {p : ℕ} [Fact p.Prime] (hD : IsProP p D) (hP : IsSylowPro p ⊤ P) : D ≤ P := by
  apply subgroup_le_of_finite_images D P hP.2.1
  intro U
  obtain ⟨S, hS⟩ := sylowPro_full_images P hP U
  rw [hS]
  exact (isPGroup_quotient_image D hD U).le_sylow_of_normal S

private theorem inf_eq_inf_sylowPro_profinite (N H P : Subgroup G) [N.Normal]
    (hH : IsClosed (H : Set G)) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (hP : IsSylowPro p H P) : N ⊓ P = N ⊓ H := by
  letI := profinite_closed_subgroup H hH
  have hle := normal_proP_le_sylowPro (N.subgroupOf H) (P.subgroupOf H)
    (proP_of_isPGroup hN.comap_subtype) (isSylowPro_subgroupOf H P hH hP)
  apply le_antisymm (inf_le_inf_left N hP.1)
  intro x hx
  exact ⟨hx.1, hle (show (⟨x, hx.2⟩ : H) ∈ N.subgroupOf H from hx.1)⟩









end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! The finite-normal-subgroup stage of Proposition 4.1. The ambient group
remains profinite. The complement case is reduced to a finite quotient in
which the complement survives, so the proved abelian cocycle argument supplies
the role of the conjugacy theorem cited in the manuscript. -/

namespace LocalConjugacy



private theorem quotient_inclusion_conjugator_from_factor
    {G : Type*} [Group G] (A B N H K : Subgroup G) [A.Normal]
    (hs : Supplements N K) (hAB : A ⊔ B = N)
    (hc : ∃ g : G ⧸ A, conjugate g (K.map (QuotientGroup.mk' A)) ≤
      H.map (QuotientGroup.mk' A)) :
    ∃ b : B, conjugate (QuotientGroup.mk' A b) (K.map (QuotientGroup.mk' A)) ≤
      H.map (QuotientGroup.mk' A) := by
  let π := QuotientGroup.mk' A
  have hn : N.map π = B.map π := by
    rw [← hAB, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hs' := supplements_map N K hs π (QuotientGroup.mk'_surjective A)
  rw [hn] at hs'
  obtain ⟨g, hg⟩ := hc
  obtain ⟨n, hn, k, hk, rfl⟩ := hs' g
  rw [← conjugate_comp, conjugate_eq_self_of_mem (K.map π) hk] at hg
  obtain ⟨b, hb, rfl⟩ := hn
  exact ⟨⟨b, hb⟩, hg⟩

universe u

private theorem abelian_inclusion_finite_kernel_aux (n : ℕ) :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]
      (N H K : Subgroup G) [N.Normal] [Finite N], Nat.card N = n →
      IsClosed (N : Set G) → IsClosed (H : Set G) → IsClosed (K : Set G) →
      (∀ a b : N, a * b = b * a) → Supplements N H → Supplements N K →
      LocallyContains H K → ∃ g : G, conjugate g K ≤ H := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ N H K _ _ hcard hN hH hK hcomm hsH hsK hlocal
    letI : CommGroup N := { (inferInstance : Group N) with mul_comm := hcomm }
    have hquot (D : Subgroup G) [D.Normal] (hDN : D ≤ N) (hD : D ≠ ⊥) :
        ∃ q : G ⧸ D, conjugate q (K.map (QuotientGroup.mk' D)) ≤
          H.map (QuotientGroup.mk' D) := by
      letI : Finite D := Finite.of_injective (Subgroup.inclusion hDN)
        (Subgroup.inclusion_injective hDN)
      have hDc : IsClosed (D : Set G) :=
        (Set.finite_coe_iff.mp (inferInstance : Finite D)).isClosed
      letI := profinite_quotient D hDc
      let π := QuotientGroup.mk' D
      letI : Finite (N.map π) := Finite.of_surjective (subgroupImageHom N π)
        (subgroupImageHom_surjective N π)
      exact ih _ (hcard ▸ card_map_quotient_lt_finite_kernel N D hDN hD)
        (N.map π) (H.map π) (K.map π) rfl
        (hN.isCompact.image continuous_quotient_mk').isClosed
        (hH.isCompact.image continuous_quotient_mk').isClosed
        (hK.isCompact.image continuous_quotient_mk').isClosed
        (commutative_map N hcomm π)
        (supplements_map N H hsH π (QuotientGroup.mk'_surjective D))
        (supplements_map N K hsK π (QuotientGroup.mk'_surjective D))
        (locallyContains_map H K hK hlocal π continuous_quotient_mk')
    by_cases hpgroup : ∃ p : ℕ, p.Prime ∧ IsPGroup p N
    · obtain ⟨p, hp, hNp⟩ := hpgroup
      letI : Fact p.Prime := ⟨hp⟩
      let D := N ⊓ H
      letI : D.Normal := inf_normal_of_stabNormal N H
        (sup_eq_top_of_supplements N H hsH) (intersectionNormal_of_commutative N H hcomm)
      by_cases hD : D = ⊥
      · have hNK : N ⊓ K = ⊥ := by
          obtain ⟨P, hP, g, hg⟩ := hlocal p hp
          have he := inf_eq_inf_sylowPro_profinite N K P hK hNp hP
          apply eq_bot_iff.mpr
          intro x hx
          have hxP : x ∈ P := (show x ∈ N ⊓ P from he ▸ hx).2
          have hm : g * x * g⁻¹ ∈ D :=
            ⟨(inferInstance : N.Normal).conj_mem x hx.1 g,
              hg (Subgroup.mem_map_of_mem _ hxP)⟩
          have hx1 : g * x * g⁻¹ = 1 := by simpa only [hD, Subgroup.mem_bot] using hm
          change x = 1
          have hc := congrArg (fun z => g⁻¹ * z * g) hx1
          simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
            inv_mul_cancel, mul_one, one_mul] using hc
        -- Both supplements are now complements, exactly as in the paper.
        have hcK := isComplement'_of_supplements_inf N K hsK hNK
        have hcH := isComplement'_of_supplements_inf N H hsH hD
        obtain ⟨g, hg⟩ := abelian_complement_inclusion_finite_kernel N H K hH hK hcomm hsH
          hcH.disjoint.eq_bot hlocal
        have hsK' : Supplements N K := by
          intro x
          obtain ⟨⟨n, k⟩, he⟩ := hcK.surjective x
          exact ⟨n, n.property, k, k.property, he⟩
        have he := eq_of_supplements_le N H (conjugate g K)
          (supplements_conjugate N K hsK' g) hcH.disjoint.eq_bot hg
        exact ⟨g, he.le⟩
      · obtain ⟨q, hq⟩ := hquot D inf_le_left hD
        exact conjugate_le_of_quotient D H K inf_le_right q hq
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
      obtain ⟨b, hb⟩ := quotient_inclusion_conjugator_from_factor A B N H K hsK hAB
        (hquot A hAN hA)
      obtain ⟨a, ha⟩ := quotient_inclusion_conjugator_from_factor B A N H K hsK
        ((sup_comm B A).trans hAB) (hquot B hBN hB)
      exact ⟨(a : G) * b, merge_coprime_conjugators_profinite A B K H hH hcop'
        (Subgroup.disjoint_of_coprime_natCard hcop') a b
        (conjugate_le_sup_of_quotient A K H b hb)
        (conjugate_le_sup_of_quotient B K H a ha)⟩

/-- Proposition 4.1 for finite abelian `N`, proved by induction on `|N|`
while the ambient group remains profinite. -/
private theorem abelian_inclusion_finite_kernel
    {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]
    (N H K : Subgroup G) [N.Normal] [Finite N]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hcomm : ∀ n m : N, n * m = m * n)
    (hsH : Supplements N H) (hsK : Supplements N K) (hlocal : LocallyContains H K) :
    ∃ g : G, conjugate g K ≤ H :=
  abelian_inclusion_finite_kernel_aux (Nat.card N) N H K rfl hN hH hK hcomm hsH hsK hlocal

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! Proposition 4.1 in the order of the manuscript: induction for finite `N`,
then compactness in the quotients by `N ∩ U`. -/

namespace LocalConjugacy

variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]



/-- Proposition 4.1, `thm:loc_inclusion_ab`. -/
private theorem proposition_4_1_preparedProof (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hcomm : ∀ n m : N, n * m = m * n)
    (hHN : Supplements N H) (hKN : Supplements N K)
    (hlocal : LocallyContains H K) : ∃ g : G, conjugate g K ≤ H := by
  apply conjugate_le_of_normal_intersection_quotients N H K hN hH
  intro U
  let D := N ⊓ U.toSubgroup
  letI := profinite_quotient D (hN.inter U.isClosed)
  let π := QuotientGroup.mk' D
  letI : Finite (N.map π) := finite_normal_intersection_image N U
  exact abelian_inclusion_finite_kernel (N.map π) (H.map π) (K.map π)
    (hN.isCompact.image continuous_quotient_mk').isClosed
    (hH.isCompact.image continuous_quotient_mk').isClosed
    (hK.isCompact.image continuous_quotient_mk').isClosed
    (commutative_map N hcomm π)
    (supplements_map N H hHN π (QuotientGroup.mk'_surjective D))
    (supplements_map N K hKN π (QuotientGroup.mk'_surjective D))
    (locallyContains_map H K hK hlocal π continuous_quotient_mk')

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
  (hcomm :
    ∀
      (n m :
        @Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x),
      @Eq.{u_1 + 1}
        (@Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
        (@HMul.hMul.{u_1, u_1, u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@instHMul.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (@Subgroup.mul.{u_1} G inst N))
          n m)
        (@HMul.hMul.{u_1, u_1, u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@instHMul.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (@Subgroup.mul.{u_1} G inst N))
          m n))
  (hHN : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N H)
  (hKN : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N K)
  (hlocal : @LocalConjugacy.Proof.LocalConjugacy.LocallyContains.{u_1} G inst inst_1 H K),
  @Exists.{u_1 + 1} G fun (g : G) =>
    @LE.le.{u_1} (@Subgroup.{u_1} G inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
      (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst g K) H :=
  @LocalConjugacy.Proof.LocalConjugacy.proposition_4_1_preparedProof
