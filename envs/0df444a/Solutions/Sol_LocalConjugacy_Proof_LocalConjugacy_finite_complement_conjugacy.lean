-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.finite_complement_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T18:01:29.63138+00:00
-- url     : https://prove2.me/submissions/288d0812-d8fc-4ba6-af66-0dc795518062

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_NonabelianComplement_local_inclusion_of_primary
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_complement_quotient_bijective
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_eq_of_supplements_le
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isProP_of_quotient_images
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_of_full_images
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_lemma_1_2_of_pronilpotent
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_lemma_1_2_of_prosupersolvable
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_subgroup_quotient_factors
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_supersolvable_subgroup

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





end Discrete
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy





universe u





section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]



/-- Closed subgroups of prosupersolvable groups are prosupersolvable.
The algebraic conclusion even holds for the induced topology on any subgroup. -/
private theorem prosupersolvable_subgroup (hG : Prosupersolvable G) (H : Subgroup G) :
    Prosupersolvable H := by
  intro V
  obtain ⟨U, f, hf⟩ := subgroup_quotient_factors H V
  exact supersolvable_of_surjective (supersolvable_subgroup (hG U) _) f hf





end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

private theorem prosupersolvable_of_continuous_injective {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [Profinite G] [TopologicalSpace H] [Profinite H]
    (hG : Prosupersolvable G) (f : H →* G) (hf : Continuous f) (hi : Function.Injective f) :
    Prosupersolvable H := by
  let e : H ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y he => hi (congrArg Subtype.val he), f.rangeRestrict_surjective⟩
  have he : Continuous e := hf.subtype_mk _
  have hei : Continuous e.symm := he.continuous_symm_of_equiv_compact_to_t2
  intro V
  exact supersolvable_of_prosupersolvable_surjective (prosupersolvable_subgroup hG f.range)
    ((QuotientGroup.mk' V.toSubgroup).comp e.symm.toMonoidHom)
    (continuous_quotient_mk'.comp hei)
    ((QuotientGroup.mk'_surjective V.toSubgroup).comp e.symm.surjective)

section Action
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
  [MulDistribMulAction J N] [ContinuousSMul J N]





end Action
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy



variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

/-- Lemma 1.2, including both branches of the manuscript's disjunction. -/
private theorem primary_decomposition [Profinite J] [Profinite N] [DiscreteTopology N] [Finite N]
    [ContinuousSMul J N] (hN : Pronilpotent N)
    (hcase : Prosupersolvable (ActionProduct J N) ∨ Pronilpotent J)
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ p, IsSylowPro p.val.val ⊤ (P p)) :
    PrimaryDecomposition (N := N) P := by
  rcases hcase with hG | hJ
  · exact lemma_1_2_of_prosupersolvable hN hG P hP
  · exact lemma_1_2_of_pronilpotent hN hJ P hP

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
namespace NonabelianComplement
open AbelianComplement

section Algebra
variable {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
  (hc : Subgroup.IsComplement' N H)







end Algebra

section Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
  (N H : Subgroup G) [N.Normal] (hc : Subgroup.IsComplement' N H)
  (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))





attribute [local instance] conjugationAction





include hc hN hH



/-- The local-inclusion form of the complement theorem when the acting
subgroup is pronilpotent and the normal coefficient subgroup is finite. -/
private theorem local_inclusion_of_pronilpotent [Finite N] [DiscreteTopology N]
    (hpronN : Pronilpotent N) (K : Subgroup G) (hK : IsClosed (K : Set G))
    (hpronK : Pronilpotent K) (hloc : LocallyContains H K) :
    ∃ n : N, conjugate (n : G) K ≤ H := by
  letI := profinite_closed_subgroup K hK
  exact local_inclusion_of_primary N H hc hN hH K hK hloc
    (fun P hP => lemma_1_2_of_pronilpotent hpronN hpronK P hP)

end Topology
end NonabelianComplement
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

private theorem pronilpotent_complement (N K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hK : IsClosed (K : Set G))
    (hs : Supplements N K) (hd : N ⊓ K = ⊥) (hq : Pronilpotent (G ⧸ N)) :
    Pronilpotent K := by
  letI := profinite_closed_subgroup K hK
  letI : IsClosed (N : Set G) := hN
  let e : K ≃* G ⧸ N := MulEquiv.ofBijective
    ((QuotientGroup.mk' N).comp K.subtype) (complement_quotient_bijective N K hs hd)
  have he : Continuous e := continuous_quotient_mk'.comp continuous_subtype_val
  have hei : Continuous e.symm := he.continuous_symm_of_equiv_compact_to_t2
  exact pronilpotent_of_continuous_surjective hq e.symm.toMonoidHom hei e.symm.surjective

private theorem locallyContains_of_locallyConjugate (H K : Subgroup G)
    (h : LocallyConjugate H K) : LocallyContains H K := by
  intro p hp
  obtain ⟨P, Q, hP, hQ, g, hg⟩ := h p hp
  refine ⟨Q, hQ, g⁻¹, ?_⟩
  rw [← hg, conjugate_inv_cancel]
  exact hP.1

/-- Proposition 3.1 in its pronilpotent-quotient branch. -/
private theorem proposition_3_1_of_pronilpotent_quotient
    (N H K : Subgroup G) [N.Normal] [DiscreteTopology N] [Finite N]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hquot : Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K)
    (hNH : N ⊓ H = ⊥) (hNK : N ⊓ K = ⊥) :
    Conjugate H K ↔ LocallyConjugate H K := by
  refine ⟨locallyConjugate_of_conjugate H K hH, fun hlocal => ?_⟩
  have hc := isComplement'_of_supplements_inf N H hHN hNH
  obtain ⟨n, hn⟩ := NonabelianComplement.local_inclusion_of_pronilpotent N H hc hN hH
    hpron K hK (pronilpotent_complement N K hN hK hKN hNK hquot)
    (locallyContains_of_locallyConjugate H K hlocal)
  have he := eq_of_supplements_le N H (conjugate (n : G) K)
    (supplements_conjugate N K hKN n) hNH hn
  refine ⟨(n : G)⁻¹, ?_⟩
  rw [← he, conjugate_inv_cancel]

end Topology
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Complement
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
  (N K : Subgroup G) [N.Normal]

attribute [local instance] NonabelianComplement.conjugationAction



private theorem complementActionHom_injective (hc : N.IsComplement' K) :
    Function.Injective (complementActionHom N K) := by
  intro x y h
  have he : (x.left, x.right) = (y.left, y.right) := hc.injective h
  exact SemidirectProduct.ext (congrArg Prod.fst he) (congrArg Prod.snd he)

private theorem complementActionHom_continuous : Continuous (complementActionHom N K) :=
  (continuous_subtype_val.comp actionProduct_continuous_left).mul
    (continuous_subtype_val.comp actionProduct_continuous_right)

private theorem prosupersolvable_complement_action [Finite N] [DiscreteTopology N]
    (hK : IsClosed (K : Set G)) (hc : N.IsComplement' K) (hG : Prosupersolvable G) :
    Prosupersolvable (ActionProduct K N) := by
  letI := profinite_closed_subgroup K hK
  exact prosupersolvable_of_continuous_injective hG (complementActionHom N K)
    (complementActionHom_continuous N K) (complementActionHom_injective N K hc)

/-- The finite-coefficient complement argument used in Proposition 3.1. -/
private theorem finite_complement_conjugacy_preparedProof (N H K : Subgroup G) [N.Normal] [DiscreteTopology N] [Finite N]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K)
    (hNH : N ⊓ H = ⊥) (hNK : N ⊓ K = ⊥) :
    Conjugate H K ↔ LocallyConjugate H K := by
  rcases hcase with hG | hquot
  · refine ⟨locallyConjugate_of_conjugate H K hH, fun hlocal => ?_⟩
    letI := profinite_closed_subgroup K hK
    letI := profinite_closed_subgroup N hN
    have hsem := prosupersolvable_complement_action N K hK
      (isComplement'_of_supplements_inf N K hKN hNK) hG
    obtain ⟨n, hn⟩ := NonabelianComplement.local_inclusion_of_primary N H
      (isComplement'_of_supplements_inf N H hHN hNH) hN hH K hK
      (locallyContains_of_locallyConjugate H K hlocal)
      (fun P hP => primary_decomposition hpron (Or.inl hsem) P hP)
    have he := eq_of_supplements_le N H (conjugate (n : G) K)
      (supplements_conjugate N K hKN n) hNH hn
    refine ⟨(n : G)⁻¹, ?_⟩
    rw [← he, conjugate_inv_cancel]
  · exact proposition_3_1_of_pronilpotent_quotient N H K hN hH hK hpron
      hquot hHN hKN hNH hNK



end Complement
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N H K : @Subgroup.{u_1} G inst)
  [inst_3 : @Subgroup.Normal.{u_1} G inst N]
  [@DiscreteTopology.{u_1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
      (@instTopologicalSpaceSubtype.{u_1} G
        (fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
        inst_1)]
  [Finite.{u_1 + 1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)]
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
  (hKN : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N K)
  (hNH :
    @Eq.{u_1 + 1} (@Subgroup.{u_1} G inst)
      (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N H)
      (@Bot.bot.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instBot.{u_1} G inst)))
  (hNK :
    @Eq.{u_1 + 1} (@Subgroup.{u_1} G inst)
      (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N K)
      (@Bot.bot.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instBot.{u_1} G inst))),
  Iff (@LocalConjugacy.Proof.LocalConjugacy.Conjugate.{u_1} G inst H K)
    (@LocalConjugacy.Proof.LocalConjugacy.LocallyConjugate.{u_1} G inst inst_1 H K) :=
  @LocalConjugacy.Proof.LocalConjugacy.finite_complement_conjugacy_preparedProof
