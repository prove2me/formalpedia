-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.exists_bound_of_coeff_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:21:02.9083+00:00
-- url     : https://prove2.me/submissions/3c619681-40b8-4815-94e6-6fb5e4bab055

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleFiniteLength
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLeviSupport
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_antitone
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_conj_mem_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_pow_mul_mem_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_apply_eq_or_gap
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagPow_conj_mem_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_finset_of_isCuspidal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_subgroupOf_congruenceSubgroup_subset
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_gap_or_bounded
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompact_subgroupOf_levi
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_subgroupOf_levi
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic ValuativeRel
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (hσ : IsSmooth σ) (hc : IsCuspidal σ) (w : W)
    {ℓ : Module.Dual ℂ W} (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) :
    ∃ N : ℕ, ∀ (μ : Fin n → ℤ) (k₁ k₂ : levi F n β), (k₁ : GL (Fin n) F) ∈ integralGL F n →
      (k₂ : GL (Fin n) F) ∈ integralGL F n →
      ℓ (σ (k₁ * ⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩ * k₂) w) ≠ 0 →
      ∃ c : Fin n → ℤ, (∀ i j, β i = β j → c i = c j) ∧ ∀ i, c i ≤ μ i ∧ μ i ≤ c i + N := by
  classical
  let KM : ℕ → Subgroup (levi F n β) := fun m => (congruenceSubgroup F n m).subgroupOf (levi F n β)
  have hKMo : ∀ m, IsOpen (KM m : Set (levi F n β)) := fun m =>
    isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m)
  have hKManti : ∀ {m m' : ℕ}, m ≤ m' → KM m' ≤ KM m := fun h x hx =>
    Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone F n h (Subgroup.mem_subgroupOf.1 hx))

  obtain ⟨m₀, hm₀⟩ := exists_subgroupOf_congruenceSubgroup_subset
    ((hσ w).mem_nhds (one_mem (stabilizerOf σ w)))
  obtain ⟨m₁, hm₁⟩ := exists_subgroupOf_congruenceSubgroup_subset
    ((mem_smoothVectors.1 hℓ).mem_nhds (one_mem (stabilizerOf (Representation.dual σ) ℓ)))
  set m := max m₀ m₁ with hmdef
  set K := KM m with hKdef
  have hwK : w ∈ fixedVectors σ K := fun k hk => hm₀ (hKManti (le_max_left _ _) hk)
  have hℓK : ∀ k ∈ K, ∀ x, ℓ (σ k x) = ℓ x := mem_fixedVectors_dual.1 fun k hk =>
    hm₁ (hKManti (le_max_right _ _) hk)

  let K₀ : Subgroup (levi F n β) := (integralGL F n).subgroupOf (levi F n β)
  have hK₀c : IsCompact (K₀ : Set (levi F n β)) :=
    isCompact_subgroupOf_levi (isCompact_integralGL F n)
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 hK₀c
  have hQ : Finite (K₀ ⧸ K.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (hKMo m).preimage continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ K.subgroupOf K₀)
  let R : Finset (levi F n β) :=
    Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : levi F n β)
  have hR : ∀ k ∈ K₀, ∃ r ∈ R, σ k w = σ r w := by
    intro k hk
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    exact act_eq_of_mk_eq σ hwK (a := ⟨k, hk⟩)
      (b := Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ K.subgroupOf K₀))
      (QuotientGroup.out_eq' _).symm
  have hnorm : ∀ k ∈ K₀, ∀ x ∈ K, k * x * k⁻¹ ∈ K := fun k hk x hx =>
    Subgroup.mem_subgroupOf.2 (by
      simpa using conj_mem_congruenceSubgroup F n (Subgroup.mem_subgroupOf.1 hk)
        (Subgroup.mem_subgroupOf.1 hx))

  let V₂ : Finset W := R.image fun r => σ r w

  have hU : ∀ S : Finset (Fin n), (∃ i j, β i = β j ∧ i ∈ S ∧ j ∉ S) → ∀ x : W,
      ∃ U : Finset (levi F n β), (∀ u ∈ U, (u : GL (Fin n) F) ∈ unipotentRadical F n (splitFun S)) ∧
        x ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ z, y = σ u z - z} :=
    fun S hS x => exists_finset_of_isCuspidal hc hS x
  choose! Uf hUf1 hUf2 using hU
  let Uall : Finset (levi F n β) := Finset.univ.biUnion fun S : Finset (Fin n) => V₂.biUnion (Uf S)
  obtain ⟨t, ht⟩ := exists_pow_mul_mem_of_isCompact F n
    (((Uall.image fun u : levi F n β => u.1) ∪ (Uall.image fun u : levi F n β => u.1⁻¹) :
      Finset (GL (Fin n) F)) : Set (GL (Fin n) F)).toFinite.isCompact
  have hbu : ∀ u ∈ Uall, ∀ i j, (uniformizer F : F) ^ t * (u : GL (Fin n) F) i j ∈ 𝒪[F] :=
    fun u hu => ht _ (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inl ⟨u, hu, rfl⟩)
  have hbu' : ∀ u ∈ Uall, ∀ i j,
      (uniformizer F : F) ^ t * ((u : GL (Fin n) F)⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F] :=
    fun u hu => ht _ (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨u, hu, rfl⟩)
  set C : ℤ := ((t + m : ℕ) : ℤ) + 1 with hCdef
  have hC : ((t + m : ℕ) : ℤ) < C := lt_add_one _
  have hC0 : 0 < C := by positivity
  refine ⟨(n * C).toNat, ?_⟩
  intro μ k₁ k₂ hk₁ hk₂ hne
  set a : levi F n β := ⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩ with hadef
  have hk₁K : k₁ ∈ K₀ := Subgroup.mem_subgroupOf.2 hk₁
  have hk₂K : k₂ ∈ K₀ := Subgroup.mem_subgroupOf.2 hk₂
  obtain ⟨r₂, hr₂, hr₂v⟩ := hR _ hk₂K
  have hwV : σ r₂ w ∈ V₂ := Finset.mem_image_of_mem _ hr₂
  rcases gap_or_bounded (β := β) μ hC0 with
    ⟨θ, b, ⟨i, hib, hiθ⟩, ⟨j, hjb, hjθ⟩, hgap⟩ | hbd
  ·
    exfalso
    apply hne
    set S : Finset (Fin n) := Finset.univ.filter fun j => β j = b ∧ θ ≤ μ j with hSdef
    have hS : ∃ i j, β i = β j ∧ i ∈ S ∧ j ∉ S :=
      ⟨i, j, hib.trans hjb.symm, by simp [S, hib, hiθ], by simp [S, hjb, not_le.2 hjθ]⟩
    have hsp := hUf2 S hS (σ r₂ w)
    have hker : Submodule.span ℂ {y | ∃ u ∈ Uf S (σ r₂ w), ∃ z, y = σ u z - z} ≤
        LinearMap.ker (ℓ ∘ₗ σ k₁ ∘ₗ σ a) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, hu, x, rfl⟩
      have huA : u ∈ Uall := Finset.mem_biUnion.2 ⟨S, Finset.mem_univ _,
        Finset.mem_biUnion.2 ⟨σ r₂ w, hwV, hu⟩⟩
      have huN := hUf1 S hS (σ r₂ w) u hu
      have hconj : a * u * a⁻¹ ∈ K := by
        refine Subgroup.mem_subgroupOf.2 ?_
        have hco : ((a * u * a⁻¹ : levi F n β) : GL (Fin n) F) =
            Cartan.diagPow F n μ * (u : GL (Fin n) F) * (Cartan.diagPow F n μ)⁻¹ := rfl
        rw [hco]
        exact diagPow_conj_mem_congruenceSubgroup hC (apply_eq_or_gap hgap u.2 huN)
          (apply_eq_or_gap hgap ((levi F n β).inv_mem u.2)
            ((unipotentRadical F n _).inv_mem huN)) (hbu u huA) (hbu' u huA)
      have hconj' : k₁ * (a * u * a⁻¹) * k₁⁻¹ ∈ K := hnorm k₁ hk₁K _ hconj
      have h1 : σ k₁ (σ a (σ u x)) = σ (k₁ * (a * u * a⁻¹) * k₁⁻¹) (σ k₁ (σ a x)) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        map_sub]
      rw [h1, hℓK _ hconj', sub_self]
    have h0 := hker hsp
    rw [LinearMap.mem_ker] at h0
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hr₂v]
    simpa using h0
  ·
    let cb : α → ℤ := fun b => if h : ∃ k, β k = b then
      ((Finset.univ.filter fun k => β k = b).image μ).min' (by
        obtain ⟨k, hk⟩ := h
        exact ⟨μ k, Finset.mem_image_of_mem _ (by simp [hk])⟩) else 0
    have hcb_le : ∀ k, cb (β k) ≤ μ k := by
      intro k
      simp only [cb, dif_pos (⟨k, rfl⟩ : ∃ j, β j = β k)]
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (by simp))
    have hcb_mem : ∀ j, ∃ k, β k = β j ∧ cb (β j) = μ k := by
      intro j
      simp only [cb, dif_pos (⟨j, rfl⟩ : ∃ k, β k = β j)]
      obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.1
        (Finset.min'_mem ((Finset.univ.filter fun k => β k = β j).image μ) _)
      exact ⟨k, (Finset.mem_filter.1 hk).2, hkeq.symm⟩
    refine ⟨fun j => cb (β j), fun i j h => by simp only [h], fun i => ⟨hcb_le i, ?_⟩⟩
    obtain ⟨k, hk, hkeq⟩ := hcb_mem i
    have h1 := hbd i k hk.symm
    have h2 : (((n * C).toNat : ℕ) : ℤ) = n * C := Int.toNat_of_nonneg (by positivity)
    rw [h2]
    show μ i ≤ cb (β i) + n * C
    rw [hkeq]
    exact h1.le
end GroundTheory.Automorphic.GodementJacquet
