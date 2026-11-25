-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isCompactModCenter_matrixCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:25:38.482018+00:00
-- url     : https://prove2.me/submissions/b51b4649-3e44-416a-bde4-c7259f9b126c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_finset_of_isSupercuspidal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagPow_const_mem_center
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_antitone
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_conj_mem_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_pow_mul_mem_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_hasBasis_nhds_one
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_apply_eq_or_gap
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagPow_add
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagPow_conj_mem_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_gap_or_bounded
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
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {π : Representation ℂ (GL (Fin n) F) V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (v : V)
    {f : Module.Dual ℂ V} (hf : f ∈ smoothVectors (Representation.dual π)) :
    IsCompactModCenter (matrixCoeff π v f) := by
  classical
  obtain ⟨m₁, -, hm₁⟩ := (hasBasis_nhds_one F n).mem_iff.1 ((hπ v).mem_nhds (one_mem _))
  obtain ⟨m₂, -, hm₂⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((mem_smoothVectors.1 hf).mem_nhds (one_mem _))
  set m := max m₁ m₂
  set K := congruenceSubgroup F n m
  have hvK : v ∈ fixedVectors π K := fun k hk =>
    hm₁ (congruenceSubgroup_antitone F n (le_max_left _ _) hk)
  have hfK : ∀ k ∈ K, ∀ x, f (π k x) = f x := mem_fixedVectors_dual.1 fun k hk =>
    hm₂ (congruenceSubgroup_antitone F n (le_max_right _ _) hk)
  set K₀ := integralGL F n
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hQ : Finite (K₀ ⧸ K.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_congruenceSubgroup F n m).preimage continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ K.subgroupOf K₀)
  let R : Finset (GL (Fin n) F) :=
    Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : GL (Fin n) F)
  have hR : ∀ k ∈ K₀, ∃ r ∈ R, π k v = π r v := by
    intro k hk
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    exact act_eq_of_mk_eq π hvK (a := ⟨k, hk⟩)
      (b := Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ K.subgroupOf K₀))
      (QuotientGroup.out_eq' _).symm
  let V₂ : Finset V := R.image fun r => π r v
  have hU : ∀ S : Finset (Fin n), (∃ i j, i ∈ S ∧ j ∉ S) → ∀ w : V,
      ∃ U : Finset (GL (Fin n) F), (∀ u ∈ U, u ∈ unipotentRadical F n (splitFun S)) ∧
        w ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ x, y = π u x - x} :=
    fun S hS w => exists_finset_of_isSupercuspidal hsc hS w
  choose! Uf hUf1 hUf2 using hU
  let Uall : Finset (GL (Fin n) F) := Finset.univ.biUnion fun S : Finset (Fin n) => V₂.biUnion (Uf S)
  obtain ⟨t, ht⟩ := exists_pow_mul_mem_of_isCompact F n
    ((Uall ∪ Uall.image fun u => u⁻¹ : Finset (GL (Fin n) F)) : Set (GL (Fin n) F)).toFinite.isCompact
  have hbu : ∀ u ∈ Uall, ∀ i j, (uniformizer F : F) ^ t * u i j ∈ 𝒪[F] :=
    fun u hu => ht _ (by simp [hu])
  have hbu' : ∀ u ∈ Uall, ∀ i j, (uniformizer F : F) ^ t * (u⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F] :=
    fun u hu => ht _ (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨u, hu, rfl⟩)
  set C : ℤ := ((t + m : ℕ) : ℤ) + 1 with hCdef
  have hC : ((t + m : ℕ) : ℤ) < C := lt_add_one _
  have hC0 : 0 < C := by positivity
  let Nset : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc 0 (n * C)
  let Cset : Set (GL (Fin n) F) := ⋃ ν ∈ (Nset : Set (Fin n → ℤ)),
    (fun p : GL (Fin n) F × GL (Fin n) F => p.1 * Cartan.diagPow F n ν * p.2) ''
      ((K₀ : Set (GL (Fin n) F)) ×ˢ (K₀ : Set (GL (Fin n) F)))
  have hCset : IsCompact Cset :=
    Nset.finite_toSet.isCompact_biUnion fun ν _ =>
      ((isCompact_integralGL F n).prod (isCompact_integralGL F n)).image (by fun_prop)
  refine ⟨Cset, hCset, fun g hg => ?_⟩
  rw [Function.mem_support] at hg
  obtain ⟨μ, -, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  obtain ⟨r₂, hr₂, hr₂v⟩ := hR k₂ hk₂
  have hwV : π r₂ v ∈ V₂ := Finset.mem_image_of_mem _ hr₂
  rcases gap_or_bounded (β := fun _ : Fin n => (0 : ℕ)) μ hC0 with
    ⟨θ, b, ⟨i, hib, hiθ⟩, ⟨j, hjb, hjθ⟩, hgap⟩ | hbd
  · exfalso
    apply hg
    set S : Finset (Fin n) :=
      Finset.univ.filter fun j => (fun _ : Fin n => (0 : ℕ)) j = b ∧ θ ≤ μ j with hSdef
    have hS : ∃ i j, i ∈ S ∧ j ∉ S :=
      ⟨i, j, by simp [S, hib, hiθ], by simp [S, hjb, not_le.2 hjθ]⟩
    have hsp := hUf2 S hS (π r₂ v)
    set a := Cartan.diagPow F n μ
    have hker : Submodule.span ℂ {y | ∃ u ∈ Uf S (π r₂ v), ∃ x, y = π u x - x} ≤
        LinearMap.ker (f ∘ₗ π k₁ ∘ₗ π a) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, hu, x, rfl⟩
      have huA : u ∈ Uall := Finset.mem_biUnion.2 ⟨S, Finset.mem_univ _,
        Finset.mem_biUnion.2 ⟨π r₂ v, hwV, hu⟩⟩
      have huN := hUf1 S hS (π r₂ v) u hu
      have hlev : ∀ w : GL (Fin n) F, w ∈ levi F n (fun _ : Fin n => (0 : ℕ)) :=
        fun w => mem_levi.2 fun i j h => absurd rfl h
      have hconj : a * u * a⁻¹ ∈ K :=
        diagPow_conj_mem_congruenceSubgroup hC (apply_eq_or_gap hgap (hlev u) huN)
          (apply_eq_or_gap hgap (hlev u⁻¹) ((unipotentRadical F n _).inv_mem huN))
          (hbu u huA) (hbu' u huA)
      have hconj' : k₁ * (a * u * a⁻¹) * k₁⁻¹ ∈ K := conj_mem_congruenceSubgroup F n hk₁ hconj
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        map_sub]
      have h1 : π k₁ (π a (π u x)) = π (k₁ * (a * u * a⁻¹) * k₁⁻¹) (π k₁ (π a x)) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        group
      rw [h1, hfK _ hconj', sub_self]
    have := hker hsp
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply] at this
    show f (π (k₁ * a * k₂) v) = 0
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hr₂v]
    exact this
  ·
    let c₀ : ℤ := if h : ∃ k : Fin n, True then
      (Finset.univ.image μ).min' ⟨_, Finset.mem_image_of_mem μ (Finset.mem_univ h.choose)⟩ else 0
    have hc₀le : ∀ k, c₀ ≤ μ k := by
      intro k
      simp only [c₀, dif_pos (⟨k, trivial⟩ : ∃ k : Fin n, True)]
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    have hc₀mem : ∀ j : Fin n, ∃ k, c₀ = μ k := by
      intro j
      simp only [c₀, dif_pos (⟨j, trivial⟩ : ∃ k : Fin n, True)]
      obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (Finset.min'_mem (Finset.univ.image μ) _)
      exact ⟨k, hk.symm⟩
    let ν : Fin n → ℤ := μ - fun _ => c₀
    have hν : ν ∈ Nset := by
      rw [Fintype.mem_piFinset]
      intro j
      rw [Finset.mem_Icc]
      obtain ⟨k, hk⟩ := hc₀mem j
      have h1 := hc₀le j
      have h2 := hbd j k rfl
      constructor
      · show 0 ≤ μ j - c₀
        linarith
      · show μ j - c₀ ≤ n * C
        linarith
    have hμ : μ = (fun _ => c₀) + ν := by
      funext j
      simp [ν]
    have hz := diagPow_const_mem_center (F := F) (n := n) c₀
    refine Set.mem_mul.2 ⟨Cartan.diagPow F n (fun _ => c₀), hz, k₁ * Cartan.diagPow F n ν * k₂,
      Set.mem_biUnion hν ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩, ?_⟩
    rw [hμ, diagPow_add, ← mul_assoc k₁, Subgroup.mem_center_iff.1 hz k₁]
    group
end GroundTheory.Automorphic.Parabolic
