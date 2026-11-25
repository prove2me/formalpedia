-- Prove2me | solution 1 for GlobalTheory.exists_isometry_of_intertwiner_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:35:33.403807+00:00
-- url     : https://prove2.me/submissions/a8bf1fd9-391b-4a41-a39d-b149ed2b41eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsIsometryOfIntertwinerOfIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped InnerProductSpace
namespace GlobalTheory
theorem _root_.solution
    (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁]
    (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂]
    (ι : Type) (π₁ : ι → (V₁ →L[ℂ] V₁)) (π₂ : ι → (V₂ →L[ℂ] V₂)) (T : V₁ ≃ₗ[ℂ] V₂)
    (h₁ : ∀ i v, ‖π₁ i v‖ = ‖v‖) (h₂ : ∀ i v, ‖π₂ i v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ V₁, (∀ i, ∀ v ∈ S, π₁ i v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hT : ∀ i v, T (π₁ i v) = π₂ i (T v)) :
    ∃ φ : V₁ ≃ₗᵢ[ℂ] V₂, ∀ i v, φ (π₁ i v) = π₂ i (φ v) := by
  rcases subsingleton_or_nontrivial V₁ with hV | hV
  · refine ⟨⟨T, fun v => ?_⟩, hT⟩
    rw [Subsingleton.elim v 0]
    simp
  let p₁ : ι → (V₁ →ₗᵢ[ℂ] V₁) := fun i => ⟨(π₁ i : V₁ →ₗ[ℂ] V₁), h₁ i⟩
  let p₂ : ι → (V₂ →ₗᵢ[ℂ] V₂) := fun i => ⟨(π₂ i : V₂ →ₗ[ℂ] V₂), h₂ i⟩
  have i₁ : ∀ i a b, ⟪π₁ i a, π₁ i b⟫_ℂ = ⟪a, b⟫_ℂ := fun i a b => (p₁ i).inner_map_map a b
  have i₂ : ∀ i a b, ⟪π₂ i a, π₂ i b⟫_ℂ = ⟪a, b⟫_ℂ := fun i a b => (p₂ i).inner_map_map a b
  have s₁ : ∀ i, Function.Surjective (π₁ i) := fun i =>
    (LinearMap.injective_iff_surjective (f := (π₁ i : V₁ →ₗ[ℂ] V₁))).1 (p₁ i).injective
  let X : Module.End ℂ V₁ :=
    (LinearMap.adjoint (T : V₁ →ₗ[ℂ] V₂)).comp (T : V₁ →ₗ[ℂ] V₂)
  have hX : ∀ a b, ⟪X a, b⟫_ℂ = ⟪T a, T b⟫_ℂ := fun a b =>
    LinearMap.adjoint_inner_left (T : V₁ →ₗ[ℂ] V₂) b (T a)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue X
  have htop : X.eigenspace c = ⊤ := by
    refine (hirr _ ?_).resolve_left hc
    intro i v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    refine ext_inner_right ℂ fun u => ?_
    obtain ⟨w, rfl⟩ := s₁ i u
    rw [hX, hT, hT, i₂, ← hX, hv, ← map_smul, i₁]
  have hall : ∀ v, ‖T v‖ = Real.sqrt ‖c‖ * ‖v‖ := by
    intro v
    have hv : X v = c • v := Module.End.mem_eigenspace_iff.1 (htop ▸ Submodule.mem_top)
    have h := hX v v
    rw [hv, inner_smul_left] at h
    have h' := congrArg norm h
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h'
    simp only [RCLike.norm_conj, norm_pow, RCLike.norm_ofReal, abs_norm, norm_norm, Complex.coe_algebraMap, Complex.norm_real] at h'
    have e : ‖T v‖ ^ 2 = (Real.sqrt ‖c‖ * ‖v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (norm_nonneg c), h']
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 e
  have hr : Real.sqrt ‖c‖ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : V₁)
    have := hall v
    rw [h0, zero_mul, norm_eq_zero] at this
    exact hv (T.map_eq_zero_iff.1 this)
  have hr' : (((Real.sqrt ‖c‖)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero hr
  refine ⟨⟨T.trans (LinearEquiv.smulOfNeZero ℂ V₂ _ hr'), fun v => ?_⟩, fun i v => ?_⟩
  · change ‖(((Real.sqrt ‖c‖)⁻¹ : ℝ) : ℂ) • T v‖ = ‖v‖
    rw [norm_smul, hall, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← mul_assoc,
      inv_mul_cancel₀ hr, one_mul]
  · change (((Real.sqrt ‖c‖)⁻¹ : ℝ) : ℂ) • T (π₁ i v)
      = π₂ i ((((Real.sqrt ‖c‖)⁻¹ : ℝ) : ℂ) • T v)
    rw [hT, map_smul]
end GlobalTheory
