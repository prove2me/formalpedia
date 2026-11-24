-- Prove2me | solution 1 for GlobalTheory.exists_free_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:37.228186+00:00
-- url     : https://prove2.me/submissions/8b14eef0-bd3f-41ab-adf2-7824458bfe9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
namespace GlobalTheory
theorem _root_.solution {C₀ C₁ K₁ K₂ : Type*} [AddCommGroup C₀] [AddCommGroup C₁]
    [AddCommGroup K₁] [AddCommGroup K₂] [Module R C₀] [Module R C₁] [Module R K₁] [Module R K₂]
    [Module.Finite R K₁] (d : C₀ →ₗ[R] C₁) (φ : K₁ →ₗ[R] C₁) (δ : K₁ →ₗ[R] K₂) (B : Submodule R C₀)
    [Module.Finite R (LinearMap.ker d ⧸ B.comap (LinearMap.ker d).subtype)] :
    ∃ (m : ℕ) (φ₀ : (Fin m → R) →ₗ[R] C₀) (δ₀ : (Fin m → R) →ₗ[R] K₁),
      (∀ x, d (φ₀ x) = φ (δ₀ x)) ∧ (∀ x, δ (δ₀ x) = 0) ∧
      ∀ c k, d c = φ k → δ k = 0 → ∃ x, c - φ₀ x ∈ B ∧ δ₀ x = k := by
  let N : Submodule R (C₀ × K₁) :=
    LinearMap.ker (d.coprod (-φ)) ⊓ LinearMap.ker (δ ∘ₗ LinearMap.snd R _ _)
  have hN : ∀ x, x ∈ N ↔ d x.1 = φ x.2 ∧ δ x.2 = 0 := by
    intro x
    simp [N, add_neg_eq_zero]
  let s : N →ₗ[R] K₁ := LinearMap.snd R _ _ ∘ₗ N.subtype
  obtain ⟨a, π₁, hπ₁⟩ := Module.Finite.exists_fin' R (LinearMap.range s)
  obtain ⟨g₁, hg₁⟩ := Module.projective_lifting_property s.rangeRestrict π₁
    s.surjective_rangeRestrict
  obtain ⟨b, π₂, hπ₂⟩ :=
    Module.Finite.exists_fin' R (LinearMap.ker d ⧸ B.comap (LinearMap.ker d).subtype)
  obtain ⟨g₂, hg₂⟩ := Module.projective_lifting_property
    (B.comap (LinearMap.ker d).subtype).mkQ π₂ (Submodule.mkQ_surjective _)
  let e : (Fin (a + b) → R) ≃ₗ[R] (Fin a → R) × (Fin b → R) :=
    (LinearEquiv.funCongrLeft R R finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ R R)
  refine ⟨a + b, ((LinearMap.fst R _ _ ∘ₗ N.subtype ∘ₗ g₁).coprod
    ((LinearMap.ker d).subtype ∘ₗ g₂)) ∘ₗ e.toLinearMap,
    (s ∘ₗ g₁ ∘ₗ LinearMap.fst R _ _) ∘ₗ e.toLinearMap, fun x => ?_, fun x => ?_,
    fun c k h h' => ?_⟩
  · have h1 := ((hN _).1 (g₁ (e x).1).2).1
    have h2 : d (g₂ (e x).2) = 0 := (g₂ (e x).2).2
    simp [s, h1, h2]
  · exact ((hN _).1 (g₁ (e x).1).2).2
  · obtain ⟨x, hx⟩ := hπ₁ (s.rangeRestrict ⟨(c, k), (hN _).2 ⟨h, h'⟩⟩)
    have hx' : ((g₁ x : N) : C₀ × K₁).2 = k := by
      rw [← hg₁] at hx
      exact congrArg Subtype.val hx
    have h1 := ((hN _).1 (g₁ x).2).1
    have h3 : c - ((g₁ x : N) : C₀ × K₁).1 ∈ LinearMap.ker d := by
      simp [h, h1, hx']
    obtain ⟨y, hy⟩ := hπ₂ ((B.comap (LinearMap.ker d).subtype).mkQ ⟨_, h3⟩)
    rw [← hg₂] at hy
    have h4 := (Submodule.Quotient.eq _).1 hy.symm
    refine ⟨e.symm (x, y), ?_, ?_⟩
    · simpa [sub_sub] using h4
    · simpa [s] using hx'
end GlobalTheory
