-- Prove2me | solution 1 for GlobalTheory.AltCorank.good_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:57:42.087806+00:00
-- url     : https://prove2.me/submissions/761df901-879e-490b-aefc-a9d72add1a5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlternatingFormLeftCorankLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AltCorank
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.AltCorank
theorem _root_.solution (S₁ S₂ T₁ T₂ : Submodule K V) (u v : V) (φ ψ : V →ₗ[K] K)
    (hφu : φ u = 1) (hφv : φ v = 0) (hψu : ψ u = 0) (hψv : ψ v = 1) (hv : v ∈ S₂)
    (hu : u ∈ S₂ ∨ ∀ x ∈ S₁, ψ x = 0)
    (h₁ : ∀ x ∈ S₁, φ x = 0 → ψ x = 0 → x ∈ T₁)
    (h₂ : ∀ y ∈ T₂, y ∈ S₂ ∧ φ y = 0 ∧ ψ y = 0) (h : Good T₁ T₂) : Good S₁ S₂ := by
  obtain ⟨ω, hω, hk⟩ := h
  let π : V →ₗ[K] V := LinearMap.id - φ.smulRight u - ψ.smulRight v
  have hπ : ∀ x, π x = x - φ x • u - ψ x • v := fun x => rfl
  let Ω : V →ₗ[K] V →ₗ[K] K :=
    ω.compl₁₂ π π + (LinearMap.mul K K).compl₁₂ φ ψ - (LinearMap.mul K K).compl₁₂ ψ φ
  have hΩ : ∀ x y, Ω x y = ω (π x) (π y) + φ x * ψ y - ψ x * φ y := fun x y => rfl
  have hπu : π u = 0 := by simp [hπ, hφu, hψu]
  have hπv : π v = 0 := by simp [hπ, hφv, hψv]
  refine ⟨Ω, fun x => by rw [hΩ, hω]; ring, fun x hx hz => ?_⟩
  have e1 : ∀ a, φ (x a) = 0 := fun a => by
    have := hz a v hv
    rw [hΩ, hπv, hφv, hψv] at this
    simpa using this
  have e2 : ∀ a, ψ (x a) = 0 := fun a => by
    rcases hu with hu | hu
    · have := hz a u hu
      rw [hΩ, hπu, hφu, hψu] at this
      simpa using this
    · exact hu _ (hx a)
  refine hk x (fun a => h₁ _ (hx a) (e1 a) (e2 a)) fun a y hy => ?_
  obtain ⟨hy, f1, f2⟩ := h₂ y hy
  have := hz a y hy
  rw [hΩ, hπ, hπ, e1, e2, f1, f2] at this
  simpa using this
end GlobalTheory.AltCorank
