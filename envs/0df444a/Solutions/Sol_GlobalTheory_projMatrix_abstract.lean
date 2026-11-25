-- Prove2me | solution 1 for GlobalTheory.projMatrix_abstract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:32.808842+00:00
-- url     : https://prove2.me/submissions/aa6d7d72-14c7-43ea-84fa-f5e8e4346bed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMatricesOfProjectiveComplex
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_IsGradedMap_id
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S : Type} [CommRing S] {P₀ P₁ P₂ F₀ F₁ G₁ G₂ : Type}
    [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂]
    [AddCommGroup F₀] [Module S F₀] [AddCommGroup F₁] [Module S F₁]
    [AddCommGroup G₁] [Module S G₁] [AddCommGroup G₂] [Module S G₂]
    (d₀ : P₀ →ₗ[S] P₁) (d₁ : P₁ →ₗ[S] P₂) (p₀ : F₀ →ₗ[S] P₀) (s₀ : P₀ →ₗ[S] F₀)
    (p₁ : F₁ →ₗ[S] P₁) (s₁ : P₁ →ₗ[S] F₁) (D₀ : F₀ →ₗ[S] G₁) (D₁ : G₁ →ₗ[S] G₂)
    (q₁ : G₁ →ₗ[S] F₁) (q₀ : G₁ →ₗ[S] F₀) (i₁ : F₁ →ₗ[S] G₁) (i₀ : F₀ →ₗ[S] G₁)
    (r₂ : G₂ →ₗ[S] P₂) (r₁ : G₂ →ₗ[S] F₁) (r₀ : G₂ →ₗ[S] P₀)
    (h₀ : p₀ ∘ₗ s₀ = LinearMap.id) (h₁ : p₁ ∘ₗ s₁ = LinearMap.id)
    (hq₁ : q₁ ∘ₗ D₀ = s₁ ∘ₗ d₀ ∘ₗ p₀) (hq₀ : q₀ ∘ₗ D₀ = LinearMap.id - s₀ ∘ₗ p₀)
    (hi : i₁ ∘ₗ q₁ + i₀ ∘ₗ q₀ = LinearMap.id)
    (hr₂ : r₂ ∘ₗ D₁ = d₁ ∘ₗ p₁ ∘ₗ q₁) (hr₁ : r₁ ∘ₗ D₁ = q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁)
    (hr₀ : r₀ ∘ₗ D₁ = p₀ ∘ₗ q₀) :
    Set.BijOn p₀ {v | D₀ v = 0} (LinearMap.ker d₀) ∧
      (Function.Exact d₀ d₁ → ∀ w, D₁ w = 0 → ∃ v, D₀ v = w) := by
  have h₀ : ∀ x, p₀ (s₀ x) = x := fun x => LinearMap.congr_fun h₀ x
  have h₁ : ∀ x, p₁ (s₁ x) = x := fun x => LinearMap.congr_fun h₁ x
  have hq₁ : ∀ x, q₁ (D₀ x) = s₁ (d₀ (p₀ x)) := fun x => LinearMap.congr_fun hq₁ x
  have hq₀ : ∀ x, q₀ (D₀ x) = x - s₀ (p₀ x) := fun x => LinearMap.congr_fun hq₀ x
  have hi : ∀ x, i₁ (q₁ x) + i₀ (q₀ x) = x := fun x => LinearMap.congr_fun hi x
  have hr₂ : ∀ x, r₂ (D₁ x) = d₁ (p₁ (q₁ x)) := fun x => LinearMap.congr_fun hr₂ x
  have hr₁ : ∀ x, r₁ (D₁ x) = q₁ x - s₁ (p₁ (q₁ x)) := fun x => LinearMap.congr_fun hr₁ x
  have hr₀ : ∀ x, r₀ (D₁ x) = p₀ (q₀ x) := fun x => LinearMap.congr_fun hr₀ x
  have key : ∀ v, D₀ v = 0 → s₀ (p₀ v) = v := fun v hv => by
    have := hq₀ v
    rw [hv, map_zero] at this
    exact (sub_eq_zero.mp this.symm).symm
  refine ⟨⟨fun v hv => ?_, fun v hv v' hv' h => ?_, fun x hx => ⟨s₀ x, ?_, h₀ x⟩⟩, ?_⟩
  · have hv : D₀ v = 0 := hv
    have := congrArg p₁ (hq₁ v)
    rw [hv, map_zero, map_zero, h₁] at this
    exact this.symm
  · rw [← key v hv, ← key v' hv', h]
  · have hx : d₀ x = 0 := hx
    show D₀ (s₀ x) = 0
    rw [← hi (D₀ (s₀ x)), hq₁, hq₀, h₀, hx]
    simp
  · intro hex w hw
    have e₂ := hr₂ w
    have e₁ := hr₁ w
    have e₀ := hr₀ w
    rw [hw, map_zero] at e₂ e₁ e₀
    obtain ⟨x, hx⟩ := (hex _).mp e₂.symm
    refine ⟨s₀ x + q₀ w, ?_⟩
    have hp : p₀ (s₀ x + q₀ w) = x := by rw [map_add, h₀, ← e₀, add_zero]
    rw [← hi (D₀ _), hq₁, hq₀, hp, hx, ← sub_eq_zero.mp e₁.symm, add_sub_cancel_left, hi]
end GlobalTheory
