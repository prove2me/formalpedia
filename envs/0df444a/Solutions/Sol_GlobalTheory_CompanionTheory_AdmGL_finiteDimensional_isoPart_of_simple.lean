-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.finiteDimensional_isoPart_of_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:20.573174+00:00
-- url     : https://prove2.me/submissions/b764e58a-e310-4b1d-9a8d-a77f1cf7d72f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalIsoPartOfSimple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {K : Type} [Group K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
namespace GlobalTheory.CompanionTheory.AdmGL
theorem _root_.solution {π : K →* (H →L[ℂ] H)}
    (hadm : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → (∀ k, ∀ w ∈ S, π k w ∈ S) →
      (∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', π k w ∈ S') → S' = ⊥ ∨ S' = S) →
      FiniteDimensional ℂ (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
        ∀ k, ∀ w ∈ S, T (π k w) = π k (T w)} : Submodule ℂ H))
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W)
    (hs : ∀ W' : Submodule ℂ W, (∀ k, W' ≤ W'.comap (ρ k)) → W' = ⊥ ∨ W' = ⊤) :
    FiniteDimensional ℂ (isoPart π ρ) := by
  classical
  by_cases h0 : ∀ T : W →ₗ[ℂ] H, (∀ k w, T (ρ k w) = π k (T w)) → T = 0
  · have hbot : isoPart π ρ = ⊥ := by
      refine le_bot_iff.1 (iSup₂_le fun T hT => ?_)
      rw [h0 T hT, LinearMap.range_zero]
    rw [hbot]
    infer_instance
  push Not at h0
  obtain ⟨T₀, hT₀, hne⟩ := h0
  have hinj : Function.Injective T₀ := by
    rw [← LinearMap.ker_eq_bot]
    rcases hs (LinearMap.ker T₀) (fun k v hv => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hv ⊢
      rw [hT₀, hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hne
  let S : Submodule ℂ H := LinearMap.range T₀
  have hSinv : ∀ k, ∀ w ∈ S, π k w ∈ S := by
    rintro k _ ⟨v, rfl⟩
    exact ⟨ρ k v, hT₀ k v⟩
  have hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', π k w ∈ S') → S' = ⊥ ∨ S' = S := by
    intro S' hle hinv
    rcases hs (S'.comap T₀) (fun k v hv => by
      simp only [Submodule.mem_comap] at hv ⊢
      rw [hT₀]
      exact hinv k _ hv) with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨v, rfl⟩ := hle hw
      have hv : v ∈ S'.comap T₀ := hw
      rw [h, Submodule.mem_bot] at hv
      rw [hv, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ S'.comap T₀ := by rw [h]; trivial
      exact hv
  have hfin := hadm S inferInstance hSinv hSirr
  let e : W ≃ₗ[ℂ] S := LinearEquiv.ofInjective T₀ hinj
  refine Submodule.finiteDimensional_of_le
    (S₂ := sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k, ∀ w ∈ S, T (π k w) = π k (T w)})
    (iSup₂_le fun T hT => ?_)
  let T' : H →ₗ[ℂ] H := T ∘ₗ (e.symm : S →ₗ[ℂ] W) ∘ₗ (S.orthogonalProjectionOnto : H →ₗ[ℂ] S)
  have hT' : ∀ v, T' (T₀ v) = T v := by
    intro v
    have he : ((e v : S) : H) = T₀ v := LinearEquiv.ofInjective_apply _ v
    simp only [T', LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [← he, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  refine le_sSup ⟨T', ?_, ?_⟩
  · have hc : T' ∘ₗ T₀ = T := LinearMap.ext hT'
    rw [← hc, LinearMap.range_comp]
  · rintro k _ ⟨v, rfl⟩
    rw [← hT₀, hT', hT', hT]
end GlobalTheory.CompanionTheory.AdmGL
