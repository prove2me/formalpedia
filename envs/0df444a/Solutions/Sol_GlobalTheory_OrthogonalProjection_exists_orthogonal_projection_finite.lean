-- Prove2me | solution 1 for GlobalTheory.OrthogonalProjection.exists_orthogonal_projection_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:17:27.498408+00:00
-- url     : https://prove2.me/submissions/421cd03c-8d25-4e18-b254-4308244a3d47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOrthogonalProjectionFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrthogonalProjection
open Module
namespace GlobalTheory.OrthogonalProjection
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hB : ∀ v : W, B v v = 0 → v = 0) (M : Submodule ℂ W) [FiniteDimensional ℂ M] (v : W) :
    ∃ m ∈ M, ∀ z ∈ M, B z (v - m) = 0 := by
  classical
  let b : Basis (Fin (finrank ℂ M)) ℂ M := Module.finBasis ℂ M
  let T : M →ₗ[ℂ] (Fin (finrank ℂ M) → ℂ) :=
    LinearMap.pi (fun i => (B (b i : W)).comp M.subtype)
  have key : ∀ w : W, (∀ i, B (b i : W) w = 0) → ∀ z ∈ M, B z w = 0 := by
    intro w hw z hz
    have h0 : (B.flip w).comp M.subtype = 0 := by
      apply b.ext
      intro i
      simpa using hw i
    have := LinearMap.congr_fun h0 ⟨z, hz⟩
    simpa using this
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    have h1 : ∀ i, B (b i : W) (m : W) = 0 := by
      intro i
      have := congr_fun hm i
      simpa [T] using this
    have h2 := key m h1 m m.2
    exact Subtype.ext (hB _ h2)
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun])).mp hinj
  obtain ⟨m, hm⟩ := hsurj (fun i => B (b i : W) v)
  refine ⟨m, m.2, ?_⟩
  apply key
  intro i
  have := congr_fun hm i
  simp [T] at this
  simp [map_sub, this]
end GlobalTheory.OrthogonalProjection
