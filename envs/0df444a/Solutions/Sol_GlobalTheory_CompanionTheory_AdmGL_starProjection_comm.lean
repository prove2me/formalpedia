-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.starProjection_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:22.085732+00:00
-- url     : https://prove2.me/submissions/e995a8fd-dc46-4cc7-8bbd-33da1841ae19

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
namespace GlobalTheory.CompanionTheory.AdmGL
theorem _root_.solution {π : K →* (H →L[ℂ] H)} (hπ : ∀ k v, ‖π k v‖ = ‖v‖) (R : Submodule ℂ H)
    [FiniteDimensional ℂ R] (hR : ∀ k, ∀ w ∈ R, π k w ∈ R) (k : K) (x : H) :
    R.starProjection (π k x) = π k (R.starProjection x) := by
  have hinner : ∀ u v, ⟪π k u, π k v⟫_ℂ = ⟪u, v⟫_ℂ := fun u v =>
    (⟨(π k : H →ₗ[ℂ] H), hπ k⟩ : H →ₗᵢ[ℂ] H).inner_map_map u v
  have hsurj : ∀ w ∈ R, ∃ w' ∈ R, π k w' = w := by
    intro w hw
    refine ⟨π k⁻¹ w, hR _ w hw, ?_⟩
    change (π k * π k⁻¹) w = w
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hR k _ (R.starProjection_apply_mem x))
  intro w hw
  obtain ⟨w', hw', rfl⟩ := hsurj w hw
  rw [← map_sub, hinner]
  exact (Submodule.mem_orthogonal' _ _).1 (R.sub_starProjection_mem_orthogonal x) w' hw'
end GlobalTheory.CompanionTheory.AdmGL
