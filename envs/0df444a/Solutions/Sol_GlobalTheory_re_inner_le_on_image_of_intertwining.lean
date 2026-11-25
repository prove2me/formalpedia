-- Prove2me | solution 1 for GlobalTheory.re_inner_le_on_image_of_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:49:43.568673+00:00
-- url     : https://prove2.me/submissions/4db32dd4-ed29-47b3-aaab-b404ef217506

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwining
import Theorems.Thm_GlobalTheory_re_inner_sum_eigen_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (T N : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
      [NormedAddCommGroup N] [InnerProductSpace ℂ N] (Φ : T →ₗ[ℂ] N) (A : T →ₗ[ℂ] T)
      (B : N →ₗ[ℂ] N) (C : ℝ), A.IsSymmetric → B.IsSymmetric → (∀ x, Φ (A x) = B (Φ x)) →
      (∀ x, (⟪x, A x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) →
      ∀ x, (⟪Φ x, B (Φ x)⟫_ℂ).re ≤ C * ‖Φ x‖ ^ 2 := by
  intro T N _ _ _ _ _ Φ A B C hA hB hΦ hC x
  set b := hA.eigenvectorBasis (n := Module.finrank ℂ T) rfl with hb
  set l := hA.eigenvalues (n := Module.finrank ℂ T) rfl with hl
  have hAb : ∀ i, A (b i) = (l i : ℂ) • b i := fun i => hA.apply_eigenvectorBasis rfl i
  have hle : ∀ i, l i ≤ C := by
    intro i
    have h := hC (b i)
    rw [hAb, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i] at h
    simpa using h
  have hx : Φ x = ∑ i, Φ (b.repr x i • b i) := by
    rw [← map_sum, b.sum_repr]
  rw [hx]
  refine re_inner_sum_eigen_le B hB C _ l (fun i => ?_) hle
  rw [← hΦ, map_smul A, hAb, smul_comm, map_smul]
end GlobalTheory
