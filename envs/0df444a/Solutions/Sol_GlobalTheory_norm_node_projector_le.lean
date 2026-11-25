-- Prove2me | solution 1 for GlobalTheory.norm_node_projector_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:03.3186+00:00
-- url     : https://prove2.me/submissions/8058f47d-339b-480e-b450-002e9195cf33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormEigenLePowMulNormSum
import Theorems.Thm_GlobalTheory_norm_eigen_le_pow_mul_norm_sum

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
    ∀ (H κ : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [Fintype κ] [DecidableEq κ] (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (Nd : Finset κ) (s : κ) (Bd Cn : ℝ), s ∈ Nd → 0 ≤ Bd → (∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = lam i • p i x) → (∀ x ∈ VV, T x ∈ VV) → (∀ j ∈ Nd.erase s, 1 ≤ ‖lam s - lam j‖) → (∀ j ∈ Nd.erase s, ∀ x ∈ VV, ‖T x - lam j • x‖ ≤ Bd * ‖x‖) → (∀ x ∈ VV, ‖∑ i ∈ Nd, p i x‖ ≤ Cn * ‖x‖) → ∀ x ∈ VV, ‖p s x‖ ≤ Cn * Bd ^ (Nd.erase s).card * ‖x‖ := by
  intro H κ _ _ _ _ VV T p lam Nd s Bd Cn hs hBd hp _ h1 h2 hC x hx
  have h := norm_eigen_le_pow_mul_norm_sum VV T lam s Bd hBd (Nd.erase s) h1 h2
    (fun i => p i x) (fun i => hp i x hx)
  have hsum : p s x + ∑ i ∈ Nd.erase s, p i x = ∑ i ∈ Nd, p i x :=
    add_sum_erase Nd (fun i => p i x) hs
  rw [hsum] at h
  calc ‖p s x‖ ≤ Bd ^ (Nd.erase s).card * ‖∑ i ∈ Nd, p i x‖ := h
    _ ≤ Bd ^ (Nd.erase s).card * (Cn * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hC x hx) (pow_nonneg hBd _)
    _ = Cn * Bd ^ (Nd.erase s).card * ‖x‖ := by ring
end GlobalTheory
