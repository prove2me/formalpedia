-- Prove2me | solution 1 for GlobalTheory.IsotypicOrth.pair_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:58.773382+00:00
-- url     : https://prove2.me/submissions/a872fa80-1551-4a7e-8aec-2999726b560c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsComplOrthogonalOfNoCommonIrreducibleTypes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.IsotypicOrth
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
  {σ : K →* K}
namespace GlobalTheory.IsotypicOrth
theorem _root_.solution (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    (k : K) (x y : V) : B (ρ k x) y = B x (ρ (σ k⁻¹) y) := by
  rw [← hB k x (ρ (σ k⁻¹) y), map_inv, Representation.self_inv_apply]
end GlobalTheory.IsotypicOrth
