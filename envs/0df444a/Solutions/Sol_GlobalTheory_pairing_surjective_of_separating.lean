-- Prove2me | solution 1 for GlobalTheory.pairing_surjective_of_separating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:22.587877+00:00
-- url     : https://prove2.me/submissions/ae5a1125-1e35-412d-8a94-3d75ad2786c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorProductNondegeneratePairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
namespace GlobalTheory
theorem _root_.solution {M N : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N] (b : M →ₗ[ℂ] N →ₗ[ℂ] ℂ)
    (hb : ∀ u, u ≠ 0 → ∃ v, b v u ≠ 0) : Function.Surjective b := by
  rw [← LinearMap.range_eq_top]
  have hco : (LinearMap.range b).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_dualCoannihilator] at hu
    by_contra h0
    obtain ⟨v, hv⟩ := hb u h0
    exact hv (hu _ ⟨v, rfl⟩)
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range b), hco,
    Submodule.dualAnnihilator_bot]
end GlobalTheory
