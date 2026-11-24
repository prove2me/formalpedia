-- Prove2me | solution 1 for GlobalTheory.gaussian_phase_critical_value_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:07:30.419871+00:00
-- url     : https://prove2.me/submissions/9f71a3f0-a2c6-41a6-8ce1-55de784e5169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GaussianPhaseCriticalValueBlocksGeneral
import Theorems.Thm_GlobalTheory_gaussian_phase_critical_value_blocks_general

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ) (a c : Fin P → ℂ) (b d : Fin Q → ℂ), IsUnit (1 - Aᴴ * B).det → let S : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 Aᴴᵀ Aᴴ 0; let T : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 B Bᵀ 0; let w : Fin P ⊕ Fin Q → ℂ := (1 - T * S)⁻¹ *ᵥ (Sum.elim c d + T *ᵥ Sum.elim a b); let u : Fin P ⊕ Fin Q → ℂ := Sum.elim a b + S *ᵥ w; 1 / 2 * (Sum.elim a b ⬝ᵥ w + Sum.elim c d ⬝ᵥ u) = a ⬝ᵥ (1 - B * Aᴴ)⁻¹ *ᵥ c + d ⬝ᵥ (1 - Aᴴ * B)⁻¹ *ᵥ b + a ⬝ᵥ ((1 - B * Aᴴ)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - Aᴴ * B)⁻¹ * Aᴴ) *ᵥ c :=
  fun _ _ A B a c b d h => gaussian_phase_critical_value_blocks_general Aᴴ B a c b d h
end GlobalTheory
