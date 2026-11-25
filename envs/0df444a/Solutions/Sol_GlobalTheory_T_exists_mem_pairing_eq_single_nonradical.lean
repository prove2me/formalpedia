-- Prove2me | solution 1 for GlobalTheory.T.exists_mem_pairing_eq_single_nonradical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:22:43.948486+00:00
-- url     : https://prove2.me/submissions/37bc201a-1482-4686-85cf-570e8c708155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMemPairingEqSingleNonradical
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMemPairingEqSingleNonradicalStatement
import Theorems.Thm_GlobalTheory_dualV_pairing_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (r g rk : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)) (ε : Fin g → Fin r → ℚ), Mqᵀ = -Mq → LinearIndependent ℚ ε → (∀ i : Fin g, i.val < rk → ∀ w ∈ V, ε i ⬝ᵥ Mq *ᵥ w = 0) → (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → y ∈ Submodule.span ℚ (ε '' {i | i.val < rk})) → ∀ j : Fin g, rk ≤ j.val → ∃ x ∈ V, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.dualV_pairing_exists | exact GlobalTheory.dualV_pairing_exists | (intros; apply GlobalTheory.dualV_pairing_exists <;> assumption)
end _root_.GlobalTheory.T
