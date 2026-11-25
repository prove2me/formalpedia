-- Prove2me | solution 1 for GlobalTheory.T.norm_det_ofReal_le_factorial_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:23:29.301505+00:00
-- url     : https://prove2.me/submissions/6a1b1e67-0261-4803-8b34-a9e8833d29f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormDetOfRealLeFactorialMulPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormDetOfRealLeFactorialMulPowStatement
import Theorems.Thm_GlobalTheory_det_map_ofReal_norm_le


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ), 0 ≤ M → Y.PosSemidef → (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef → ‖(Y.map Complex.ofReal).det‖ ≤ (g.factorial : ℝ) * M ^ g := by
  first | exact @GlobalTheory.det_map_ofReal_norm_le | exact GlobalTheory.det_map_ofReal_norm_le | (intros; apply GlobalTheory.det_map_ofReal_norm_le <;> assumption)
end _root_.GlobalTheory.T
