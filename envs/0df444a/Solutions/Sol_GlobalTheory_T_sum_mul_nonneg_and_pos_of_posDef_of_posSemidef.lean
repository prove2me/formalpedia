-- Prove2me | solution 1 for GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:24:48.101276+00:00
-- url     : https://prove2.me/submissions/f4343ba7-d14c-4a18-aeff-747b484d3232

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumHadamardPosDefPosSemidef
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumHadamardPosDefPosSemidefStatement
import Theorems.Thm_GlobalTheory_sum_hadamard_posDef_posSemidef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef → 0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by
  first | exact @GlobalTheory.sum_hadamard_posDef_posSemidef | exact GlobalTheory.sum_hadamard_posDef_posSemidef | (intros; apply GlobalTheory.sum_hadamard_posDef_posSemidef <;> assumption)
end _root_.GlobalTheory.T
