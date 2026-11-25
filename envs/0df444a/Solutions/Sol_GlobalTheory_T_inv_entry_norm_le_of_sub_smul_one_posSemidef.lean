-- Prove2me | solution 1 for GlobalTheory.T.inv_entry_norm_le_of_sub_smul_one_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:20:37.088041+00:00
-- url     : https://prove2.me/submissions/f3a0801c-5bf2-4a71-bd12-80d5baefec7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InvEntryNormLeOfSubSmulOnePosSemidef
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InvEntryNormLeOfSubSmulOnePosSemidefStatement
import Theorems.Thm_GlobalTheory_inv_entry_norm_le_of_sub_posSemidef


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
theorem _root_.solution : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ), 0 < c → (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ∀ i j, ‖(Y.map Complex.ofReal)⁻¹ i j‖ ≤ 1 / c := by
  first | exact @GlobalTheory.inv_entry_norm_le_of_sub_posSemidef | exact GlobalTheory.inv_entry_norm_le_of_sub_posSemidef | (intros; apply GlobalTheory.inv_entry_norm_le_of_sub_posSemidef <;> assumption)
end _root_.GlobalTheory.T
