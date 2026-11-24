-- Prove2me | solution 1 for GlobalTheory.T.normal_inv_mul_and_norm_inv_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:19:39.375081+00:00
-- url     : https://prove2.me/submissions/f89e9b0b-a5b9-48d2-b7d1-4ae918b12375

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMulStatement
import Theorems.Thm_GlobalTheory_PMonE_normal_of_inv_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (m : Type) [Fintype m] [DecidableEq m] (N : ℕ) (B : ℕ → Matrix m m F), (∀ n i j, ‖B n i j‖ ≤ 1) → (∀ n, N < n → ∀ i j, ‖B n i j‖ < 1) → ‖(B N).det‖ = 1 → Normal N (fun n => (B N)⁻¹ * B n) ∧ ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := by
  first | exact @GlobalTheory.PMonE.normal_of_inv_mul | exact GlobalTheory.PMonE.normal_of_inv_mul | (intros; apply GlobalTheory.PMonE.normal_of_inv_mul <;> assumption)
end _root_.GlobalTheory.T
