-- Prove2me | solution 1 for GlobalTheory.PMonE.normal_of_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:10:13.04857+00:00
-- url     : https://prove2.me/submissions/817ef36a-579a-4a9b-a785-7afe9bf9ad25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMul
import Theorems.Thm_GlobalTheory_PMonE_norm_inv_le_one_of_det
import Theorems.Thm_GlobalTheory_PMonE_norm_mul_apply_le_one
import Theorems.Thm_GlobalTheory_PMonE_norm_mul_apply_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open GlobalTheory GlobalTheory.PMonE
open Finset
namespace GlobalTheory.PMonE
theorem _root_.solution : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (m : Type) [Fintype m]
    [DecidableEq m] (N : ℕ) (B : ℕ → Matrix m m F), (∀ n i j, ‖B n i j‖ ≤ 1) →
    (∀ n, N < n → ∀ i j, ‖B n i j‖ < 1) → ‖(B N).det‖ = 1 →
    Normal N (fun n => (B N)⁻¹ * B n) ∧ ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := by
  intro F _ _ m _ _ N B hint hsmall hd
  have hinv : ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := norm_inv_le_one_of_det (B N) (hint N) hd
  have hunit : IsUnit (B N).det := by
    rw [isUnit_iff_ne_zero]; intro h0; rw [h0, norm_zero] at hd; exact zero_ne_one hd
  refine ⟨⟨fun n i j => norm_mul_apply_le_one _ _ hinv (hint n) i j, ?_,
    fun n hn i j => norm_mul_apply_lt_one _ _ hinv (hsmall n hn) i j⟩, hinv⟩
  exact Matrix.nonsing_inv_mul _ hunit
end GlobalTheory.PMonE
