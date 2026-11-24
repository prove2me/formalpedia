-- Prove2me | solution 1 for GlobalTheory.EntrySumMulBound.entrySum_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:51.670664+00:00
-- url     : https://prove2.me/submissions/248aa782-1a43-4291-9779-1da63d77836a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EntrySumMulLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EntrySumMulBound
namespace GlobalTheory.EntrySumMulBound
theorem _root_.solution :
    (let d1 : {n : Type} → [Fintype n] → Matrix n n ℂ → ℝ := @(fun {n : Type} [Fintype n] (M : Matrix n n ℂ) ↦ ∑ i : n, ∑ j : n, ‖M i j‖); ∀ {n : Type} [inst : Fintype n] (A B : Matrix n n ℂ), d1 (A * B) ≤ d1 A * d1 B) := by
  intro d1 n inst A B
  show ∑ i : n, ∑ j : n, ‖(A * B) i j‖ ≤ (∑ i : n, ∑ k : n, ‖A i k‖) * (∑ l : n, ∑ j : n, ‖B l j‖)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j : n, ‖(A * B) i j‖ ≤ ∑ j : n, ∑ k : n, ‖A i k‖ * ‖B k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k : n, ‖A i k‖ * ∑ j : n, ‖B k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ k : n, ‖A i k‖ * ∑ l : n, ∑ j : n, ‖B l j‖ := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun l => ∑ j : n, ‖B l j‖)
          (fun l _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)
    _ = (∑ k : n, ‖A i k‖) * ∑ l : n, ∑ j : n, ‖B l j‖ := (Finset.sum_mul _ _ _).symm
end GlobalTheory.EntrySumMulBound
