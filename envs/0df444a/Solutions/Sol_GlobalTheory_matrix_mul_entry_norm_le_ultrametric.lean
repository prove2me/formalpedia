-- Prove2me | solution 1 for GlobalTheory.matrix_mul_entry_norm_le_ultrametric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:00.443644+00:00
-- url     : https://prove2.me/submissions/2aff5f98-a44e-413e-b53d-60bc78bad67f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixMulEntryNormLeUltrametric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (A B : Matrix n n E) (a b : ℝ), 0 ≤ a → 0 ≤ b → (∀ i j, ‖A i j‖ ≤ a) → (∀ i j, ‖B i j‖ ≤ b) →
      ∀ i j, ‖(A * B) i j‖ ≤ a * b := by
  intro E _ _ n _ _ A B a b ha hb hA hB i j
  rw [Matrix.mul_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb)
  intro k _
  rw [norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha
end GlobalTheory
