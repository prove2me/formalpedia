-- Prove2me | solution 1 for GlobalTheory.matrix_one_add_pow_sub_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:18.983873+00:00
-- url     : https://prove2.me/submissions/4bac4311-00e8-41ca-9353-b53db7af7b82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixOneAddPowSubEntryLe
import Theorems.Thm_GlobalTheory_ultra_matrix_mul_entry_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (Y : Matrix n n E) (t : ℝ), 0 ≤ t → t ≤ 1 → (∀ i j, ‖Y i j‖ ≤ t) →
      ∀ (m : ℕ) i j, ‖((1 + Y) ^ m - 1 - (m : E) • Y) i j‖ ≤ t ^ 2 := by
  intro E _ _ n _ _ Y t ht0 ht1 hY m
  induction m with
  | zero => intro i j; simp; positivity
  | succ m ih =>
    have key : (1 + Y) ^ (m + 1) - 1 - ((m + 1 : ℕ) : E) • Y
        = ((1 + Y) ^ m - 1 - (m : E) • Y) + ((1 + Y) ^ m - 1 - (m : E) • Y) * Y
          + (m : E) • (Y * Y) := by
      rw [pow_succ]
      push_cast
      simp only [mul_add, add_mul, mul_one, one_mul, sub_mul, smul_mul_assoc, add_smul, one_smul]
      abel
    intro i j
    rw [key]
    have h1 := ih i j
    have h2 : ‖(((1 + Y) ^ m - 1 - (m : E) • Y) * Y) i j‖ ≤ t ^ 2 := by
      have := ultra_matrix_mul_entry_le _ Y (t ^ 2) t (by positivity) ht0 ih hY i j
      calc _ ≤ t ^ 2 * t := this
        _ ≤ t ^ 2 * 1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
        _ = t ^ 2 := mul_one _
    have h3 : ‖((m : E) • (Y * Y)) i j‖ ≤ t ^ 2 := by
      rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
      have := ultra_matrix_mul_entry_le Y Y t t ht0 ht0 hY hY i j
      calc ‖(m : E)‖ * ‖(Y * Y) i j‖ ≤ 1 * (t * t) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one E m) this (norm_nonneg _) zero_le_one
        _ = t ^ 2 := by ring
    rw [Matrix.add_apply, Matrix.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)) h3)
end GlobalTheory
