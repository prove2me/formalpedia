-- Prove2me | solution 1 for GlobalTheory.SummableSeriesBounds.decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:47.76581+00:00
-- url     : https://prove2.me/submissions/c4a078ac-ac25-48fc-ad21-cf486d16a725

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded
import Theorems.Thm_GlobalTheory_SummableSeriesBounds_coeff_zero_lin
import Theorems.Thm_GlobalTheory_SummableSeriesBounds_coeff_succ_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableSeriesBounds
open PowerSeries Filter Topology
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
namespace GlobalTheory.SummableSeriesBounds
theorem _root_.solution {π : C} (hπ : ‖π‖ < 1) {b : ℝ} {G : PowerSeries C} (hb : ∀ m, ‖coeff m G‖ ≤ b)
    (n m : ℕ) : ‖coeff m ((X - PowerSeries.C π) ^ n * G)‖ ≤ ‖π‖ ^ (n - m) * b := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  induction n generalizing m with
  | zero => simpa using hb m
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    cases m with
    | zero =>
      rw [coeff_zero_lin, norm_neg, norm_mul]
      refine (mul_le_mul_of_nonneg_left (ih 0) (norm_nonneg _)).trans (le_of_eq ?_)
      simp only [Nat.sub_zero]; ring
    | succ m =>
      rw [coeff_succ_lin, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · simpa using ih m
      · rw [norm_neg, norm_mul]
        refine (mul_le_mul_of_nonneg_left (ih (m + 1)) (norm_nonneg _)).trans ?_
        rw [← mul_assoc, ← pow_succ']
        refine mul_le_mul_of_nonneg_right ?_ hb0
        exact pow_le_pow_of_le_one (norm_nonneg _) hπ.le (by omega)
end GlobalTheory.SummableSeriesBounds
