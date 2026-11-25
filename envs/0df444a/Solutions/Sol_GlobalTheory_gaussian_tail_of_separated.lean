-- Prove2me | solution 1 for GlobalTheory.gaussian_tail_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:22:30.352329+00:00
-- url     : https://prove2.me/submissions/5c1887ca-676a-4b5c-84d8-e56681606fe0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
import Theorems.Thm_GlobalTheory_summable_exp_neg_of_card_le
import Theorems.Thm_GlobalTheory_finset_card_le_of_separated_family

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} (u : ι → E) (w : E) {r q : ℝ} (hr : 0 < r)
    (hq : 0 < q) (hd : (finrank ℝ E : ℝ) ≤ q * r ^ 2)
    (hu : Pairwise fun i j => r ≤ dist (u i) (u j)) (hw : ∀ i, r ≤ ‖u i - w‖) :
    Summable (fun i => exp (-(q * ‖u i - w‖ ^ 2))) ∧
      ∑' i, exp (-(q * ‖u i - w‖ ^ 2)) ≤ 2 * 3 ^ finrank ℝ E * exp (-(q * r ^ 2)) := by
  refine summable_exp_neg_of_card_le (fun i => q * ‖u i - w‖ ^ 2) (fun i => ?_) ?_
  · have := hw i
    gcongr
  · intro s v hv hs
    have ht : 0 < q * r ^ 2 := by positivity
    have hv0 : 0 < v := ht.trans_le hv
    set R := √(v / q) with hRdef
    have hR0 : 0 ≤ R := sqrt_nonneg _
    have hR2 : R ^ 2 = v / q := sq_sqrt (by positivity)
    have hcard := finset_card_le_of_separated_family u hr hR0 hu w s fun i hi => by
      rw [dist_eq_norm]
      refine le_sqrt_of_sq_le ?_
      rw [le_div_iff₀ hq, mul_comm]
      exact hs i hi
    refine hcard.trans ?_
    set x := R / r with hx
    have hx0 : 0 ≤ x := by positivity
    have hx2 : x ^ 2 = v / (q * r ^ 2) := by rw [hx, div_pow, hR2]; field_simp
    have hx1 : 1 ≤ x ^ 2 := by rw [hx2]; exact (one_le_div ht).2 hv
    have h1 : 1 + 2 * R / r ≤ 3 * exp ((x ^ 2 - 1) / 2) := by
      have := add_one_le_exp ((x ^ 2 - 1) / 2)
      rw [mul_div_assoc, ← hx]
      nlinarith [sq_nonneg (x - 1)]
    calc (1 + 2 * R / r) ^ finrank ℝ E ≤ (3 * exp ((x ^ 2 - 1) / 2)) ^ finrank ℝ E :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = 3 ^ finrank ℝ E * exp ((finrank ℝ E : ℝ) * ((x ^ 2 - 1) / 2)) := by
          rw [mul_pow, exp_nat_mul]
      _ ≤ 3 ^ finrank ℝ E * exp (q * r ^ 2 * ((x ^ 2 - 1) / 2)) := by
          gcongr
      _ = _ := by rw [hx2]; congr 2; field_simp
end GlobalTheory
