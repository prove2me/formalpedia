-- Prove2me | solution 1 for GlobalTheory.gaussian_tail_addMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:29:38.345132+00:00
-- url     : https://prove2.me/submissions/efb54315-bcb8-4128-8e31-c687160c84cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
import Theorems.Thm_GlobalTheory_gaussian_tail_of_separated

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
theorem _root_.solution {A : Type*} [AddGroup A] (u : A →+ E) {b q : ℝ} (hb : 0 < b)
    (hd : (finrank ℝ E : ℝ) + 1 ≤ q * b) (hu : ∀ y, y ≠ 0 → b ≤ ‖u y‖ ^ 2) :
    Summable (fun y : {y : A // y ≠ 0} => exp (-(q * ‖u y‖ ^ 2))) ∧
      ∑' y : {y : A // y ≠ 0}, exp (-(q * ‖u y‖ ^ 2)) ≤ 2 * 3 ^ finrank ℝ E * exp (-(q * b)) := by
  have hq : 0 < q := by
    have : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
    exact (mul_pos_iff_of_pos_right hb).1 (by linarith)
  have hb2 : √b ^ 2 = b := sq_sqrt hb.le
  have hu' : ∀ y, y ≠ 0 → √b ≤ ‖u y‖ := fun y hy => sqrt_le_iff.2 ⟨norm_nonneg _, hu y hy⟩
  have := gaussian_tail_of_separated (fun y : {y : A // y ≠ 0} => u y) 0 (sqrt_pos.2 hb) hq
    (by rw [hb2]; linarith)
    (fun i j hij => by
      change √b ≤ dist (u i) (u j)
      rw [dist_eq_norm, ← map_sub]
      exact hu' _ (sub_ne_zero.2 fun h => hij (Subtype.ext h)))
    (fun i => by rw [sub_zero]; exact hu' _ i.2)
  simpa only [sub_zero, hb2] using this
end GlobalTheory
