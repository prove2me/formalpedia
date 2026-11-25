-- Prove2me | solution 1 for GlobalTheory.gaussian_tail_sum_le_of_min_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:43:53.666457+00:00
-- url     : https://prove2.me/submissions/ec81161f-4a5c-4aba-a996-e18c336469e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
import Theorems.Thm_GlobalTheory_gaussian_tail_addMonoidHom

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
theorem _root_.solution {A : Type*} [AddGroup A] (u : A →+ E) {b q : ℝ}
    (hb : 0 < b) (hd : (finrank ℝ E : ℝ) + 1 ≤ q * b) (hu : ∀ y, y ≠ 0 → b ≤ ‖u y‖ ^ 2) :
    Summable (fun y : {y : A // y ≠ 0} => exp (-(q * ‖u y‖ ^ 2))) ∧
      ∑' y : {y : A // y ≠ 0}, exp (-(q * ‖u y‖ ^ 2)) ≤
        2 * 4.3 ^ finrank ℝ E * exp (-(q * b)) := by
  have h := gaussian_tail_addMonoidHom u hb hd hu
  refine ⟨h.1, h.2.trans ?_⟩
  gcongr; norm_num
end GlobalTheory
