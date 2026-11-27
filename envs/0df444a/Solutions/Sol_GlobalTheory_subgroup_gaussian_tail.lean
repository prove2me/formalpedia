-- Prove2me | solution 1 for GlobalTheory.subgroup_gaussian_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:41:53.691621+00:00
-- url     : https://prove2.me/submissions/06eb0646-637b-46e6-9a41-141dc855a2fb

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
theorem _root_.solution (G : AddSubgroup E) {b q : ℝ} (hb : 0 < b)
    (hd : (finrank ℝ E : ℝ) + 1 ≤ q * b) (hG : ∀ y ∈ G, y ≠ 0 → b ≤ ‖y‖ ^ 2) :
    Summable (fun y : {y : G // y ≠ 0} => exp (-(q * ‖(y.1 : E)‖ ^ 2))) ∧
      ∑' y : {y : G // y ≠ 0}, exp (-(q * ‖(y.1 : E)‖ ^ 2)) ≤
        2 * 3 ^ finrank ℝ E * exp (-(q * b)) :=
  gaussian_tail_addMonoidHom G.subtype hb hd fun y hy => hG y y.2 fun h => hy (Subtype.ext h)
end GlobalTheory
