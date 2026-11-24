-- Prove2me | solution 1 for GlobalTheory.ShiftedTheta.summable_shifted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:28:43.3753+00:00
-- url     : https://prove2.me/submissions/4c0d779c-ab9e-4c32-b886-b7fb34feabfb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableExpNegMulSq
import Theorems.Thm_GlobalTheory_ShiftedTheta_summable_exp_neg_mul_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ShiftedTheta
namespace GlobalTheory.ShiftedTheta
theorem _root_.solution {s : ℝ} (θ : ℝ) (hs : 0 < s) :
    Summable fun m : ℤ => Real.exp (-(s * (m + θ) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_)
    ((summable_exp_neg_mul_sq (half_pos hs)).mul_left (Real.exp (s * θ ^ 2)))
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg hs.le (sq_nonneg ((m : ℝ) + 2 * θ))]
end GlobalTheory.ShiftedTheta
