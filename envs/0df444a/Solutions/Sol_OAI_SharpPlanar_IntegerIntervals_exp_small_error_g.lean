-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.exp_small_error_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:08:15.738482+00:00
-- url     : https://prove2.me/submissions/a7736d90-4460-4497-b479-c8fd5dbc88a3

import Mathlib
import Definitions.Def_OAIQ098G017
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_expHorner_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

lemma exp_small_error_g_oai {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (precision:ℝ)*‖Complex.exp z-expHorner z 0 32‖ ≤ 1 := by
  rw [expHorner_eq_g]
  simp only [Nat.zero_add]
  have hh := Complex.exp_bound hz (n:=33) (by norm_num)
  have hp : ‖z‖^33 ≤ (1:ℝ) := pow_le_one₀ (norm_nonneg _) hz
  have hc : (34:ℝ)*((33).factorial*33:ℝ)⁻¹ ≤ 1/10^30 := by norm_num
  have hb : ‖Complex.exp z-∑ n ∈ Finset.range 33, z^n/(n.factorial:ℂ)‖ ≤ 1/10^30 :=
    hh.trans ((mul_le_of_le_one_left (by positivity) hp).trans hc)
  dsimp [precision]
  norm_num
  nlinarith only [hb]

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.exp_small_error_g_oai := @OAI.SharpPlanar.IntegerIntervals.exp_small_error_g_oai
