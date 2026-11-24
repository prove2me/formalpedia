-- Prove2me | solution 1 for GlobalTheory.LGrowth.norm_mellin_summatory_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:33.02574+00:00
-- url     : https://prove2.me/submissions/e80809bf-7706-4d75-86c0-f2ed2fb389da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtMellinSummatory
import Theorems.Thm_GlobalTheory_LGrowth_mellin_summatory

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LGrowth
open Filter Topology Asymptotics
variable {f : ℕ → ℂ} {C : ℝ}
namespace GlobalTheory.LGrowth
theorem _root_.solution (hC : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    ‖mellin (summatory f) (-s)‖ ≤ C / s.re := by
  rw [mellin_summatory]
  have hlt : -(s.re + 1) < -1 := by linarith
  refine (norm_integral_le_of_norm_le (g := fun t : ℝ => C * t ^ (-(s.re + 1)))
    ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul C) ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.rpow_nonneg ht0.le _)
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt zero_lt_one, Real.one_rpow]
    refine le_of_eq ?_
    have : -(s.re + 1) + 1 = -s.re := by ring
    rw [this]
    field_simp
end GlobalTheory.LGrowth
