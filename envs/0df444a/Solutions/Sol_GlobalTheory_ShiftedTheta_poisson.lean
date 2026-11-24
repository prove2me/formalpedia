-- Prove2me | solution 1 for GlobalTheory.ShiftedTheta.poisson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:47:08.771997+00:00
-- url     : https://prove2.me/submissions/af734080-b45b-495a-80ee-e7156a0c3f25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableExpNegMulSq

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
    ((∑' m : ℤ, Real.exp (-(s * (m + θ) ^ 2)) : ℝ) : ℂ) =
      (Real.sqrt (Real.pi / s) : ℂ) * ∑' n : ℤ,
        cexp (-(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n) := by
  have ha : 0 < Real.pi / s := div_pos Real.pi_pos hs
  rw [Complex.tsum_exp_neg_quadratic (by rwa [ofReal_re])]
  have h1 : ((Real.pi / s : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi / s) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow ha.le]
    norm_num
  have h2 : (Real.sqrt (Real.pi / s) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  rw [h1, ← mul_assoc, mul_one_div_cancel h2, one_mul, ofReal_tsum]
  refine tsum_congr fun n => ?_
  have h3 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have h5 : I * (-I * θ) = θ := by
    rw [← mul_assoc, mul_neg, I_mul_I]; ring
  rw [h5]
  push_cast
  congr 1
  field_simp
end GlobalTheory.ShiftedTheta
