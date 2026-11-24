-- Prove2me | solution 1 for GlobalTheory.taylorTail_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:59.181986+00:00
-- url     : https://prove2.me/submissions/3e782dcd-cc03-4932-8160-2b92e9bedcd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralTaylorTailIteratedDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (j : ℕ) (s : ℝ) (hs : 0 < s) :
    ∫⁻ t in Ioo (0:ℝ) s, ENNReal.ofReal (t ^ j / (j.factorial : ℝ))
      = ENNReal.ofReal (s ^ (j+1) / ((j+1).factorial : ℝ)) := by
  have hcont : Continuous (fun t : ℝ => t ^ j / (j.factorial : ℝ)) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.le,
      intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
    push_cast
    rw [zero_pow (Nat.succ_ne_zero j), sub_zero, div_div, mul_comm]
  · exact (hcont.integrableOn_Icc (a := 0) (b := s)).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact div_nonneg (pow_nonneg ht.1.le _) (by positivity)
end GlobalTheory
