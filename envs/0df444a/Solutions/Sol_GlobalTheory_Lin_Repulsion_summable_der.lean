-- Prove2me | solution 1 for GlobalTheory.Lin.Repulsion.summable_der
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:43:56.900316+00:00
-- url     : https://prove2.me/submissions/10dc21c5-7eb3-4ecb-97a3-a004b0fe1840

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.Repulsion
namespace GlobalTheory.Lin.Repulsion
theorem _root_.solution (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (k : ℕ) (t : ℝ) :
    Summable fun n : ℕ => ((Λ n : ℝ) : ℂ) * c n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) *
      (n : ℂ) ^ (-((2 : ℂ) + t * I)) := by
  have hO : (fun n : ℕ => Real.log n ^ (k + 1)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) := by
    have := (isLittleO_log_rpow_rpow_atTop ((k + 1 : ℕ) : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)).isBigO
    have := this.comp_tendsto tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Real.rpow_natCast] using this
  have hS : Summable fun n : ℕ => Real.log n ^ (k + 1) * (n : ℝ) ^ (-2 : ℝ) := by
    refine summable_of_isBigO_nat (Real.summable_nat_rpow.2 (show (-3 / 2 : ℝ) < -1 by norm_num)) ?_
    refine (hO.mul (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) atTop)).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← Real.rpow_add (by exact_mod_cast hn)]; norm_num
  refine Summable.of_norm_bounded hS fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, norm_div, norm_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
    Real.norm_of_nonneg hl, Complex.norm_natCast]
  have e : (-((2 : ℂ) + t * I)).re = -2 := by simp
  rw [e, pow_succ']
  have hf : (1 : ℝ) ≤ k.factorial := by exact_mod_cast k.factorial_pos
  gcongr
  · calc Λ n * ‖c n‖ ≤ Real.log n * 1 := by gcongr; exacts [vonMangoldt_le_log, hc n]
      _ = _ := mul_one _
  · exact div_le_self (by positivity) hf
end GlobalTheory.Lin.Repulsion
