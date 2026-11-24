-- Prove2me | solution 1 for GlobalTheory.Hk.integral_integral_exp_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:52:08.377295+00:00
-- url     : https://prove2.me/submissions/9021da2b-0414-4880-8079-b1499cca19b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
import Theorems.Thm_GlobalTheory_Hk_integral_mul_exp_neg_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution (A : ℝ → ℂ) (hA : Measurable A) (K : ℝ)
    (hK : ∀ x : ℝ, 1 < x → ‖A x‖ ≤ K * Real.sqrt x) :
    ∫ t in Set.Ioi (0 : ℝ), ∫ x in Set.Ioi (1 : ℝ), A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ) =
      ∫ x in Set.Ioi (1 : ℝ), A x * (x : ℂ) ^ (-(1 : ℂ) - 1) := by
  have hm : Measurable (Function.uncurry fun (x t : ℝ) => A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ)) := by
    unfold Function.uncurry
    fun_prop
  have hint : Integrable (Function.uncurry fun (x t : ℝ) => A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ))
      ((volume.restrict (Set.Ioi (1 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      exact (Integrable.ofReal (𝕜 := ℂ) (integral_mul_exp_neg_sq hx0).1).const_mul (A x)
    · have hb : IntegrableOn (fun x : ℝ => K * x ^ (-(3 / 2) : ℝ)) (Set.Ioi 1) :=
        (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul K
      refine Integrable.mono' hb (hm.aestronglyMeasurable.norm.integral_prod_right') ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      have e : ∫ t in Set.Ioi (0 : ℝ), ‖A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ)‖ = ‖A x‖ * x ^ (-2 : ℝ) := by
        rw [← (integral_mul_exp_neg_sq hx0).2, ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have ht0 : (0 : ℝ) < t := ht
        simp only
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      simp only [Function.uncurry]
      rw [e, Real.norm_of_nonneg (by positivity)]
      calc ‖A x‖ * x ^ (-2 : ℝ) ≤ K * Real.sqrt x * x ^ (-2 : ℝ) := by
            gcongr; exact hK x hx
        _ = K * x ^ (-(3 / 2) : ℝ) := by
            rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hx0]; norm_num
  rw [← integral_integral_swap hint]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simp only
  rw [integral_const_mul, integral_complex_ofReal, (integral_mul_exp_neg_sq hx0).2,
    Complex.ofReal_cpow hx0.le]
  norm_num
end GlobalTheory.Hk
