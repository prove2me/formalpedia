-- Prove2me | solution 1 for GlobalTheory.weighted_fejer_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:33.065208+00:00
-- url     : https://prove2.me/submissions/b500901f-ef7d-4524-a47c-4a64369b1974

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeightedFejerPositivity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (J : ℕ) (θ : ℝ) (w : ℂ) :
    ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re
      = ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1))
            * ((w * Complex.exp (θ * I)) ^ j).re) / 2
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1))
            * ((w * Complex.exp (-(θ * I))) ^ j).re) / 2 := by
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : Complex.exp (θ * I) ^ j = Complex.exp (((j * θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Complex.exp (-(θ * I)) ^ j = Complex.exp (((-(j * θ) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, mul_pow, e1, e2, Complex.mul_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg]
  ring
end GlobalTheory
