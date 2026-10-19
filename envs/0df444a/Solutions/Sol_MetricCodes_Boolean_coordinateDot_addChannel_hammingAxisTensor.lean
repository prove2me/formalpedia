-- Prove2me | solution 1 for MetricCodes.Boolean.coordinateDot_addChannel_hammingAxisTensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/f38dc9c7-29e4-4ee0-87bb-06ea7292003a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_lowerAt_twist
import Theorems.Thm_MetricCodes_Boolean_sum_dot_twist_lowerAt

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    (i : ℕ) (x : BinaryWord n) (f g : Function n) :
    coordinateDot (addChannel i f)
      (hammingAxisTensor x (twist x g)) =
      ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        dot f (twist x (lower g)) := by
  classical
  unfold coordinateDot addChannel hammingAxisTensor
  simp only [dot_smul_left, dot_smul_right,
    hammingAxis, PiLp.toLp_apply]
  change
    (∑ a : Fin n,
      ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
        ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          dot (raiseAt a f) (twist x g))) = _
  simp_rw [dot_raiseAt_eq_lowerAt,
    lowerAt_twist, dot_smul_right]
  calc
    (∑ a : Fin n,
      ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
        ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (sign (x a) * dot f (twist x (lowerAt a g))))) =
      ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        (∑ a : Fin n, dot f (twist x (lowerAt a g))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          calc
            ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
                ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
                  (sign (x a) * dot f (twist x (lowerAt a g)))) =
              ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
                (Real.sqrt (n : ℝ))⁻¹) *
                  ((sign (x a) * sign (x a)) *
                    dot f (twist x (lowerAt a g))) := by
                      ring
            _ = ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
                (Real.sqrt (n : ℝ))⁻¹) *
                  dot f (twist x (lowerAt a g)) := by
                    rw [sign_mul_self, one_mul]
    _ = ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        dot f (twist x (lower g)) := by
          rw [sum_dot_twist_lowerAt]
end MetricCodes.Boolean
