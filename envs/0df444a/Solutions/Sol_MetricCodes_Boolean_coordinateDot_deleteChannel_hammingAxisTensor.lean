-- Prove2me | solution 1 for MetricCodes.Boolean.coordinateDot_deleteChannel_hammingAxisTensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/ee619690-85b9-4051-8f9a-9293dc7021b7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_raiseAt_twist
import Theorems.Thm_MetricCodes_Boolean_sum_dot_twist_raiseAt

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
    coordinateDot (deleteChannel i f)
      (hammingAxisTensor x (twist x g)) =
      ((Real.sqrt (i : ℝ))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        dot f (twist x (raise g)) := by
  classical
  unfold coordinateDot deleteChannel hammingAxisTensor
  simp only [dot_smul_left, dot_smul_right,
    hammingAxis, PiLp.toLp_apply]
  change
    (∑ a : Fin n,
      ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
        ((Real.sqrt (i : ℝ))⁻¹ *
          dot (lowerAt a f) (twist x g))) = _
  simp_rw [dot_lowerAt_eq_raiseAt,
    raiseAt_twist, dot_smul_right]
  calc
    (∑ a : Fin n,
      ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
        ((Real.sqrt (i : ℝ))⁻¹ *
          (sign (x a) * dot f (twist x (raiseAt a g))))) =
      ((Real.sqrt (i : ℝ))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        (∑ a : Fin n, dot f (twist x (raiseAt a g))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          calc
            ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
                ((Real.sqrt (i : ℝ))⁻¹ *
                  (sign (x a) * dot f (twist x (raiseAt a g)))) =
              ((Real.sqrt (i : ℝ))⁻¹ *
                (Real.sqrt (n : ℝ))⁻¹) *
                  ((sign (x a) * sign (x a)) *
                    dot f (twist x (raiseAt a g))) := by
                      ring
            _ = ((Real.sqrt (i : ℝ))⁻¹ *
                (Real.sqrt (n : ℝ))⁻¹) *
                  dot f (twist x (raiseAt a g)) := by
                    rw [sign_mul_self, one_mul]
    _ = ((Real.sqrt (i : ℝ))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        dot f (twist x (raise g)) := by
          rw [sum_dot_twist_raiseAt]
end MetricCodes.Boolean
