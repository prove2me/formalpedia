-- Prove2me | solution 1 for MetricCodes.Boolean.sum_sign_mul_eq_hammingDist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/44a95789-28c5-43fc-841c-48455422a7d1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_sign_mul_eq_difference_indicator

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    (x y : BinaryWord n) :
    (∑ a : Fin n, sign (x a) * sign (y a)) =
      (n : ℝ) - 2 * (MetricCodes.hammingDist x y : ℝ) := by
  classical
  calc
    (∑ a : Fin n, sign (x a) * sign (y a)) =
        ∑ a : Fin n,
          (1 - 2 * (if x a ≠ y a then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact sign_mul_eq_difference_indicator (x a) (y a)
    _ = (n : ℝ) - 2 * (MetricCodes.hammingDist x y : ℝ) := by
      have hcount :
          (∑ a : Fin n,
            if x a ≠ y a then (1 : ℝ) else 0) =
              (MetricCodes.hammingDist x y : ℝ) := by
        simpa only [MetricCodes.hammingDist] using
          (Finset.sum_boole (R := ℝ)
            (fun a : Fin n => x a ≠ y a)
            (Finset.univ : Finset (Fin n)))
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hcount]
      simp
end MetricCodes.Boolean
