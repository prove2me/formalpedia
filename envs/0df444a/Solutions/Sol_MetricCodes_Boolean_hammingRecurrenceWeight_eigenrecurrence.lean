-- Prove2me | solution 1 for MetricCodes.Boolean.hammingRecurrenceWeight_eigenrecurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/6f7f8912-d3d3-43b2-8038-f4ab17ac7333

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_mul_sqrt_choose

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1))) (lam : ℝ)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (m : Fin (L - k + 1)) :
    (∑ i : Fin (L - k + 1),
      hammingSourceChannelCoefficient n k L m i *
        hammingRecurrenceWeight n k L v i) =
      lam * hammingRecurrenceWeight n k L v m := by
  classical
  have hcoordinate := congrArg
    (fun z : EuclideanSpace ℝ (Fin (L - k + 1)) => z m)
      heigen
  change
    (∑ i : Fin (L - k + 1),
      MetricCodes.hammingJacobiMatrix n k L m i * v i) =
      lam * v m at hcoordinate
  calc
    (∑ i : Fin (L - k + 1),
      hammingSourceChannelCoefficient n k L m i *
        hammingRecurrenceWeight n k L v i) =
      ∑ i : Fin (L - k + 1),
        (MetricCodes.hammingJacobiMatrix n k L m i * v i) *
          Real.sqrt (n.choose (k + m.val) : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            unfold hammingRecurrenceWeight
            have h := hammingSourceChannelCoefficient_mul_sqrt_choose
              hkL hLn m i
            calc
              hammingSourceChannelCoefficient n k L m i *
                  (Real.sqrt (n.choose (k + i.val) : ℝ) * v i) =
                (hammingSourceChannelCoefficient n k L m i *
                  Real.sqrt (n.choose (k + i.val) : ℝ)) * v i := by
                    ring
              _ = (MetricCodes.hammingJacobiMatrix n k L m i *
                    Real.sqrt (n.choose (k + m.val) : ℝ)) * v i := by
                      rw [h]
              _ = (MetricCodes.hammingJacobiMatrix n k L m i * v i) *
                    Real.sqrt (n.choose (k + m.val) : ℝ) := by
                      ring
    _ = (∑ i : Fin (L - k + 1),
          MetricCodes.hammingJacobiMatrix n k L m i * v i) *
        Real.sqrt (n.choose (k + m.val) : ℝ) := by
          rw [Finset.sum_mul]
    _ = lam * hammingRecurrenceWeight n k L v m := by
          rw [hcoordinate]
          unfold hammingRecurrenceWeight
          ring
end MetricCodes.Boolean
