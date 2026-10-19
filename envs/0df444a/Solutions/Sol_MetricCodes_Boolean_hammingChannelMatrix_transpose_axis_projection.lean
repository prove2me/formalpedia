-- Prove2me | solution 1 for MetricCodes.Boolean.hammingChannelMatrix_transpose_axis_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/55b2c9bc-34fb-45de-ab51-2ab3785b3561

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingChannelMatrix_transpose_axis_fibre

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    {n k L : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (x : BinaryWord n) :
    (hammingChannelMatrix n k L v lam)ᵀ *
      matrixAxisLift (fun a : Fin n => hammingAxis x a)
        ((hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).projection x) =
      Real.sqrt lam •
        ((hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).projection x) := by
  let A := hammingFibreMatrix n k L hk v x
  change
    (hammingChannelMatrix n k L v lam)ᵀ *
      matrixAxisLift (fun a : Fin n => hammingAxis x a)
        (A * Aᵀ) =
      Real.sqrt lam • (A * Aᵀ)
  rw [matrixAxisLift_mul, ← Matrix.mul_assoc,
    hammingChannelMatrix_transpose_axis_fibre
      hn hk hkL hLn v hunit hv lam hlam heigen x,
    Matrix.smul_mul]
end MetricCodes.Boolean
