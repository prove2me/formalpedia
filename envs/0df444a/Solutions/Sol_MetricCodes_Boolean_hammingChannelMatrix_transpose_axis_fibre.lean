-- Prove2me | solution 1 for MetricCodes.Boolean.hammingChannelMatrix_transpose_axis_fibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/e1cd890a-4e68-46a8-8fd6-53319b1b7cb2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingWindowChannelMatrix_transpose_axis_fibre

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
        (hammingFibreMatrix n k L hk v x) =
      Real.sqrt lam • hammingFibreMatrix n k L hk v x := by
  classical
  let e := hammingWindowIndexEquiv n k L
  ext i p
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  change
    (∑ z : Fin n × Fin (hammingWindowDimension n k L),
      hammingWindowChannelMatrix n k L v lam
          (z.1, e.symm z.2) (e.symm i) *
        (hammingAxis x z.1 *
          hammingWindowFibreMatrix n k L hk v x
            (e.symm z.2) p)) =
      Real.sqrt lam *
        hammingWindowFibreMatrix n k L hk v x (e.symm i) p
  have hwindow := congrArg
    (fun M : Matrix (HammingWindowIndex n k L)
        (Fin (MetricCodes.hammingFibreDimension n k)) ℝ =>
      M (e.symm i) p)
    (hammingWindowChannelMatrix_transpose_axis_fibre
      hn hk hkL hLn v hunit hv lam hlam heigen x)
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul] at hwindow
  rw [Fintype.sum_prod_type] at hwindow ⊢
  calc
    (∑ a : Fin n,
      ∑ t : Fin (hammingWindowDimension n k L),
        hammingWindowChannelMatrix n k L v lam
            (a, e.symm t) (e.symm i) *
          (hammingAxis x a *
            hammingWindowFibreMatrix n k L hk v x
              (e.symm t) p)) =
      ∑ a : Fin n,
        ∑ T : HammingWindowIndex n k L,
          hammingWindowChannelMatrix n k L v lam
              (a, T) (e.symm i) *
            (hammingAxis x a *
              hammingWindowFibreMatrix n k L hk v x T p) := by
          apply Finset.sum_congr rfl
          intro a _
          exact e.symm.sum_comp
            (fun T : HammingWindowIndex n k L =>
              hammingWindowChannelMatrix n k L v lam
                  (a, T) (e.symm i) *
                (hammingAxis x a *
                  hammingWindowFibreMatrix n k L hk v x T p))
    _ = Real.sqrt lam *
      hammingWindowFibreMatrix n k L hk v x (e.symm i) p :=
        hwindow
end MetricCodes.Boolean
