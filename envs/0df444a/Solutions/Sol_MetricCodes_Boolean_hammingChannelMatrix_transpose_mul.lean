-- Prove2me | solution 1 for MetricCodes.Boolean.hammingChannelMatrix_transpose_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/9139a00f-8580-4e2e-b97c-fbef47517bf1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingWindowChannelMatrix_transpose_mul

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v) :
    (hammingChannelMatrix n k L v lam)ᵀ *
      hammingChannelMatrix n k L v lam = 1 := by
  classical
  let e := hammingWindowIndexEquiv n k L
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  change
    (∑ p : Fin n × Fin (hammingWindowDimension n k L),
      hammingWindowChannelMatrix n k L v lam
          (p.1, e.symm p.2) (e.symm i) *
        hammingWindowChannelMatrix n k L v lam
          (p.1, e.symm p.2) (e.symm j)) =
      if i = j then 1 else 0
  have hwindow := congrArg
    (fun M : Matrix (HammingWindowIndex n k L)
        (HammingWindowIndex n k L) ℝ =>
      M (e.symm i) (e.symm j))
    (hammingWindowChannelMatrix_transpose_mul
      hn hkL hLn v hv lam hlam heigen)
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply] at hwindow
  rw [Fintype.sum_prod_type] at hwindow ⊢
  calc
    (∑ a : Fin n,
      ∑ t : Fin (hammingWindowDimension n k L),
        hammingWindowChannelMatrix n k L v lam
            (a, e.symm t) (e.symm i) *
          hammingWindowChannelMatrix n k L v lam
            (a, e.symm t) (e.symm j)) =
      ∑ a : Fin n,
        ∑ T : HammingWindowIndex n k L,
          hammingWindowChannelMatrix n k L v lam
              (a, T) (e.symm i) *
            hammingWindowChannelMatrix n k L v lam
              (a, T) (e.symm j) := by
          apply Finset.sum_congr rfl
          intro a _
          exact e.symm.sum_comp
            (fun T : HammingWindowIndex n k L =>
              hammingWindowChannelMatrix n k L v lam
                  (a, T) (e.symm i) *
                hammingWindowChannelMatrix n k L v lam
                  (a, T) (e.symm j))
    _ = (if e.symm i = e.symm j then 1 else 0) := hwindow
    _ = (if i = j then 1 else 0) := by
      simp
end MetricCodes.Boolean
