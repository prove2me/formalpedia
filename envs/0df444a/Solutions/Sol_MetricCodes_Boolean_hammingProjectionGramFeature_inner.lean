-- Prove2me | solution 1 for MetricCodes.Boolean.hammingProjectionGramFeature_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/bce6570b-2782-4c75-9184-9d5ebbcdf1f6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingAxis_inner
import Theorems.Thm_MetricCodes_Boolean_hammingChannelMatrix_transpose_mul
import Theorems.Thm_MetricCodes_Boolean_hammingChannelMatrix_transpose_axis_projection

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
    (x y : BinaryWord n) :
    @inner ℝ
      (EuclideanSpace ℝ
        ((Fin n × Fin (hammingWindowDimension n k L)) ×
          Fin (hammingWindowDimension n k L))) _
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam x)
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam y) =
      (MetricCodes.hammingCorrelation x y - lam) *
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).overlap x y := by
  have hgram := matrixAxisResidual_gram
    (hammingProjectionFamily hk hkL hLn
      v hunit (fun i => (hv i).le))
    (fun (z : BinaryWord n) (a : Fin n) => hammingAxis z a)
    (hammingChannelMatrix n k L v lam)
    (Real.sqrt lam) lam
    (hammingChannelMatrix_transpose_mul
      hn hkL hLn v hv lam hlam heigen)
    (fun z => hammingChannelMatrix_transpose_axis_projection
      hn hk hkL hLn v hunit hv lam hlam heigen z)
    (Real.sq_sqrt hlam.le) x y
  change
    @inner ℝ
      (EuclideanSpace ℝ
        ((Fin n × Fin (hammingWindowDimension n k L)) ×
          Fin (hammingWindowDimension n k L))) _
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam x)
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam y) =
      (MetricCodes.hammingCorrelation x y - lam) *
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).overlap x y
  have haxis' :
      (∑ a : Fin n, hammingAxis x a * hammingAxis y a) =
        MetricCodes.hammingCorrelation x y := by
    simpa only [PiLp.inner_apply, Real.inner_apply, mul_comm] using
      hammingAxis_inner hn x y
  change
    @inner ℝ
      (EuclideanSpace ℝ
        ((Fin n × Fin (hammingWindowDimension n k L)) ×
          Fin (hammingWindowDimension n k L))) _
      (matrixAxisGramFeature
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le))
        (fun (z : BinaryWord n) (a : Fin n) => hammingAxis z a)
        (hammingChannelMatrix n k L v lam)
        (Real.sqrt lam) x)
      (matrixAxisGramFeature
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le))
        (fun (z : BinaryWord n) (a : Fin n) => hammingAxis z a)
        (hammingChannelMatrix n k L v lam)
        (Real.sqrt lam) y) = _
  rw [← haxis']
  exact hgram
end MetricCodes.Boolean
