-- Prove2me | solution 1 for MetricCodes.Hamming.finite_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/09333ab8-b36f-4e51-8ece-f54eaa2109c5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingProjectionGramFeature_inner
import Theorems.Thm_MetricCodes_Hamming_hammingFibreDimension_pos
import Theorems.Thm_MetricCodes_Hamming_finite_codeNumber_bound_of_projection_gram

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {n k L d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (hkL : k < L) (hLn : L + k ≤ n)
    (hgap : threshold n d < topEigenvalue n k L) :
    (codeNumber n d : ℝ) ≤
      ((1 - threshold n d) /
        (topEigenvalue n k L - threshold n d)) *
        ((ambientDimension n k L : ℝ) /
          (MetricCodes.hammingFibreDimension n k : ℝ)) := by
  have hk : 2 * k ≤ n := by omega
  obtain ⟨v, hunit, heigen, hpositive⟩ :=
    exists_positive_unit_topEigenvector hn hkL.le hLn
  have heigenraw :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        topEigenvalue n k L • v := by
    simpa [operator, matrix] using heigen
  have hlambda : 0 < topEigenvalue n k L :=
    topEigenvalue_pos hn hkL hLn
  let P : MetricCodes.ProjectionFamily (BinaryWord n)
      (ambientDimension n k L) (MetricCodes.hammingFibreDimension n k) :=
    MetricCodes.Boolean.hammingProjectionFamily hk hkL.le hLn
      v hunit (fun i => (hpositive i).le)
  let q := MetricCodes.Boolean.hammingProjectionGramFeature
    hk hkL.le hLn v hunit hpositive (topEigenvalue n k L)
  apply finite_codeNumber_bound_of_projection_gram
    hn hd P q (hammingFibreDimension_pos hk) hgap
  intro x y
  simpa [P, q, ambientDimension, MetricCodes.Boolean.hammingWindowDimension] using
    (MetricCodes.Boolean.hammingProjectionGramFeature_inner
      hn hk hkL.le hLn v hunit hpositive (topEigenvalue n k L)
      hlambda heigenraw x y)
end MetricCodes.Hamming
