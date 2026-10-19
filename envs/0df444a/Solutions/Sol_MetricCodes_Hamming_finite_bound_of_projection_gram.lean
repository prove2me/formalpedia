-- Prove2me | solution 1 for MetricCodes.Hamming.finite_bound_of_projection_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/fcd61af6-2ac3-4329-8045-ff32b6aade06

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_hammingCorrelation_le_of_dist_le
import Theorems.Thm_MetricCodes_projection_certificate
import Theorems.Thm_MetricCodes_Hamming_threshold_lt_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n k L d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (C : Finset (BinaryWord n)) (hC : MetricCodes.IsBinaryCode d C)
    (P : MetricCodes.ProjectionFamily (BinaryWord n)
      (ambientDimension n k L) (MetricCodes.hammingFibreDimension n k))
    (q : BinaryWord n → E)
    (hrank : 0 < MetricCodes.hammingFibreDimension n k)
    (hgap : threshold n d < topEigenvalue n k L)
    (hgram : ∀ x ∈ C, ∀ y ∈ C,
      ⟪q x, q y⟫_ℝ =
        (MetricCodes.hammingCorrelation x y - topEigenvalue n k L) *
          P.overlap x y) :
    (C.card : ℝ) ≤
      ((1 - threshold n d) /
        (topEigenvalue n k L - threshold n d)) *
        ((ambientDimension n k L : ℝ) /
          (MetricCodes.hammingFibreDimension n k : ℝ)) := by
  refine MetricCodes.projection_certificate P C MetricCodes.hammingCorrelation q
    hrank (threshold_lt_one hn hd) hgap
    (fun x _ => MetricCodes.hammingCorrelation_self x) ?_ hgram
  intro x hx y hy hxy
  exact MetricCodes.hammingCorrelation_le_of_dist_le hn (hC hx hy hxy)
end MetricCodes.Hamming
