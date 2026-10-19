-- Prove2me | solution 1 for MetricCodes.Hamming.finite_codeNumber_bound_of_projection_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/850a8e37-5526-4e46-ba24-b666d49aa284

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_codeNumber_real_le_of_forall
import Theorems.Thm_MetricCodes_Hamming_finite_bound_of_projection_gram

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
    (P : MetricCodes.ProjectionFamily (BinaryWord n)
      (ambientDimension n k L) (MetricCodes.hammingFibreDimension n k))
    (q : BinaryWord n → E)
    (hrank : 0 < MetricCodes.hammingFibreDimension n k)
    (hgap : threshold n d < topEigenvalue n k L)
    (hgram : ∀ x y : BinaryWord n,
      ⟪q x, q y⟫_ℝ =
        (MetricCodes.hammingCorrelation x y - topEigenvalue n k L) *
          P.overlap x y) :
    (codeNumber n d : ℝ) ≤
      ((1 - threshold n d) /
        (topEigenvalue n k L - threshold n d)) *
        ((ambientDimension n k L : ℝ) /
          (MetricCodes.hammingFibreDimension n k : ℝ)) := by
  apply codeNumber_real_le_of_forall
  intro C hC
  apply finite_bound_of_projection_gram hn hd C hC P q hrank hgap
  intro x hx y hy
  exact hgram x y
end MetricCodes.Hamming
