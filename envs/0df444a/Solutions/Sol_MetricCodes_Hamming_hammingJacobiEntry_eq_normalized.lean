-- Prove2me | solution 1 for MetricCodes.Hamming.hammingJacobiEntry_eq_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/36c83b4f-38e1-4402-8781-4303f3e44f89

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    (n k i : ℕ) (hn : 0 < n) :
    MetricCodes.hammingJacobiEntry n k i =
      normalizedCoefficient
        ((i : ℝ) / (n : ℝ))
        ((k : ℝ) / (n : ℝ))
        ((1 : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hnreal.ne'
  have hrad :
      (((i : ℝ) + 1) * ((n : ℝ) - (i : ℝ))) =
        (n : ℝ) ^ 2 *
          (((i : ℝ) / (n : ℝ) + (1 : ℝ) / (n : ℝ)) *
            (1 - (i : ℝ) / (n : ℝ))) := by
    field_simp [hnne]

  unfold MetricCodes.hammingJacobiEntry normalizedCoefficient
  rw [hrad, Real.sqrt_mul (sq_nonneg (n : ℝ)),
    Real.sqrt_sq hnreal.le]
  field_simp [hnne]
end MetricCodes.Hamming
