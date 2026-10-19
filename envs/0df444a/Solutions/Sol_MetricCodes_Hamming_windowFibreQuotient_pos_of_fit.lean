-- Prove2me | solution 1 for MetricCodes.Hamming.windowFibreQuotient_pos_of_fit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/08185e37-3afa-4eda-8113-5b6489136146

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_hammingFibreDimension_pos
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_dimension
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_half
import Theorems.Thm_MetricCodes_Hamming_choose_le_ambientDimension

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {a b : ℝ} {n : ℕ}
    (ha : a ≤ (1 : ℝ) / 2)
    (hfit : transverseDegree b n ≤ longitudinalDegree a n) :
    0 < windowFibreQuotient a b n := by
  have hhalf := longitudinalDegree_le_half ha n
  have hkhalf : 2 * transverseDegree b n ≤ n := by omega
  have hfibre :
      0 < (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ) := by
    exact_mod_cast hammingFibreDimension_pos hkhalf
  have haone : a ≤ 1 := by linarith
  have hchoose : 0 < (n.choose (longitudinalDegree a n) : ℝ) := by
    exact_mod_cast
      Nat.choose_pos (longitudinalDegree_le_dimension haone n)
  have hambient :
      0 < (ambientDimension n (transverseDegree b n)
        (longitudinalDegree a n) : ℝ) := by
    have hle := choose_le_ambientDimension n
      (transverseDegree b n) (longitudinalDegree a n) hfit
    exact lt_of_lt_of_le hchoose (by exact_mod_cast hle)
  exact div_pos hambient hfibre
end MetricCodes.Hamming
