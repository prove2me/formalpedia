-- Prove2me | solution 1 for MetricCodes.Boolean.hammingSourceChannelCoefficient_eq_deletion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/8c06eef6-ade5-4104-b733-9c7dde6ce797

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_mul_sqrt_choose
import Theorems.Thm_MetricCodes_Boolean_hammingDeletionChannelSquare_mul_sqrt_choose

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
    (source target : Fin (L - k + 1))
    (hadjacent : target.val + 1 = source.val) :
    hammingSourceChannelCoefficient n k L source target =
      hammingDeletionChannelSquare n k (k + target.val) := by
  have hs := source.isLt
  have ht := target.isLt
  have hboundary : k + target.val + k < n := by omega
  have hdimension : 0 < (n.choose (k + target.val) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show k + target.val ≤ n by omega)
  have hroot : Real.sqrt (n.choose (k + target.val) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hdimension).ne'
  apply mul_right_cancel₀ hroot
  rw [hammingSourceChannelCoefficient_mul_sqrt_choose
    hkL hLn source target]
  have hnot : source.val + 1 ≠ target.val := by omega
  have hdegree : k + source.val = (k + target.val) + 1 := by omega
  simpa [MetricCodes.hammingJacobiMatrix, hnot, hadjacent, hdegree] using
    (hammingDeletionChannelSquare_mul_sqrt_choose
      hn (show k ≤ k + target.val by omega) hboundary).symm
end MetricCodes.Boolean
