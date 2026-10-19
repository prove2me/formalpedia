-- Prove2me | solution 1 for MetricCodes.Boolean.hammingSourceChannelCoefficient_eq_insertion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/9ccfb8e7-07b3-4488-8f93-bbb7fe07239c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_mul_sqrt_choose
import Theorems.Thm_MetricCodes_Boolean_hammingInsertionChannelSquare_mul_sqrt_choose

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
    (hadjacent : source.val + 1 = target.val) :
    hammingSourceChannelCoefficient n k L source target =
      hammingInsertionChannelSquare n k (k + source.val) := by
  have hs := source.isLt
  have ht := target.isLt
  have hboundary : k + source.val + k < n := by omega
  have hdimension : 0 < (n.choose (k + target.val) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show k + target.val ≤ n by omega)
  have hroot : Real.sqrt (n.choose (k + target.val) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hdimension).ne'
  apply mul_right_cancel₀ hroot
  rw [hammingSourceChannelCoefficient_mul_sqrt_choose
    hkL hLn source target]
  have hdegree : k + target.val = (k + source.val) + 1 := by omega
  simpa [MetricCodes.hammingJacobiMatrix, hadjacent, hdegree] using
    (hammingInsertionChannelSquare_mul_sqrt_choose
      hn (show k ≤ k + source.val by omega) hboundary).symm
end MetricCodes.Boolean
