-- Prove2me | solution 1 for MetricCodes.Boolean.hammingSourceChannelCoefficient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/c4818c07-0c95-4695-9db4-abbd97af8099

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    (m i : Fin (L - k + 1)) :
    0 ≤ hammingSourceChannelCoefficient n k L m i := by
  have hm := m.isLt
  have hi := i.isLt
  have hentry : 0 ≤ MetricCodes.hammingJacobiMatrix n k L m i := by
    unfold MetricCodes.hammingJacobiMatrix
    split_ifs with hforward hbackward
    · exact (MetricCodes.hammingJacobiEntry_pos hn
        (by omega) (by omega)).le
    · exact (MetricCodes.hammingJacobiEntry_pos hn
        (by omega) (by omega)).le
    · exact le_rfl
  unfold hammingSourceChannelCoefficient
  exact div_nonneg
    (mul_nonneg hentry (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
end MetricCodes.Boolean
