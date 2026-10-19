-- Prove2me | solution 1 for MetricCodes.Boolean.hammingSourceChannelCoefficient_mul_sqrt_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/d8e3105a-ad8d-4f23-80d4-edb44c183b43

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
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (m i : Fin (L - k + 1)) :
    hammingSourceChannelCoefficient n k L m i *
        Real.sqrt (n.choose (k + i.val) : ℝ) =
      MetricCodes.hammingJacobiMatrix n k L m i *
        Real.sqrt (n.choose (k + m.val) : ℝ) := by
  have hi := i.isLt
  have hlevel : k + i.val ≤ n := by omega
  have hchoose : 0 < (n.choose (k + i.val) : ℝ) := by
    exact_mod_cast Nat.choose_pos hlevel
  have hsqrt : Real.sqrt (n.choose (k + i.val) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hchoose).ne'
  unfold hammingSourceChannelCoefficient
  field_simp [hsqrt]
end MetricCodes.Boolean
