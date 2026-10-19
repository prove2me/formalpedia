-- Prove2me | solution 1 for MetricCodes.Boolean.hammingAdjacentBlockCoefficient_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/b3e06abc-39c1-4583-9d67-d387e6a2c76e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_nonneg
import Theorems.Thm_MetricCodes_Boolean_hammingRecurrenceWeight_pos_of_pos

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
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (target source : Fin (L - k + 1)) :
    hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 =
      hammingSourceChannelCoefficient n k L source target *
        hammingRecurrenceWeight n k L v target /
          (lam * hammingRecurrenceWeight n k L v source) := by
  unfold hammingAdjacentBlockCoefficient
  apply Real.sq_sqrt
  exact div_nonneg
    (mul_nonneg
      (hammingSourceChannelCoefficient_nonneg hn hkL hLn
        source target)
      (hammingRecurrenceWeight_pos_of_pos hkL hLn v hv target).le)
    (mul_pos hlam
      (hammingRecurrenceWeight_pos_of_pos hkL hLn v hv source)).le
end MetricCodes.Boolean
