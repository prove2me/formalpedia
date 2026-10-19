-- Prove2me | solution 1 for MetricCodes.Boolean.hammingAdjacentBlockCoefficient_sq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/2c9a5acc-57b7-42f8-b287-252141264446

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingRecurrenceWeight_eigenrecurrence
import Theorems.Thm_MetricCodes_Boolean_hammingRecurrenceWeight_pos_of_pos
import Theorems.Thm_MetricCodes_Boolean_hammingAdjacentBlockCoefficient_sq

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
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (source : Fin (L - k + 1)) :
    (∑ target : Fin (L - k + 1),
      hammingAdjacentBlockCoefficient n k L v lam target source ^ 2) =
      1 := by
  classical
  simp_rw [hammingAdjacentBlockCoefficient_sq
    hn hkL hLn v hv lam hlam]
  rw [← Finset.sum_div,
    hammingRecurrenceWeight_eigenrecurrence
      hkL hLn v lam heigen source]
  exact div_self
    (mul_pos hlam
      (hammingRecurrenceWeight_pos_of_pos hkL hLn v hv source)).ne'
end MetricCodes.Boolean
