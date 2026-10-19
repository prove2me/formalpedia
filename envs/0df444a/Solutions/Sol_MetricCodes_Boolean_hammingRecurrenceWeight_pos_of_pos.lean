-- Prove2me | solution 1 for MetricCodes.Boolean.hammingRecurrenceWeight_pos_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/df2c5d72-735b-40e1-ab84-ead65abd8fc2

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
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (i : Fin (L - k + 1)) :
    0 < hammingRecurrenceWeight n k L v i := by
  have hi := i.isLt
  unfold hammingRecurrenceWeight
  apply mul_pos
  · apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (show k + i.val ≤ n by omega)
  · exact hv i
end MetricCodes.Boolean
