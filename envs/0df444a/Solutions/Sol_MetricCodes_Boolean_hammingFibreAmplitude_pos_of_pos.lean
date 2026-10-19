-- Prove2me | solution 1 for MetricCodes.Boolean.hammingFibreAmplitude_pos_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/2fd94f45-48c3-42c7-a86d-90b420c9df83

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
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
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (i : Fin (L - k + 1)) :
    0 < hammingFibreAmplitude n k L v i := by
  unfold hammingFibreAmplitude
  apply Real.sqrt_pos.mpr
  exact div_pos
    (hammingRecurrenceWeight_pos_of_pos hkL hLn v hv i)
    (hammingRecurrenceNormalization_pos hkL hLn v hunit
      (fun j => (hv j).le))
end MetricCodes.Boolean
