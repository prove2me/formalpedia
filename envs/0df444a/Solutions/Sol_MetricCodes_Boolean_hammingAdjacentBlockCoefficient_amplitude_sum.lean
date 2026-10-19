-- Prove2me | solution 1 for MetricCodes.Boolean.hammingAdjacentBlockCoefficient_amplitude_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/609cf2db-3951-4d2c-b179-ece9decc76fe

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingAdjacentBlockCoefficient_sq_sum
import Theorems.Thm_MetricCodes_Boolean_hammingAdjacentBlockCoefficient_amplitude_identity

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
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (source : Fin (L - k + 1)) :
    (∑ target : Fin (L - k + 1),
      hammingAdjacentBlockCoefficient n k L v lam target source *
        hammingFibreAmplitude n k L v target *
        Real.sqrt
          (hammingSourceChannelCoefficient n k L source target)) =
      Real.sqrt lam * hammingFibreAmplitude n k L v source := by
  simp_rw [hammingAdjacentBlockCoefficient_amplitude_identity
    hn hkL hLn v hunit hv lam hlam]
  rw [← Finset.sum_mul, ← Finset.sum_mul,
    hammingAdjacentBlockCoefficient_sq_sum
      hn hkL hLn v hv lam hlam heigen source]
  simp
end MetricCodes.Boolean
