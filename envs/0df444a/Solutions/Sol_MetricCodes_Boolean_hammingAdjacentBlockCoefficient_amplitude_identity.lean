-- Prove2me | solution 1 for MetricCodes.Boolean.hammingAdjacentBlockCoefficient_amplitude_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/4bb525ef-4e5b-4cb8-ab18-c1b57f1fd46e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_nonneg
import Theorems.Thm_MetricCodes_Boolean_hammingRecurrenceWeight_pos_of_pos
import Theorems.Thm_MetricCodes_Boolean_hammingFibreAmplitude_pos_of_pos
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
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (target source : Fin (L - k + 1)) :
    hammingAdjacentBlockCoefficient n k L v lam target source *
        hammingFibreAmplitude n k L v target *
        Real.sqrt
          (hammingSourceChannelCoefficient n k L source target) =
      hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 *
        Real.sqrt lam * hammingFibreAmplitude n k L v source := by
  have hcoefficient :=
    hammingSourceChannelCoefficient_nonneg hn hkL hLn source target
  have hsource :=
    hammingRecurrenceWeight_pos_of_pos hkL hLn v hv source
  have hnormal := hammingRecurrenceNormalization_pos
    hkL hLn v hunit (fun i => (hv i).le)
  have hleft :
      0 ≤ hammingAdjacentBlockCoefficient n k L v lam target source *
        hammingFibreAmplitude n k L v target *
        Real.sqrt
          (hammingSourceChannelCoefficient n k L source target) := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (hammingFibreAmplitude_pos_of_pos
          hkL hLn v hunit hv target).le)
      (Real.sqrt_nonneg _)
  have hright :
      0 ≤ hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 *
        Real.sqrt lam * hammingFibreAmplitude n k L v source := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
      (hammingFibreAmplitude_pos_of_pos
        hkL hLn v hunit hv source).le
  have hsquare :
      (hammingAdjacentBlockCoefficient n k L v lam target source *
        hammingFibreAmplitude n k L v target *
        Real.sqrt
          (hammingSourceChannelCoefficient n k L source target)) ^ 2 =
      (hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 *
        Real.sqrt lam * hammingFibreAmplitude n k L v source) ^ 2 := by
    simp only [mul_pow]
    rw [hammingAdjacentBlockCoefficient_sq
      hn hkL hLn v hv lam hlam target source,
      hammingFibreAmplitude_sq
        hkL hLn v hunit (fun i => (hv i).le) target,
      Real.sq_sqrt hcoefficient,
      Real.sq_sqrt hlam.le,
      hammingFibreAmplitude_sq
        hkL hLn v hunit (fun i => (hv i).le) source]
    field_simp [hlam.ne', hsource.ne', hnormal.ne']
  nlinarith
end MetricCodes.Boolean
