-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound_source017
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T18:44:56.447832+00:00
-- url     : https://prove2.me/submissions/277ee938-ebac-45b8-b95f-659b876d0465

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_arithmetic_lower_bound

namespace OAI.PiExponent.DeterminantContradiction

open Filter
open scoped Topology

theorem finiteDenominators_two_le {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    2 ≤ finiteDenominators d i := (d.approximations i.val).1

theorem logWeights_eq {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) :=
  (d.x_log i.val).symm

end OAI.PiExponent.DeterminantContradiction

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : FixedData nu)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - d.arithmeticError ≤
      Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : ℝ) * H) := by
  have hh := MatrixArithmetic.selectedMinor_arithmetic_lower_bound
    (finiteNumerators d) (finiteDenominators d) (finiteDenominators_two_le d)
    (Nat.zero_lt_of_lt d.K_pos) d.w0_pos d.v0_pos d.base.theta_pos d.F0_pos.le hH
    d.wstar_pos (fun i => by rw [logWeights_eq]; exact d.wstar_lower i) selection hdet
  simpa only [actualMinor, actualMean, actualRowCount,
    AdmissibleParameters.arithmeticError, logWeights_eq] using hh
