-- Prove2me | solution 1 for MIPStarRE.QPBT.actual_rounding_error_le_root
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T20:54:55.228084+00:00
-- url     : https://prove2.me/submissions/49a7f281-7099-4fc9-b610-8dec9a0df2e8

-- Generated proof for MIPStarRE.QPBT.actual_rounding_error_le_root.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # Absorption of the actual rounded polynomial-pair error

The point and line errors both enter low-degree soundness. The actual
projective rounding then incurs an eighth root. The unit cap is applied only
to the final consistency defect.

## References

Paper `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`.
This module composes the direct passing estimate with square-root closure for
the global error function.
-/



open MIPStarRE.QPBT

theorem solution {delta point ratio t : ℝ}
    (hd : 0 ≤ delta) (hp : 0 ≤ point)
    (hdt : delta ≤ t) (hpt : Real.sqrt point ≤ t) (hrt : ratio ≤ t) :
    min 1 (32 * delta + 32 * Real.sqrt (220 * delta ^ (1 / 4 : ℝ)) +
      64 * Real.sqrt (2 * delta) + 64 * point + 30 * ratio) ≤
      1024 * Real.sqrt (Real.sqrt (Real.sqrt (min 1 t))) := by
  have ht : 0 ≤ t := hd.trans hdt
  by_cases ht1 : t ≤ 1
  · rw [min_eq_right ht1]
    have hroot : Real.sqrt (Real.sqrt (Real.sqrt t)) = t ^ (1 / 8 : ℝ) := by
      simp only [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul ht, ← Real.rpow_mul ht]
      norm_num
    rw [hroot]
    have h18 : t ≤ t ^ (1 / 8 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' ht ht1
        (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1)
    have h14 : t ≤ t ^ (1 / 4 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' ht ht1
        (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
    have hsqrt : Real.sqrt (t ^ (1 / 4 : ℝ)) = t ^ (1 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
      norm_num
    have hround : Real.sqrt (220 * delta ^ (1 / 4 : ℝ)) ≤
        15 * t ^ (1 / 8 : ℝ) := by
      calc
        _ ≤ Real.sqrt (225 * t ^ (1 / 4 : ℝ)) := Real.sqrt_le_sqrt
          (mul_le_mul (by norm_num) (Real.rpow_le_rpow hd hdt (by norm_num))
            (Real.rpow_nonneg hd _) (by norm_num))
        _ = _ := by rw [Real.sqrt_mul (by norm_num), hsqrt]; norm_num
    have hsecond : Real.sqrt (2 * delta) ≤ 2 * t ^ (1 / 8 : ℝ) := by
      calc
        _ ≤ Real.sqrt (4 * t ^ (1 / 4 : ℝ)) :=
          Real.sqrt_le_sqrt (by nlinarith [Real.rpow_nonneg ht (1 / 4 : ℝ)])
        _ = _ := by rw [Real.sqrt_mul (by norm_num), hsqrt]; norm_num
    have hpoint : point ≤ t := by
      nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg point]
    refine (min_le_right _ _).trans ?_
    nlinarith [Real.rpow_nonneg ht (1 / 8 : ℝ)]
  · rw [min_eq_left (le_of_not_ge ht1)]
    norm_num
