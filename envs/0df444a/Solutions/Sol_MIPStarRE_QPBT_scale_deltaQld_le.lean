-- Prove2me | solution 1 for MIPStarRE.QPBT.scale_deltaQld_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T20:54:55.046018+00:00
-- url     : https://prove2.me/submissions/c6480e63-8c87-4cc3-8123-0c1a4604a30b

-- Generated proof for MIPStarRE.QPBT.scale_deltaQld_le.
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
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
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

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {a b epsilon K : ℝ}
    (ha : 1 ≤ a) (he : 0 ≤ epsilon) (hK : 1 ≤ K) :
    K * _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q ≤
      _root_.MIPStarRE.QPBT.deltaQld (K * a) b epsilon P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have haK : a ≤ K * a := le_mul_of_one_le_left (by linarith) hK
  have ha0 : 0 ≤ a := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hsum : 0 ≤ Real.rpow epsilon b + Real.rpow (P.q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((P.m * P.d : ℕ) : ℝ))) :=
    add_nonneg (add_nonneg (Real.rpow_nonneg he _) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by norm_num) _)
  unfold _root_.MIPStarRE.QPBT.deltaQld
  rw [← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hmd haK) (mul_nonneg hK0 ha0)) hsum
