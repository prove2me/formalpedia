-- Prove2me | solution 1 for MIPStarRE.QPBT.extendedDirectLd_coefficientCollisionLoss_le_five_mul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T20:57:53.542737+00:00
-- url     : https://prove2.me/submissions/d543e8e3-f996-4497-a2ac-3c0ef28a2936

-- Generated proof for MIPStarRE.QPBT.extendedDirectLd_coefficientCollisionLoss_le_five_mul.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Extended direct coefficient-collision loss

This module compares the sum of the axis and diagonal coefficient-collision
losses at the extended directly indexed parameters with the original `m*d/q`
ratio.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603`
-/



open MIPStarRE.QPBT

theorem solution
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    ((P.extendedDirectLd.d : ℝ) +
        (P.extendedDirectLd.m * P.extendedDirectLd.d : ℝ)) /
        (P.extendedDirectLd.q : ℝ) ≤
      5 * ((P.m * P.d : ℝ) / (P.q : ℝ)) := by
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by
    exact_mod_cast P.one_le_m
  have hqNat : 0 < P.q := by
    rcases P.hq with ⟨k, _, hk⟩
    rw [hk]
    exact Nat.pow_pos (by decide)
  have hq : (0 : ℝ) < (P.q : ℝ) := by
    exact_mod_cast hqNat
  change ((P.d : ℝ) + ((2 * P.m + 2 : ℕ) : ℝ) * (P.d : ℝ)) /
      (P.q : ℝ) ≤ 5 * ((P.m : ℝ) * (P.d : ℝ) / (P.q : ℝ))
  push_cast
  rw [show 5 * ((P.m : ℝ) * (P.d : ℝ) / (P.q : ℝ)) =
    (5 * ((P.m : ℝ) * (P.d : ℝ))) / (P.q : ℝ) by ring]
  apply (div_le_div_iff_of_pos_right hq).2
  nlinarith [show (0 : ℝ) ≤ (P.d : ℝ) by positivity]
