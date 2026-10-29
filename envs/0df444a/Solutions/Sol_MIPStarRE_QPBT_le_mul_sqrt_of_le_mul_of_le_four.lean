-- Prove2me | solution 1 for MIPStarRE.QPBT.le_mul_sqrt_of_le_mul_of_le_four
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:59:25.97364+00:00
-- url     : https://prove2.me/submissions/95f273d7-1366-4508-8d6c-2bcbaf745ee9

-- Generated proof for MIPStarRE.QPBT.le_mul_sqrt_of_le_mul_of_le_four.
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

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Square-root error bounds for placed measurement families

The consistency conclusions of `lem:qld-comm-line-cons` are stated with the
common error `deltaLine ε = √ε`, while the individual estimates of the proof
are linear in `ε` or already of square-root form. This module records the two
elementary facts that convert those estimates into the common form: the
state-dependent distance between two placed complete measurements never
exceeds `4`, and a quantity bounded by both `a * ε` and `4` is bounded by
`(a + 4) * √ε`.

## References

`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-545`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

open MIPStarRE.QPBT.DistanceCalculus

theorem solution {x ε a : ℝ} (ha : 1 ≤ a) (hx0 : 0 ≤ x)
    (hxa : x ≤ a * ε) (hx4 : x ≤ 4) : x ≤ (a + 4) * Real.sqrt ε := by
  have hε : 0 ≤ ε := by
    by_contra hneg
    have hlt : ε < 0 := lt_of_not_ge hneg
    nlinarith
  have hsqrt : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  by_cases hε1 : ε ≤ 1
  · have hle : ε ≤ Real.sqrt ε := by
      rw [Real.le_sqrt hε hε]
      nlinarith
    calc
      x ≤ a * ε := hxa
      _ ≤ a * Real.sqrt ε := mul_le_mul_of_nonneg_left hle (by linarith)
      _ ≤ (a + 4) * Real.sqrt ε := by nlinarith
  · have hone : 1 ≤ Real.sqrt ε :=
      Real.one_le_sqrt.mpr (lt_of_not_ge hε1).le
    calc
      x ≤ 4 := hx4
      _ ≤ 4 * Real.sqrt ε := by nlinarith
      _ ≤ (a + 4) * Real.sqrt ε := by nlinarith
