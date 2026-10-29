-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.placeSide_extracted
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:24:57.505211+00:00
-- url     : https://prove2.me/submissions/92faa1cf-d55b-4277-a81a-07448179cf90

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.placeSide_extracted.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Total Pauli measurements under the extraction swaps

The evaluated overlap on the swapped state is the original evaluated-Pauli
consistency overlap. Both player orientations retain their six-register
placements. These identities instantiate the ideal-state Pauli comparison.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1785-1858`,
especially `eq:qld-unitary-6` and `eq:qld-unitary-9`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement





open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)

theorem solution (side : _root_.MIPStarRE.QPBT.PlayerSide) (T : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) :
    S.placeSide side (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace side)) T) =
      S.placeExtractedRegister side T := by
  cases side
  · ext row col
    change
      ((if (row.1.1, row.1.2.1) = (col.1.1, col.1.2.1) then (1 : ℂ) else 0) *
        T row.1.2.2 col.1.2.2) *
        (if ((row.2.1, row.2.2.1), row.2.2.2) =
          ((col.2.1, col.2.2.1), col.2.2.2) then 1 else 0) =
      (if row.1.1 = col.1.1 then 1 else 0) *
        (if row.1.2.1 = col.1.2.1 then 1 else 0) *
        ((if row.2.1 = col.2.1 then 1 else 0) * T row.1.2.2 col.1.2.2) *
        (if row.2.2.1 = col.2.2.1 then 1 else 0) *
        (if row.2.2.2 = col.2.2.2 then 1 else 0)
    simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, one_mul, mul_one,
      zero_mul, mul_zero]
    split_ifs <;> rfl
  · ext row col
    change
      (if ((row.1.1, row.1.2.1), row.1.2.2) =
        ((col.1.1, col.1.2.1), col.1.2.2) then (1 : ℂ) else 0) *
        ((if (row.2.1, row.2.2.1) = (col.2.1, col.2.2.1) then 1 else 0) *
          T row.2.2.2 col.2.2.2) =
      ((if row.1.1 = col.1.1 then 1 else 0) * T row.2.2.2 col.2.2.2) *
        (if row.1.2.1 = col.1.2.1 then 1 else 0) *
        (if row.1.2.2 = col.1.2.2 then 1 else 0) *
        (if row.2.1 = col.2.1 then 1 else 0) *
        (if row.2.2.1 = col.2.2.1 then 1 else 0)
    simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, one_mul, mul_one,
      zero_mul, mul_zero]
    split_ifs <;> rfl
