-- Prove2me | solution 1 for MIPStarRE.QPBT.combinedPairSubmeasurement_missing
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:55:47.152355+00:00
-- url     : https://prove2.me/submissions/75f61012-145e-4d2f-a82e-7250f7524130

-- Generated proof for MIPStarRE.QPBT.combinedPairSubmeasurement_missing.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_PairCompletion
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Restricting and completing global polynomial-pair measurements

The combining map embeds pairs of bounded individual-degree polynomials into
extended polynomials. Restricting a measurement along this embedding produces a
submeasurement whose missing operator is the sum of the noncombined effects.
Relabeling those effects by one specified pair completes the measurement and
preserves projectivity.

These algebraic constructions do not establish the concentration estimate
`eq:qld-g-non-separable` or the point consistency required by
`exists_globalPairWitness`; those are separate quantitative obligations.

## References

- Blueprint `lem:qld-4-7`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`,
  `eq:qld-sgg-completeness` and the final completion paragraph.
-/



open MIPStarRE.QPBT

open scoped BigOperators MatrixOrder

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : _root_.LIDT.MIPStarRE.Quantum.Measurement
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (_root_.MIPStarRE.QPBT.PauliScalar P) P.d) carrier) :
    1 - (_root_.MIPStarRE.QPBT.combinedPairSubmeasurement P measurement).total =
      ∑ polynomial ∈ Finset.univ.filter
        (fun polynomial => polynomial ∉ Set.range (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P)),
        measurement.effect polynomial := by
  classical
  have htotal : (_root_.MIPStarRE.QPBT.combinedPairSubmeasurement P measurement).total =
      ∑ polynomial ∈ Finset.univ.filter
        (fun polynomial => polynomial ∈ Set.range (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P)),
        measurement.effect polynomial := by
    change (∑ pair, measurement.effect (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P pair)) = _
    rw [← Finset.sum_image (fun first _ second _ heq =>
      (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P).injective heq)]
    congr 1
    ext polynomial
    simp
  rw [htotal, ← measurement.sum_eq_one]
  apply sub_eq_iff_eq_add.mpr
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun polynomial => polynomial ∈ Set.range (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P))
    measurement.effect).symm.trans (add_comm _ _)
