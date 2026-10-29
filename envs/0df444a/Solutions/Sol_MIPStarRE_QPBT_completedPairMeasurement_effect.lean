-- Prove2me | solution 1 for MIPStarRE.QPBT.completedPairMeasurement_effect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:59:22.389993+00:00
-- url     : https://prove2.me/submissions/4783152e-b738-4ed0-b572-b491908641d4

-- Generated proof for MIPStarRE.QPBT.completedPairMeasurement_effect.
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
import Theorems.Thm_MIPStarRE_QPBT_combinedPairSubmeasurement_missing

namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/PairCompletion.lean. -/
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

@[expose] public section

namespace MIPStarRE.QPBT

open scoped BigOperators MatrixOrder

noncomputable section





















/-- All outcomes outside the combining map's range go to the completion pair. -/
theorem completedPairLabel_of_not_mem_range (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (completionPair : _root_.MIPStarRE.QPBT.PolyPair P)
    (polynomial : _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (_root_.MIPStarRE.QPBT.PauliScalar P) P.d)
    (houtside : polynomial ∉ Set.range (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P)) :
    _root_.MIPStarRE.QPBT.completedPairLabel P completionPair polynomial = completionPair := by
  exact Function.extend_apply' _ _ _ houtside







open LIDT.MIPStarRE.Quantum DistanceCalculus





end

end MIPStarRE.QPBT

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
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (_root_.MIPStarRE.QPBT.PauliScalar P) P.d) carrier)
    (completionPair pair : _root_.MIPStarRE.QPBT.PolyPair P) :
    (_root_.MIPStarRE.QPBT.completedPairMeasurement P measurement completionPair).effect pair =
      (_root_.MIPStarRE.QPBT.combinedPairSubmeasurement P measurement).effect pair +
        if pair = completionPair then 1 - (_root_.MIPStarRE.QPBT.combinedPairSubmeasurement P measurement).total
        else 0 := by
  classical
  rw [_root_.MIPStarRE.QPBT.completedPairMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun polynomial => polynomial ∈ Set.range (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P))]
  have hgood :
      Finset.univ.filter (fun polynomial => polynomial ∈ Set.range (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P)) =
        Finset.univ.image (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P) := by
    ext polynomial
    simp
  rw [hgood, Finset.sum_image (fun first _ second _ heq =>
    (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P).injective heq)]
  simp only [_root_.MIPStarRE.QPBT.completedPairLabel_combinedPolyEmbedding]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ pair)]
  congr 1
  have hbad :
      (∑ polynomial ∈ Finset.univ.filter
        (fun polynomial => polynomial ∉ Set.range (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P)),
        if _root_.MIPStarRE.QPBT.completedPairLabel P completionPair polynomial = pair then
          measurement.effect polynomial else 0) =
      ∑ polynomial ∈ Finset.univ.filter
        (fun polynomial => polynomial ∉ Set.range (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P)),
        if completionPair = pair then measurement.effect polynomial else 0 := by
    apply Finset.sum_congr rfl
    intro polynomial hpolynomial
    rw [_root_.MIPStarRE.QPBT.completedPairLabel_of_not_mem_range P completionPair polynomial
      (Finset.mem_filter.mp hpolynomial).2]
  rw [hbad]
  by_cases heq : pair = completionPair
  · simp [heq, _root_.MIPStarRE.QPBT.combinedPairSubmeasurement_missing]
  · simp [heq, Ne.symm heq]
