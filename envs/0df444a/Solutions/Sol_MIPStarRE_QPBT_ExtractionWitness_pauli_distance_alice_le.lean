-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtractionWitness.pauli_distance_alice_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:58:14.080299+00:00
-- url     : https://prove2.me/submissions/7d842ae5-1312-4088-86f4-076f4bf9a771

-- Generated proof for MIPStarRE.QPBT.ExtractionWitness.pauli_distance_alice_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Extraction_Unitary
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Definitions.Def_QPBT_QPBT_Test_Soundness_StateTransfer
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtractionWitness_pauli_distance_alice_le_components

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Operator transfer from supplied extraction data

The complete swap-conjugated measurements intertwine with the local ancilla
isometries. The range-projection estimates then transfer both Pauli families
to the ideal state, with squared error at most four times the extraction error.

## References

Formalization support for the final argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
This conditional construction uses supplied extraction data in a projective
setting; it does not prove blueprint `thm:pauli`. The omitted range projection
is documented in `docs/paper-gaps/qpbt_extraction-transfer.tex` (issue
Dengnifer/MIPStarRE-QPBT-bak#529).
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.MagicSquareRigidity MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement



variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} {w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG}

theorem solution (v : _root_.MIPStarRE.QPBT.ExtractionWitness S w delta)
    (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P S.toStrategy v.toPauliSoundnessWitness W ≤ 4 * delta := by
  calc
    _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P S.toStrategy v.toPauliSoundnessWitness W ≤
        2 * _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (fun (_ : Unit) (h : _root_.MIPStarRE.QPBT.PauliRegister P) =>
            _root_.MIPStarRE.QPBT.conjBy (S.placeSide .alice (_root_.MIPStarRE.QPBT.swapUnitary w .alice))
              (S.placePlayer .alice ((S.pauliMeas .alice W).effect h)))
          (fun (_ : Unit) (h : _root_.MIPStarRE.QPBT.PauliRegister P) =>
            S.placeExtractedRegister .alice (_root_.MIPStarRE.QPBT.pauliProj W h))
          (S.idealExpState v.aux) +
        2 * ‖S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat -
          S.idealExpState v.aux‖ ^ 2 := v.pauli_distance_alice_le_components W
    _ ≤ 2 * delta + 2 * delta := add_le_add
      (mul_le_mul_of_nonneg_left (v.pauli_close .alice W) (by norm_num))
      (mul_le_mul_of_nonneg_left v.state_close (by norm_num))
    _ = 4 * delta := by ring
