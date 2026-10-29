-- Prove2me | solution 1 for MIPStarRE.QPBT.opDistSq_conjBy_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:28:35.27392+00:00
-- url     : https://prove2.me/submissions/9823547c-cf6b-46d6-ae6b-d01bb5662db2

-- Generated proof for MIPStarRE.QPBT.opDistSq_conjBy_apply_eq.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
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

/-!
# Observable consistency after the concrete swaps

Unitary conjugation transports the supplied-witness observable estimate to
the canonical Pauli operators on the extracted registers. This is the input
to the EPR correlation argument, before projection and normalization.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1701-1724`.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum LIDT.MIPStarRE.LDT MIPStarRE.QPBT.DistanceCalculus

theorem solution {X I : Type} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I] (mu : _root_.LIDT.MIPStarRE.LDT.Distribution X) (U : _root_.LIDT.MIPStarRE.Quantum.Op I)
    (hU : Uᴴ * U = 1) (A B : X → _root_.LIDT.MIPStarRE.Quantum.Op I) (psi : EuclideanSpace ℂ I) :
    _root_.MIPStarRE.QPBT.opDistSq mu (fun x => _root_.MIPStarRE.QPBT.conjBy U (A x)) (fun x => _root_.MIPStarRE.QPBT.conjBy U (B x))
      (_root_.MIPStarRE.QPBT.applyOperatorToState U psi) = _root_.MIPStarRE.QPBT.opDistSq mu A B psi := by
  have hterm (M N : _root_.LIDT.MIPStarRE.Quantum.Op I) : (_root_.MIPStarRE.QPBT.conjBy U M - _root_.MIPStarRE.QPBT.conjBy U N) * U = U * (M - N) := by
    simp only [_root_.MIPStarRE.QPBT.conjBy]
    calc
      _ = U * (M - N) * (Uᴴ * U) := by noncomm_ring
      _ = _ := by rw [hU, Matrix.mul_one]
  unfold _root_.MIPStarRE.QPBT.opDistSq _root_.MIPStarRE.QPBT.opFamilyDistSq
  simp only [Fintype.sum_unique]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, hterm,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hU]
