-- Prove2me | solution 1 for MIPStarRE.QPBT.pullingMeas_eval_effect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:13:28.994225+00:00
-- url     : https://prove2.me/submissions/ae6949fd-9e38-4bbf-8bc4-47945e2d2764

-- Generated proof for MIPStarRE.QPBT.pullingMeas_eval_effect.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_EncodingSupport
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Extraction_PullingMeasurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Point overlaps for the difference-polynomial measurement

Evaluation of the difference polynomial gives `g(u) - g_h(u)`. Unlike
evaluation after decoding, this formula holds for every polynomial outcome.
The resulting point overlaps are the ones supplied by the global witness.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1495-1545`,
  especially `eq:qld-pulling-2b` and `eq:qld-pulling-12`.
- The point-placement and convolution identities identify these overlaps with
  the two consistency relations of the supplied global measurement.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the extraction obligations of this chapter. These
  identities do not construct the global witness. This module was
  originally filed under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    ((_root_.MIPStarRE.QPBT.pullingMeas w side W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a =
      ∑ g : _root_.MIPStarRE.QPBT.Poly P, _root_.MIPStarRE.QPBT.heteroKron ((w.marginalPoly side W).effect g)
        (_root_.MIPStarRE.QPBT.tauDotProj W (_root_.MIPStarRE.QPBT.indicatorVec u) (_root_.MIPStarRE.QPBT.evalPoly g u - a)) := by
  rw [_root_.MIPStarRE.QPBT.pullingMeas, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
  have heval (outcome : _root_.MIPStarRE.QPBT.Poly P × _root_.MIPStarRE.QPBT.PauliRegister P) :
      _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.pullingPoly outcome) u =
        _root_.MIPStarRE.QPBT.evalPoly outcome.1 u - dotProduct outcome.2 (_root_.MIPStarRE.QPBT.indicatorVec u) := by
    change MvPolynomial.eval u (outcome.1.1 - _root_.MIPStarRE.QPBT.lowDegreeEncoding outcome.2) = _
    rw [MvPolynomial.eval_sub]
    exact congrArg (_root_.MIPStarRE.QPBT.evalPoly outcome.1 u - ·) (_root_.MIPStarRE.QPBT.lowDegreeEnc_eq_dotProduct outcome.2 u)
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter, heval,
    _root_.MIPStarRE.QPBT.tensorMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne, _root_.MIPStarRE.QPBT.pauliRegisterMeas]
  rw [Fintype.sum_prod_type]
  unfold _root_.MIPStarRE.QPBT.tauDotProj _root_.MIPStarRE.QPBT.bracketOp
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro h _
  have hlabel : _root_.MIPStarRE.QPBT.evalPoly g u - dotProduct h (_root_.MIPStarRE.QPBT.indicatorVec u) = a ↔
      dotProduct h (_root_.MIPStarRE.QPBT.indicatorVec u) = _root_.MIPStarRE.QPBT.evalPoly g u - a := by
    constructor <;> intro heq <;> linear_combination -heq
  simp only [hlabel]
