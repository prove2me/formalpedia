-- Prove2me | solution 1 for MIPStarRE.QPBT.pullingMeas_postprocess_effect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:13:28.891617+00:00
-- url     : https://prove2.me/submissions/5a550ee4-b601-465c-8d2f-1038c81f03c1

-- Generated proof for MIPStarRE.QPBT.pullingMeas_postprocess_effect.
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
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCodeTheorems
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
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Extraction/PullingMeasurement.lean. -/
/-!
# Polynomial outcomes in the pulling argument

The joint measurement of a polynomial marginal and an ideal Pauli register
returns the difference between the polynomial and the encoding of the register.
Decoding this difference gives exactly the pulled-apart measurement. Polynomial
collision estimates apply to these representatives without an encoding-support
restriction on the original marginal.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1530-1605`,
  `eq:qld-pulling-11`, `eq:qld-pulling-12`, and the following symmetry argument.
- `docs/paper-gaps/qpbt_decoding-identity.tex`; only decoder linearity and its
  left-inverse identity are used here.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the `eq:qld-pulling-cons` extraction obligation;
  these
  auxiliary results do not assert it. This module was originally filed
  under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
- The collision estimate compares unequal difference polynomials under uniform
  evaluation.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus
open WinImplications

noncomputable section

open scoped Classical



/-- Decoder linearity identifies the label in `eq:qld-pulling-12`. This uses
`Dec(g_h) = h`, never the reverse identity on arbitrary polynomials. -/
theorem decodeFq_pullingPoly {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (outcome : _root_.MIPStarRE.QPBT.Poly P × _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.decodeFq (_root_.MIPStarRE.QPBT.pullingPoly outcome) = _root_.MIPStarRE.QPBT.decodeFq outcome.1 - outcome.2 := by
  have hsub (g h : _root_.MIPStarRE.QPBT.Poly P) : _root_.MIPStarRE.QPBT.decodeFq (g - h) = _root_.MIPStarRE.QPBT.decodeFq g - _root_.MIPStarRE.QPBT.decodeFq h := by
    funext y
    simp [_root_.MIPStarRE.QPBT.decodeOn, _root_.MIPStarRE.QPBT.decodeAt, _root_.MIPStarRE.QPBT.evalPoly, MvPolynomial.eval_sub]
  rw [_root_.MIPStarRE.QPBT.pullingPoly, hsub, _root_.MIPStarRE.QPBT.decodeFq_lowDegreeEncoding]

















end

end MIPStarRE.QPBT

/-!
# Polynomial outcomes in the pulling argument

The joint measurement of a polynomial marginal and an ideal Pauli register
returns the difference between the polynomial and the encoding of the register.
Decoding this difference gives exactly the pulled-apart measurement. Polynomial
collision estimates apply to these representatives without an encoding-support
restriction on the original marginal.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1530-1605`,
  `eq:qld-pulling-11`, `eq:qld-pulling-12`, and the following symmetry argument.
- `docs/paper-gaps/qpbt_decoding-identity.tex`; only decoder linearity and its
  left-inverse identity are used here.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the `eq:qld-pulling-cons` extraction obligation;
  these
  auxiliary results do not assert it. This module was originally filed
  under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
- The collision estimate compares unequal difference polynomials under uniform
  evaluation.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open MIPStarRE.QPBT.WinImplications



open scoped Classical

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : _root_.MIPStarRE.QPBT.PauliRegister P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    ((_root_.MIPStarRE.QPBT.pullingMeas w side W).postprocess (fun g => dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) u)).effect a =
      _root_.MIPStarRE.QPBT.tildeM w side W u a := by
  classical
  rw [_root_.MIPStarRE.QPBT.pullingMeas, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter,
    _root_.MIPStarRE.QPBT.decodeFq_pullingPoly, _root_.MIPStarRE.QPBT.tensorMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne, _root_.MIPStarRE.QPBT.pauliRegisterMeas]
  rw [Fintype.sum_prod_type]
  unfold _root_.MIPStarRE.QPBT.tildeM _root_.MIPStarRE.QPBT.tauDotProj _root_.MIPStarRE.QPBT.bracketOp
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro h _
  have hlabel : dotProduct (_root_.MIPStarRE.QPBT.decodeFq g - h) u = a ↔
      dotProduct h u = dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) u - a := by
    rw [sub_dotProduct]
    constructor <;> intro heq <;> linear_combination -heq
  simp only [hlabel]
