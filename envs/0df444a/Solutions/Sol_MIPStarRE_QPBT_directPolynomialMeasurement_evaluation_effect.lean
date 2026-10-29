-- Prove2me | solution 1 for MIPStarRE.QPBT.directPolynomialMeasurement_evaluation_effect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:15:21.507652+00:00
-- url     : https://prove2.me/submissions/b034fc9d-fe83-415a-b395-995c4bb09670

-- Generated proof for MIPStarRE.QPBT.directPolynomialMeasurement_evaluation_effect.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_Measurements
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Low-degree consistency transport

This module identifies the low individual degree polynomial outcomes with the
bounded polynomial representatives used by the directly indexed QPBT game.  It
also transports complete measurements and their evaluation postprocessings
without changing either coordinate order or consistency error.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum



/-! ## Polynomial outcomes -/











/-! ## Complete measurements -/

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    letI := D.toLDTFieldModel
    ∀ {iota : Type*} [Fintype iota] [DecidableEq iota]
      (G : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial D.toLDTParameters) iota)
      (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (a : _root_.MIPStarRE.QPBT.DirectScalarQ D),
      ((_root_.MIPStarRE.QPBT.directPolynomialMeasurement D G).postprocess
        (fun g => MvPolynomial.eval u g.1)).effect a =
        (_root_.MIPStarRE.QPBT.ldtMeasurementToMatrixMeasurement
          (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess G
            (fun g => g (_root_.MIPStarRE.QPBT.directPointEquiv D u))).toMeasurement).effect
            (_root_.MIPStarRE.QPBT.directScalarEquiv D a) := by
  letI := D.toLDTFieldModel
  intro iota _ _ G u a
  classical
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [_root_.MIPStarRE.QPBT.ldtMeasurementToMatrixMeasurement_effect,
    _root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess, _root_.LIDT.MIPStarRE.LDT.SubMeas.postprocess_outcome]
  apply Finset.sum_bij (fun g _ => _root_.MIPStarRE.QPBT.directPolyEquivPolynomial D g)
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    simpa only [_root_.MIPStarRE.QPBT.directPolyEquivPolynomial_apply] using
      congrArg (_root_.MIPStarRE.QPBT.directScalarEquiv D) hg
  · intro g₁ _ g₂ _ h
    exact (_root_.MIPStarRE.QPBT.directPolyEquivPolynomial D).injective h
  · intro g hg
    refine ⟨(_root_.MIPStarRE.QPBT.directPolyEquivPolynomial D).symm g, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      have heval := _root_.MIPStarRE.QPBT.directPolyEquivPolynomial_apply D
        ((_root_.MIPStarRE.QPBT.directPolyEquivPolynomial D).symm g) u
      rw [(_root_.MIPStarRE.QPBT.directPolyEquivPolynomial D).apply_symm_apply] at heval
      exact (_root_.MIPStarRE.QPBT.directScalarEquiv D).injective (heval.symm.trans hg)
    · exact (_root_.MIPStarRE.QPBT.directPolyEquivPolynomial D).apply_symm_apply g
  · intro g _
    rw [_root_.MIPStarRE.QPBT.directPolynomialMeasurement_effect]
