-- Prove2me | solution 1 for MIPStarRE.QPBT.ldStrategyToDirect_pointPolynomial_compression
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:58:14.689044+00:00
-- url     : https://prove2.me/submissions/48a58290-ba9f-4504-84be-1353d158a86c

-- Generated proof for MIPStarRE.QPBT.ldStrategyToDirect_pointPolynomial_compression.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_Compression
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_Measurements
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_SeedFiber
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Upstream
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_blockDiagonalMeasurement_postprocess
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_seedFiber_compress_right

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Consistency/Measurements.lean. -/
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

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Polynomial outcomes -/











/-! ## Complete measurements -/



















/-! ## Correlated-ancilla compression -/

/-!
The diagonal-block conditional expectation preserves either mixed defect
exactly because the point measurement on the opposite carrier is constant on
the residue register.  It does not yield a global/global compression theorem:
the lifted state pairs equal residues, whereas separately compressing both
polynomial measurements produces an independent double average over residues.
Neither quantity bounds the other in general.  This open obstruction is
recorded in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/







private theorem averageDiagonalBlock_finset_sum
    {alpha iota block : Type*} [Fintype iota] [Fintype block]
    (s : Finset alpha) (A : alpha → _root_.LIDT.MIPStarRE.Quantum.Op (iota × block)) :
    _root_.MIPStarRE.QPBT.averageDiagonalBlock (∑ a ∈ s, A a) =
      ∑ a ∈ s, _root_.MIPStarRE.QPBT.averageDiagonalBlock (A a) := by
  classical
  ext i j
  simp only [_root_.MIPStarRE.QPBT.averageDiagonalBlock, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.submatrix_apply]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]

/-- Normalized diagonal-block compression commutes with deterministic outcome
postprocessing. -/
theorem correlatedAncillaCompressMeasurement_postprocess
    {alpha beta iota block : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement alpha (iota × block))
    (f : alpha → beta) :
    _root_.MIPStarRE.QPBT.correlatedAncillaCompressMeasurement (M.postprocess f) =
      (_root_.MIPStarRE.QPBT.correlatedAncillaCompressMeasurement M).postprocess f := by
  classical
  apply _root_.LIDT.MIPStarRE.Quantum.Measurement.ext
  intro b
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
    _root_.MIPStarRE.QPBT.correlatedAncillaCompressMeasurement_effect,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact averageDiagonalBlock_finset_sum
    (Finset.univ.filter (fun a => f a = b)) M.effect





/-- Seed-fiber compression commutes with deterministic outcome
postprocessing. -/
theorem seedFiberCompressMeasurement_postprocess
    (L : _root_.MIPStarRE.QPBT.LdParams) {alpha beta iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement alpha
      (iota × Fin (L.q / L.m))) (f : alpha → beta) :
    _root_.MIPStarRE.QPBT.seedFiberCompressMeasurement L (M.postprocess f) =
      (_root_.MIPStarRE.QPBT.seedFiberCompressMeasurement L M).postprocess f := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact _root_.MIPStarRE.QPBT.correlatedAncillaCompressMeasurement_postprocess M f





/-- Polynomial evaluation commutes exactly with compression of the correlated
seed-residue carrier. -/
theorem seedFiberCompressPolyMeasTuple_evaluation
    (L : _root_.MIPStarRE.QPBT.LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple L.toDirectLdParams
      (iota × Fin (L.q / L.m))) (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) :
    (_root_.MIPStarRE.QPBT.seedFiberCompressPolyMeasTuple L G).postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u) =
      _root_.MIPStarRE.QPBT.seedFiberCompressMeasurement L
        (G.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)) := by
  exact (_root_.MIPStarRE.QPBT.seedFiberCompressMeasurement_postprocess L G
    (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).symm



private theorem matrixMeasurementTransport_eq_postprocess
    {alpha beta iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : _root_.LIDT.MIPStarRE.Quantum.Measurement alpha iota) :
    _root_.MIPStarRE.QPBT.matrixMeasurementTransport e M = M.postprocess e := by
  classical
  apply _root_.LIDT.MIPStarRE.Quantum.Measurement.ext
  intro b
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [Finset.sum_eq_single (e.symm b)]
  · simp
  · intro a haMem ha
    have hea : e a = b := (Finset.mem_filter.mp haMem).2
    exact (ha (e.injective (hea.trans (e.apply_symm_apply b).symm))).elim
  · simp

/-- Relabeling along an outcome equivalence commutes with subsequent
postprocessing. -/
theorem matrixMeasurementTransport_postprocess
    {alpha beta gamma iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype gamma] [DecidableEq gamma]
    [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : _root_.LIDT.MIPStarRE.Quantum.Measurement alpha iota)
    (f : beta → gamma) :
    (_root_.MIPStarRE.QPBT.matrixMeasurementTransport e M).postprocess f =
      M.postprocess (fun a => f (e a)) := by
  rw [matrixMeasurementTransport_eq_postprocess,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Consistency/Compression.lean. -/
/-!
# Correlated-ancilla consistency compression

This module contains the correlated-state identities and the two valid
seed-fiber consistency-defect compression results.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Seed-fiber identities -/





private theorem seedFiberPointMeasurement
    (L : _root_.MIPStarRE.QPBT.LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (M : _root_.MIPStarRE.QPBT.LdQuestion L →
      _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.LdAnswer L) iota)
    (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) :
    (_root_.MIPStarRE.QPBT.blockDiagonalMeasurement fun residue =>
        _root_.MIPStarRE.QPBT.matrixMeasurementTransport (_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L)
          (M (_root_.MIPStarRE.QPBT.seededLdQuestion L
            (_root_.MIPStarRE.QPBT.directLdPointQuestionOf L.toDirectLdParams u) residue))).postprocess
        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero L.toDirectLdParams) =
      _root_.MIPStarRE.QPBT.blockDiagonalMeasurement fun _ =>
        (M (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L) := by
  rw [_root_.MIPStarRE.QPBT.blockDiagonalMeasurement_postprocess]
  apply congrArg _root_.MIPStarRE.QPBT.blockDiagonalMeasurement
  funext residue
  rw [_root_.MIPStarRE.QPBT.matrixMeasurementTransport_postprocess,
    _root_.MIPStarRE.QPBT.seededLdQuestion_directLdPointQuestionOf]
  congr 1
  funext a
  cases a <;> rfl

/-- The point POVM of the correlated-residue extension of the strategy is the
block-diagonal amplification of Alice's original seed-indexed point POVM. -/
theorem ldStrategyToDirect_pointMeasurementA
    (L : _root_.MIPStarRE.QPBT.LdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.ldGame L))
    (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) :
    (((_root_.MIPStarRE.QPBT.ldStrategyToDirect L S).A
        (_root_.MIPStarRE.QPBT.directLdPointQuestionOf L.toDirectLdParams u)).postprocess
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero L.toDirectLdParams)) =
      _root_.MIPStarRE.QPBT.blockDiagonalMeasurement fun _ =>
        (S.A (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L) := by
  change (_root_.MIPStarRE.QPBT.blockDiagonalMeasurement fun residue =>
      _root_.MIPStarRE.QPBT.matrixMeasurementTransport (_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L)
        (S.A (_root_.MIPStarRE.QPBT.seededLdQuestion L
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf L.toDirectLdParams u) residue))).postprocess
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero L.toDirectLdParams) = _
  exact seedFiberPointMeasurement L S.A u



















end

end MIPStarRE.QPBT

/-!
# Correlated-ancilla consistency compression

This module contains the correlated-state identities and the two valid
seed-fiber consistency-defect compression results.

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



/-! ## Seed-fiber identities -/

theorem solution
    (L : _root_.MIPStarRE.QPBT.LdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.ldGame L))
    (GB : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple L.toDirectLdParams
      (S.ιB × Fin (L.q / L.m))) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
        (fun u outcome =>
          _root_.MIPStarRE.QPBT.heteroKron
            ((((_root_.MIPStarRE.QPBT.ldStrategyToDirect L S).A
              (_root_.MIPStarRE.QPBT.directLdPointQuestionOf L.toDirectLdParams u)).postprocess
                (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero L.toDirectLdParams)).effect outcome) 1)
        (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
          ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
        (_root_.MIPStarRE.QPBT.ldStrategyToDirect L S).ψ =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
        (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
          (((S.A (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
            (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect outcome) 1)
        (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
          (((_root_.MIPStarRE.QPBT.seedFiberCompressPolyMeasTuple L GB).postprocess
            (_root_.MIPStarRE.QPBT.evalPolyTupleAt u)).effect outcome)) S.ψ := by
  rw [show (_root_.MIPStarRE.QPBT.ldStrategyToDirect L S).ψ = _root_.MIPStarRE.QPBT.seedFiberLiftedState S L by rfl]
  simp only [_root_.MIPStarRE.QPBT.seedFiberCompressPolyMeasTuple_evaluation,
    _root_.MIPStarRE.QPBT.seedFiberCompressMeasurement_effect]
  convert _root_.MIPStarRE.QPBT.consistencyDefect_seedFiber_compress_right S L
    (X := Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) (alpha := Fin L.k → _root_.MIPStarRE.QPBT.ScalarQ L)
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
    (fun u outcome =>
      ((S.A (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
        (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect outcome)
    (fun u outcome =>
      (GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) using 1
  apply _root_.MIPStarRE.QPBT.consistencyDefect_congr
  · intro u outcome
    rw [_root_.MIPStarRE.QPBT.ldStrategyToDirect_pointMeasurementA, _root_.MIPStarRE.QPBT.blockDiagonalMeasurement_effect]
    congr 2
  · intros
    rfl
