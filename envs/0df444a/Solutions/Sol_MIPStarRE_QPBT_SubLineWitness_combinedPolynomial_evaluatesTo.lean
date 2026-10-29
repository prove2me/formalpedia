-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.combinedPolynomial_evaluatesTo
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:47:23.401267+00:00
-- url     : https://prove2.me/submissions/4c0bafc6-6d68-4219-8c9e-66b4b34deec0

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.combinedPolynomial_evaluatesTo.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Measurement
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_combineLinePoly_spec

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/ExtendedLines/Measurement.lean. -/
/-!
# Conditional extended-line measurements

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

















/-- The selected coordinates satisfy the source's affine line identities. -/
theorem SubLineWitness.affineData_compatible {params : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness params) (sample : _root_.MIPStarRE.QPBT.SubLineTriple params)
    (hsample : sample ∈ sublines.D.support) :
    let data := sublines.affineData sample hsample
    _root_.MIPStarRE.QPBT.IsCombineLineCompatible (_root_.MIPStarRE.QPBT.directPointToPauli params sample.1.base)
      (_root_.MIPStarRE.QPBT.directPointToPauli params sample.1.direction)
      sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
      (data 0) (data 1) (data 2) (data 3) (data 4) (data 5) (data 6) (data 7) :=
  Classical.choose_spec (sublines.exists_affineData sample hsample)









/-- Evaluation commutes with the canonical scalar identification. -/
private theorem evalCoefficient_extendedScalar {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {bound : ℕ}
    (polynomial : _root_.MIPStarRE.QPBT.DirectDegPoly params.extendedDirectLd bound)
    (parameter : _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params (_root_.MIPStarRE.QPBT.evalCoefficient polynomial parameter) =
      _root_.MIPStarRE.QPBT.evalCoefficient (fun index => _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params (polynomial index))
        (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params parameter) := by
  simp [_root_.MIPStarRE.QPBT.evalCoefficient]






















end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineBranch.lean. -/
/-!
# The branch data of the sub-line sampling procedure

The sampling procedure of the sub-line lemma draws a line kind, a stored
extended coordinate, and an unrestricted extended direction, and forms from
them the direction of the extended line: the elementary direction at the
stored coordinate in the axis branch, and the extended direction with the
coordinates preceding the stored coordinate replaced by zero in the diagonal
branch.  The two source lines are then read off the two coordinate blocks.
This module fixes the coordinate index that each source line must carry: the
stored coordinate itself when it belongs to that block, the first coordinate
otherwise.  With that choice the source block of the extended direction always
lies in the line spanned by the corresponding source direction, which is the
incidence hypothesis of the two projection lemmas.  The module also records
that moving an extended point to its canonical representative does not change
the canonical representative of either of its source blocks.

## References

The statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate blocks are those of `def:combine-map`, blueprint lines
445--480, paper lines 970--989; the prefix truncation is that of
blueprint `def:ld-question-distribution`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The three ranges of extended coordinates -/



/-! ## Linearity of the identification of the two scalar fields -/

/-- The identification of the two scalar fields is additive on extended
points.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem directPointToPauli_add (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (u v : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directPointToPauli P (u + v) =
      _root_.MIPStarRE.QPBT.directPointToPauli P u + _root_.MIPStarRE.QPBT.directPointToPauli P v := by
  funext i
  change _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (u i + v i) =
    _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (u i) + _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (v i)
  rw [map_add]

/-- The identification of the two scalar fields carries a scalar multiple of
an extended point to the multiple by the identified scalar.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem directPointToPauli_smul (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (t : _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
    (u : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directPointToPauli P (t • u) =
      _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P t • _root_.MIPStarRE.QPBT.directPointToPauli P u := by
  funext i
  change _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (t * u i) =
    _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P t * _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (u i)
  rw [map_mul]

/-! ## The coordinate index carried by each source line -/























/-! ## The two directions of a branch -/





/-! ## Incidence of the two source blocks of a branch direction -/





/-! ## Canonical representatives of the two source blocks -/





end

end MIPStarRE.QPBT

/-!
# Conditional extended-line measurements

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

theorem solution {params : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness params) (sample : _root_.MIPStarRE.QPBT.SubLineTriple params)
    (hsample : sample ∈ sublines.D.support)
    (polynomials : _root_.MIPStarRE.QPBT.DegPoly params.toLdParams (params.m * params.d) ×
      _root_.MIPStarRE.QPBT.DegPoly params.toLdParams (params.m * params.d))
    (point : Fin params.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd)
    (hpoint : point ∈ sample.1.pointSet) (valueX valueZ : _root_.MIPStarRE.QPBT.PauliScalar params)
    (hevalX : _root_.MIPStarRE.QPBT.EvaluatesTo sample.2.1 polynomials.1
      (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli params point)) valueX)
    (hevalZ : _root_.MIPStarRE.QPBT.EvaluatesTo sample.2.2 polynomials.2
      (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli params point)) valueZ) :
    _root_.MIPStarRE.QPBT.DirectEvaluatesTo sample.1 (sublines.combinedPolynomial sample hsample polynomials) point
      ((_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params).symm
        ((_root_.MIPStarRE.QPBT.directPointToPauli params point) (_root_.MIPStarRE.QPBT.alphaVar params.m) * valueX +
          (_root_.MIPStarRE.QPBT.directPointToPauli params point) (_root_.MIPStarRE.QPBT.betaVar params.m) * valueZ)) := by
  obtain ⟨initialParameter, hinitial⟩ := hpoint
  refine ⟨⟨initialParameter, hinitial⟩, ?_⟩
  intro parameter hparameter
  let data := sublines.affineData sample hsample
  have hcompat := sublines.affineData_compatible sample hsample
  have hformula := _root_.MIPStarRE.QPBT.combineLinePoly_spec
    (_root_.MIPStarRE.QPBT.directPointToPauli params sample.1.base) (_root_.MIPStarRE.QPBT.directPointToPauli params sample.1.direction)
    sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
    (data 0) (data 1) (data 2) (data 3) (data 4) (data 5) (data 6) (data 7)
    polynomials.1 polynomials.2 hcompat (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params parameter)
  have hpointTransport : _root_.MIPStarRE.QPBT.directPointToPauli params point =
      _root_.MIPStarRE.QPBT.directPointToPauli params sample.1.base +
        _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params parameter •
          _root_.MIPStarRE.QPBT.directPointToPauli params sample.1.direction := by
    rw [hparameter, _root_.MIPStarRE.QPBT.directPointToPauli_add, _root_.MIPStarRE.QPBT.directPointToPauli_smul]
  have hvalueX := hevalX.2 _ (hpointTransport ▸ hformula.1)
  have hvalueZ := hevalZ.2 _ (hpointTransport ▸ hformula.2.1)
  apply (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params).injective
  rw [evalCoefficient_extendedScalar, RingEquiv.apply_symm_apply]
  simp only [_root_.MIPStarRE.QPBT.SubLineWitness.combinedPolynomial, RingEquiv.apply_symm_apply]
  rw [hformula.2.2]
  erw [hvalueX, hvalueZ]
  rw [hpointTransport]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hcompat.1, hcompat.2.1, hcompat.2.2.1, hcompat.2.2.2.1]
