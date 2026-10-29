-- Prove2me | solution 1 for MIPStarRE.QPBT.honest_dlinePointCondition
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:01:05.551406+00:00
-- url     : https://prove2.me/submissions/7cef695a-de3e-4976-841b-b302d626df90

-- Generated proof for MIPStarRE.QPBT.honest_dlinePointCondition.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Restriction
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_eval_polynomialOnLine
import Theorems.Thm_MIPStarRE_QPBT_polynomialOnLine_lowDegreeEncoding_natDegree_le_sum

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/Restriction.lean. -/
/-!
# Restriction of low-degree encodings to canonical lines

This module substitutes a canonical line into a multivariate polynomial and
records the resulting univariate polynomial as a coefficient list. The
multilinear low-degree encoding has degree at most `m ≤ m*d` on any line and
degree at most `1 ≤ d` on an axis-parallel line. Its coefficient list evaluates
to the original encoding at every point on the line, including a line with
zero direction.

## References

The encoding is equation `eq:ld-encoding` in
`references/qpbt-paper/04_preliminaries.tex:869-896`. Restriction supplies the
line answers in `lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1244-1273`, and the ancillary
line projector in the proof of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. The restriction bounds and
evaluation identities are recorded in blueprint
`lem:low-degree-encoding-line-restriction`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section





/-- Each coordinate of the affine parameterization has degree at most one.
This is a formalization-only auxiliary for the multilinearity argument in
blueprint `lem:low-degree-encoding-line-restriction`. -/
private theorem natDegree_lineCoordinate_le (L : _root_.MIPStarRE.QPBT.LdParams) (line : _root_.MIPStarRE.QPBT.LineDesc L)
    (i : Fin L.m) :
    (_root_.Polynomial.C (line.base i) +
        _root_.Polynomial.X * _root_.Polynomial.C (line.direction i) :
        Polynomial (_root_.MIPStarRE.QPBT.ScalarQ L)).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp
  · refine Polynomial.natDegree_mul_le.trans ?_
    simp





/-- Restricting a multilinear low-degree encoding to a line has degree at most
`m*d`. This is the degree justification in `def:expanded-line-measurement`,
paper `14_analysis_of_the_pauli_basis_test.tex:535-557`, blueprint
`def:expanded-line-measurement`. -/
theorem polynomialOnLine_lowDegreeEncoding_natDegree_le (L : _root_.MIPStarRE.QPBT.LdParams)
    (line : _root_.MIPStarRE.QPBT.LineDesc L) (h : _root_.MIPStarRE.QPBT.Cube L.m → _root_.MIPStarRE.QPBT.ScalarQ L) :
    (_root_.MIPStarRE.QPBT.polynomialOnLine L line (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)).natDegree ≤ L.m * L.d := by
  refine (_root_.MIPStarRE.QPBT.polynomialOnLine_lowDegreeEncoding_natDegree_le_sum L line h
    (fun _ => 1) (fun i => natDegree_lineCoordinate_le L line i)).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]
  exact Nat.le_mul_of_pos_right L.m L.hd







/-! ## Evaluation of the restriction along the line -/



/-- The coefficient-list evaluation agrees with polynomial evaluation when
the restriction has degree at most `m*d`. This is a formalization-only
coefficient identity for blueprint `lem:low-degree-encoding-line-restriction`.
Its degree hypothesis prevents truncation of a general polynomial. -/
theorem evalCoefficient_restrictToLine (L : _root_.MIPStarRE.QPBT.LdParams) (line : _root_.MIPStarRE.QPBT.LineDesc L)
    (g : MvPolynomial (Fin L.m) (_root_.MIPStarRE.QPBT.ScalarQ L))
    (hg : (_root_.MIPStarRE.QPBT.polynomialOnLine L line g).natDegree ≤ L.m * L.d) (t : _root_.MIPStarRE.QPBT.ScalarQ L) :
    _root_.MIPStarRE.QPBT.evalCoefficient (_root_.MIPStarRE.QPBT.restrictToLine L line g) t =
      Polynomial.eval t (_root_.MIPStarRE.QPBT.polynomialOnLine L line g) := by
  unfold _root_.MIPStarRE.QPBT.evalCoefficient _root_.MIPStarRE.QPBT.restrictToLine
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hg) t]
  exact Fin.sum_univ_eq_sum_range
    (fun i => (_root_.MIPStarRE.QPBT.polynomialOnLine L line g).coeff i * t ^ i) (L.m * L.d + 1)







end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/LowDegreeGame.lean. -/
/-!
# The low-degree game

The low-degree component of the Pauli basis test has finite question and answer
alphabets.  Its question maps act explicitly on the point, coordinate, and
direction registers of the ambient coefficient space and have recursive
conditionally linear representations of levels one, two, and three.

## References

The source-facing nodes are blueprint `def:ld-game`,
`def:ld-question-distribution`, and `def:ld-win-predicate`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
The exact decomposition of a scalar seed into its coordinate index and its
residue records the balance assertion for the map `chi` in the same source
definition.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section























/-! ### Formalization-only coordinate-index fibers

The following decomposition supplies the equal-fiber calculation used in the
uniform coordinate-index law.
-/



















/-- Zeroing the coordinates preceding a fixed index is idempotent.  This is a
formalization-only consequence of the prefix restriction in
`def:ld-question-distribution`, recorded as `lem:prefix-projection-idempotent`
in blueprint chapter 13. -/
theorem prefixProjection_idempotent {P : _root_.MIPStarRE.QPBT.LdParams} (i : Fin P.m)
    (v : Fin P.m → _root_.MIPStarRE.QPBT.ScalarQ P) :
    _root_.MIPStarRE.QPBT.prefixProjection i (_root_.MIPStarRE.QPBT.prefixProjection i v) = _root_.MIPStarRE.QPBT.prefixProjection i v := by
  funext j
  by_cases h : j.val < i.val
  · simp only [_root_.MIPStarRE.QPBT.prefixProjection, if_pos h]
  · simp only [_root_.MIPStarRE.QPBT.prefixProjection, if_neg h]









































































end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Completeness/Rejection.lean. -/
/-!
# Rejection of wrong answers by the honest Pauli measurements

This module shows that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily` assigns the zero
operator product to every answer pair rejected by the Pauli win predicate on a
question pair of positive weight for the Pauli question sampler.  Together with
the normalisation of the Born weights this yields the value-one assertion of
`lem:pauli-completeness`.

## References

Blueprint `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1383-1421`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

set_option maxRecDepth 8000

/-! ### Answers of an inadmissible form -/

















/-! ### Coordinate invariants of the typed Pauli conditionally linear maps -/



/-- The point block of a Point/W question is the point block of the ambient
coefficient vector; `def:pauli-question-distribution`. -/
theorem pauliPointBlock_pauliCL_point (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.pauliPointBlock W (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z) = _root_.MIPStarRE.QPBT.pauliPointBlock W z := by
  cases W <;> rfl















/-- The direction of the canonical diagonal-line description of a
Diagonal-line/W question is the direction block carried by that question;
`def:pauli-question-distribution`. -/
theorem dLineDescOf_direction_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    (_root_.MIPStarRE.QPBT.dLineDescOf P.toLdParams
        (_root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z))).direction =
      _root_.MIPStarRE.QPBT.pauliDirectionBlock (_root_.MIPStarRE.QPBT.pauliCL P (.dline W) z) := by
  exact _root_.MIPStarRE.QPBT.prefixProjection_idempotent _ _

/-- The point block of a Diagonal-line/W question is the point coordinate of
the diagonal-line conditionally linear image; `def:pauli-question-distribution`. -/
theorem pauliPointBlock_pauliCL_dline (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.pauliPointBlock W (_root_.MIPStarRE.QPBT.pauliCL P (.dline W) z) =
      (_root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z)).point := by
  cases W <;> rfl

/-- The base of the canonical diagonal-line description of a Diagonal-line/W
question is the point block carried by that question;
`def:pauli-question-distribution`. -/
theorem dLineDescOf_base_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind) (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    (_root_.MIPStarRE.QPBT.dLineDescOf P.toLdParams
        (_root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z))).base =
      _root_.MIPStarRE.QPBT.pauliPointBlock W (_root_.MIPStarRE.QPBT.pauliCL P (.dline W) z) := by
  rw [_root_.MIPStarRE.QPBT.pauliPointBlock_pauliCL_dline]
  change _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed)
        (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed)
          (_root_.MIPStarRE.QPBT.pauliToLd P W z).direction))
        (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed)
          (_root_.MIPStarRE.QPBT.pauliToLd P W z).direction) (_root_.MIPStarRE.QPBT.pauliToLd P W z).point) =
      _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z).seed)
        (_root_.MIPStarRE.QPBT.pauliToLd P W z).direction) (_root_.MIPStarRE.QPBT.pauliToLd P W z).point
  rw [_root_.MIPStarRE.QPBT.prefixProjection_idempotent]
  exact _root_.MIPStarRE.QPBT.lineRepMap_apply_self _ _

/-! ### The honest measurements as coarse-grainings of one Pauli basis -/















/-! ### The consistency clauses along the incidence forms -/





/-! ### Zero products along the incidence forms of the Pauli type graph -/















/-! ### The Pair/W versus Pair incidence form -/





/-! ### The Magic Square incidence forms -/



/-! ### Zero products along the oriented incidence forms -/



end

end MIPStarRE.QPBT

/-!
# Rejection of wrong answers by the honest Pauli measurements

This module shows that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily` assigns the zero
operator product to every answer pair rejected by the Pauli win predicate on a
question pair of positive weight for the Pauli question sampler.  Together with
the normalisation of the Born weights this yields the value-one assertion of
`lem:pauli-completeness`.

## References

Blueprint `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1383-1421`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



set_option maxRecDepth 8000

/-! ### Answers of an inadmissible form -/

















/-! ### Coordinate invariants of the typed Pauli conditionally linear maps -/

























/-! ### The honest measurements as coarse-grainings of one Pauli basis -/















/-! ### The consistency clauses along the incidence forms -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.pauliDlinePointCondition P W (_root_.MIPStarRE.QPBT.pauliCL P (.dline W) z) (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z)
      (_root_.MIPStarRE.QPBT.restrictToLine P.toLdParams
        (_root_.MIPStarRE.QPBT.dLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z)))
        (_root_.MIPStarRE.QPBT.lowDegreeEncoding h))
      (_root_.MIPStarRE.QPBT.lowDegreeEnc h (_root_.MIPStarRE.QPBT.pauliPointBlock W z)) := by
  intro t ht
  rw [_root_.MIPStarRE.QPBT.pauliPointBlock_pauliCL_point] at ht
  have hkey := _root_.MIPStarRE.QPBT.evalCoefficient_restrictToLine P.toLdParams
    (_root_.MIPStarRE.QPBT.dLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z)))
    (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)
    (_root_.MIPStarRE.QPBT.polynomialOnLine_lowDegreeEncoding_natDegree_le P.toLdParams _ h) t
  have hkey2 := _root_.MIPStarRE.QPBT.eval_polynomialOnLine P.toLdParams
    (_root_.MIPStarRE.QPBT.dLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z)))
    (_root_.MIPStarRE.QPBT.lowDegreeEncoding h) t
  rw [_root_.MIPStarRE.QPBT.dLineDescOf_base_eq, _root_.MIPStarRE.QPBT.dLineDescOf_direction_eq] at hkey2
  rw [ht]
  exact hkey.trans hkey2
