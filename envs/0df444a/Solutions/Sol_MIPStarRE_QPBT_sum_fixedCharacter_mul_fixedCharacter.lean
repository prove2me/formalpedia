-- Prove2me | solution 1 for MIPStarRE.QPBT.sum_fixedCharacter_mul_fixedCharacter
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:03:55.444978+00:00
-- url     : https://prove2.me/submissions/063a5d39-e345-458f-8c29-b0de60a9e4f4

-- Generated proof for MIPStarRE.QPBT.sum_fixedCharacter_mul_fixedCharacter.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_sum_fixedCharacter_mul

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/Points/Commutation.lean. -/
/-!
# Approximate commutation of the field-valued expanded point measurements

The approximate commutation of `lem:qld-comm-cons` is stated for the binary
refinements `M^{(Point,W),u,r}_b` of the expanded point measurements.  The
combined point measurements of `lem:qld-4-10` are built here directly from the
`F_q`-valued measurements `M^{(Point,W),u}_a`, so the commutation estimate is
transferred to them.  The transfer is exact: since
`M^{(Point,X),x}_a = E_r (-1)^{tr(ar)} X^r(x)` and
`M^{(Point,Z),z}_b = E_s (-1)^{tr(bs)} Z^s(z)`, the commutator of the two
measurement effects is the Fourier transform, in the outcome pair `(a, b)`,
of the commutators of the expanded observables, and Parseval's identity for
the additive characters of `F_q` turns the sum over `(a, b)` of the squared
norms into the average over `(r, s)` of the squared norms of the observable
commutators.  No factor depending on `q` is lost.

## Main results

* `sum_norm_sum_smul_sq_of_orthogonal`: Parseval's identity for an orthogonal
  system of coefficients.
* `sum_fixedCharacter_mul`: Fourier cancellation for the fixed trace character.
* `expPoint_comm`: the field-valued expanded point measurements approximately
  commute on every register placement, with the error of
  `lem:qld-comm-cons`.

## References

The commutation estimate for the binary refinements is item 2 of
`lem:qld-comm-cons`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1210`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`; the
Fourier form of the point effects is `def:expanded-point-measurement`, paper
lines 384--418.  The role of the transfer in the proof of `lem:qld-4-10` is
explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section



/-! ## Parseval's identity for an orthogonal system of coefficients -/



/-! ## The fixed trace character -/

section Characters

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams}

/-- The phase induced by the fixed binary trace is an additive character.
Paper `references/qpbt-paper/04_preliminaries.tex:1052-1081`. -/
theorem fixedCharacter_mul (x y : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model x) * _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model y) =
      _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (x + y)) := by
  rw [_root_.MIPStarRE.QPBT.fixedBinTrace, map_add, _root_.MIPStarRE.QPBT.phaseSign_eq_ffChar, _root_.MIPStarRE.QPBT.phaseSign_eq_ffChar,
    _root_.MIPStarRE.QPBT.phaseSign_eq_ffChar]
  exact ((ZMod.stdAddChar (N := 2)).map_add_eq_mul _ _).symm

/-- The fixed trace character is even: negation acts trivially on the binary
trace. -/
theorem fixedCharacter_neg (x : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (-x)) =
      _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model x) := by
  rw [_root_.MIPStarRE.QPBT.fixedBinTrace, map_neg]
  have phaseSign_neg (value : ZMod 2) : _root_.MIPStarRE.QPBT.phaseSign (-value) = _root_.MIPStarRE.QPBT.phaseSign value := by
    exact congrArg _root_.MIPStarRE.QPBT.phaseSign (ZMod.neg_eq_self_mod_two value)
  exact phaseSign_neg _







end Characters

/-! ## Fourier form of the point effects and of their commutator -/





end

end MIPStarRE.QPBT

/-!
# Approximate commutation of the field-valued expanded point measurements

The approximate commutation of `lem:qld-comm-cons` is stated for the binary
refinements `M^{(Point,W),u,r}_b` of the expanded point measurements.  The
combined point measurements of `lem:qld-4-10` are built here directly from the
`F_q`-valued measurements `M^{(Point,W),u}_a`, so the commutation estimate is
transferred to them.  The transfer is exact: since
`M^{(Point,X),x}_a = E_r (-1)^{tr(ar)} X^r(x)` and
`M^{(Point,Z),z}_b = E_s (-1)^{tr(bs)} Z^s(z)`, the commutator of the two
measurement effects is the Fourier transform, in the outcome pair `(a, b)`,
of the commutators of the expanded observables, and Parseval's identity for
the additive characters of `F_q` turns the sum over `(a, b)` of the squared
norms into the average over `(r, s)` of the squared norms of the observable
commutators.  No factor depending on `q` is lost.

## Main results

* `sum_norm_sum_smul_sq_of_orthogonal`: Parseval's identity for an orthogonal
  system of coefficients.
* `sum_fixedCharacter_mul`: Fourier cancellation for the fixed trace character.
* `expPoint_comm`: the field-valued expanded point measurements approximately
  commute on every register placement, with the error of
  `lem:qld-comm-cons`.

## References

The commutation estimate for the binary refinements is item 2 of
`lem:qld-comm-cons`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1210`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`; the
Fourier form of the point effects is `def:expanded-point-measurement`, paper
lines 384--418.  The role of the transfer in the proof of `lem:qld-4-10` is
explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.Preliminaries





/-! ## Parseval's identity for an orthogonal system of coefficients -/



/-! ## The fixed trace character -/



variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams}

theorem solution (r r' : _root_.MIPStarRE.QPBT.PauliScalar P) :
    ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * r)) *
        _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * r')) =
      if r = r' then (Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) : ℂ) else 0 := by
  have hterm : ∀ a : _root_.MIPStarRE.QPBT.PauliScalar P,
      _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * r)) *
          _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * r')) =
        _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * (r' - r))) := by
    intro a
    rw [← _root_.MIPStarRE.QPBT.fixedCharacter_neg (a * r), _root_.MIPStarRE.QPBT.fixedCharacter_mul]
    congr 2
    ring
  simp_rw [hterm, _root_.MIPStarRE.QPBT.sum_fixedCharacter_mul]
  by_cases h : r = r'
  · simp [h]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (sub_eq_zero.mp h').symm
