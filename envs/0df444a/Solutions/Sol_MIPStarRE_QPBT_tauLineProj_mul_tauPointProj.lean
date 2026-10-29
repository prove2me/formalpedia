-- Prove2me | solution 1 for MIPStarRE.QPBT.tauLineProj_mul_tauPointProj
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:04:38.110472+00:00
-- url     : https://prove2.me/submissions/3cad80d6-0adf-4ea2-b180-519ed270397a

-- Generated proof for MIPStarRE.QPBT.tauLineProj_mul_tauPointProj.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Projector
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Restriction
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
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
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/WinImplications/LowDegree.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.instDecidableRel_qPBT
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.linePointFintypeCanonical
/-!
# Low-degree winning implications

This module proves the exact line-point and Pauli-basis consistency bounds.

## References

The line-point and Pauli-basis consistency theorems prove items 2 and 3
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications





































/-- A uniquely determined line evaluation is returned by `evalOpt`. -/
theorem evalOpt_eq_some_of_evaluatesTo {L : _root_.MIPStarRE.QPBT.LdParams} {c : ℕ}
    (line : _root_.MIPStarRE.QPBT.LineDesc L) (f : _root_.MIPStarRE.QPBT.DegPoly L c) (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)
    (a : _root_.MIPStarRE.QPBT.ScalarQ L) (h : _root_.MIPStarRE.QPBT.EvaluatesTo line f u a) :
    _root_.MIPStarRE.QPBT.evalOpt line u f = some a := by
  unfold _root_.MIPStarRE.QPBT.evalOpt
  rw [dif_pos ⟨a, h⟩]
  apply congrArg some
  obtain ⟨t, ht⟩ := h.1
  exact ((Classical.choose_spec ⟨a, h⟩).2 t ht).symm.trans (h.2 t ht)
























































end WinImplications

end

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

/-- A bounded-degree restriction evaluates to the original polynomial at
every point on the line. This is a formalization-only identity for the
evaluation classes in blueprint `def:ideg-deg-polynomials`, paper
`14_analysis_of_the_pauli_basis_test.tex:51-58`. -/
theorem evaluatesTo_restrictToLine (L : _root_.MIPStarRE.QPBT.LdParams) (line : _root_.MIPStarRE.QPBT.LineDesc L)
    (g : MvPolynomial (Fin L.m) (_root_.MIPStarRE.QPBT.ScalarQ L))
    (hg : (_root_.MIPStarRE.QPBT.polynomialOnLine L line g).natDegree ≤ L.m * L.d)
    (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) (hu : u ∈ line.pointSet) :
    _root_.MIPStarRE.QPBT.EvaluatesTo line (_root_.MIPStarRE.QPBT.restrictToLine L line g) u (MvPolynomial.eval u g) := by
  refine ⟨hu, fun t ht => ?_⟩
  rw [_root_.MIPStarRE.QPBT.evalCoefficient_restrictToLine L line g hg, _root_.MIPStarRE.QPBT.eval_polynomialOnLine, ht]

/-- The partial evaluation of a bounded-degree restriction returns the
original polynomial value at a point on the line. This is a
formalization-only identity for the evaluation classes in blueprint
`def:ideg-deg-polynomials`, paper
`14_analysis_of_the_pauli_basis_test.tex:51-58`. -/
theorem evalOpt_restrictToLine (L : _root_.MIPStarRE.QPBT.LdParams) (line : _root_.MIPStarRE.QPBT.LineDesc L)
    (g : MvPolynomial (Fin L.m) (_root_.MIPStarRE.QPBT.ScalarQ L))
    (hg : (_root_.MIPStarRE.QPBT.polynomialOnLine L line g).natDegree ≤ L.m * L.d)
    (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) (hu : u ∈ line.pointSet) :
    _root_.MIPStarRE.QPBT.evalOpt line u (_root_.MIPStarRE.QPBT.restrictToLine L line g) = some (MvPolynomial.eval u g) :=
  _root_.MIPStarRE.QPBT.WinImplications.evalOpt_eq_some_of_evaluatesTo line _ u _
    (_root_.MIPStarRE.QPBT.evaluatesTo_restrictToLine L line g hg u hu)

/-- The restricted encoding evaluates to `g_h(u) = h · ind_m(u)` at every
point on the line. This proves the evaluation assertion in blueprint
`lem:low-degree-encoding-line-restriction`, using equation
`eq:low-degree-encoding-definition`, paper `04_preliminaries.tex:892-896`. -/
theorem evalOpt_restrictToLine_lowDegreeEncoding (L : _root_.MIPStarRE.QPBT.LdParams)
    (line : _root_.MIPStarRE.QPBT.LineDesc L) (h : _root_.MIPStarRE.QPBT.Cube L.m → _root_.MIPStarRE.QPBT.ScalarQ L)
    (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) (hu : u ∈ line.pointSet) :
    _root_.MIPStarRE.QPBT.evalOpt line u (_root_.MIPStarRE.QPBT.restrictToLine L line (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)) =
      some (dotProduct h (_root_.MIPStarRE.QPBT.indicatorVec u)) := by
  rw [_root_.MIPStarRE.QPBT.evalOpt_restrictToLine L line _
    (_root_.MIPStarRE.QPBT.polynomialOnLine_lowDegreeEncoding_natDegree_le L line h) u hu]
  congr 1
  exact _root_.MIPStarRE.QPBT.lowDegreeEnc_eq_dotProduct h u

end

end MIPStarRE.QPBT

/-!
# Pauli-register line projectors

This module constructs the projective measurement `tau^{W,line}` of one
generalized-Pauli register whose outcome is the restriction to a canonical
line of the low-degree encoding of the measured basis label. It records that
the outcome projectors are orthogonal projections summing to the identity,
that they are symmetric matrices (so that they act identically on either half
of an EPR pair), and that on an axis-parallel line they vanish outside the
embedded degree-`d` subspace.

## References

The projectors are `tau^{W,line}_{f''}` of `def:expanded-line-measurement`,
with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:552-556`. Their
perfect self-consistency on an EPR pair is the ancillary input to item 1 of
`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-532`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



















/-! ## Interaction with the point projectors -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (hu : u ∈ line.pointSet) (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d))
    (b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.tauLineProj P W line f * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b =
      if _root_.MIPStarRE.QPBT.evalOpt line u f = some b then _root_.MIPStarRE.QPBT.tauLineProj P W line f else 0 := by
  classical
  unfold _root_.MIPStarRE.QPBT.tauLineProj _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, _root_.MIPStarRE.QPBT.pauliProj_mul_pauliProj]
  calc
    (∑ e ∈ Finset.univ.filter (fun e : _root_.MIPStarRE.QPBT.PauliRegister P =>
        _root_.MIPStarRE.QPBT.restrictToLine P.toLdParams line (_root_.MIPStarRE.QPBT.lowDegreeEncoding e) = f),
        ∑ e' ∈ Finset.univ.filter (fun e' : _root_.MIPStarRE.QPBT.PauliRegister P =>
          dotProduct e' (_root_.MIPStarRE.QPBT.indicatorVec u) = b),
          if e = e' then _root_.MIPStarRE.QPBT.pauliProj W e else 0) =
      ∑ e ∈ Finset.univ.filter (fun e : _root_.MIPStarRE.QPBT.PauliRegister P =>
        _root_.MIPStarRE.QPBT.restrictToLine P.toLdParams line (_root_.MIPStarRE.QPBT.lowDegreeEncoding e) = f),
        if _root_.MIPStarRE.QPBT.evalOpt line u f = some b then _root_.MIPStarRE.QPBT.pauliProj W e else 0 := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Finset.sum_ite_eq]
      have hev := _root_.MIPStarRE.QPBT.evalOpt_restrictToLine_lowDegreeEncoding P.toLdParams line e u hu
      rw [(Finset.mem_filter.mp he).2] at hev
      have hev' : _root_.MIPStarRE.QPBT.evalOpt line u f = some (dotProduct e (_root_.MIPStarRE.QPBT.indicatorVec u)) := hev
      by_cases hb : _root_.MIPStarRE.QPBT.evalOpt line u f = some b
      · rw [if_pos hb, if_pos]
        have hbe : dotProduct e (_root_.MIPStarRE.QPBT.indicatorVec u) = b :=
          Option.some.inj (hev'.symm.trans hb)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbe⟩
      · rw [if_neg hb, if_neg]
        intro hmem
        apply hb
        exact hev'.trans (congrArg some (Finset.mem_filter.mp hmem).2)
    _ = _ := by
      split_ifs <;> simp
