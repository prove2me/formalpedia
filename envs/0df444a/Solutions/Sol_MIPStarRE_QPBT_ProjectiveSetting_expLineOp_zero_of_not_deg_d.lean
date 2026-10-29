-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.expLineOp_zero_of_not_deg_d
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:08:33.131535+00:00
-- url     : https://prove2.me/submissions/360711c4-fb2c-4978-a1d6-41fa7ab48bfb

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.expLineOp_zero_of_not_deg_d.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Projector
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Restriction
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_lineMeas_effect_eq_zero_of_axis
import Theorems.Thm_MIPStarRE_QPBT_polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

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

















/-- On an axis-parallel line, the restriction belongs to the embedded
degree-`d` subspace. This is the coefficient form of the axis assertion in
blueprint `lem:low-degree-encoding-line-restriction`. -/
theorem restrictToLine_lowDegreeEncoding_fitsDegree_of_axis (L : _root_.MIPStarRE.QPBT.LdParams)
    (line : _root_.MIPStarRE.QPBT.LineDesc L) (haxis : line.kind = .axis)
    (h : _root_.MIPStarRE.QPBT.Cube L.m → _root_.MIPStarRE.QPBT.ScalarQ L) :
    (_root_.MIPStarRE.QPBT.restrictToLine L line (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)).FitsDegree L.d := by
  intro i hi
  unfold _root_.MIPStarRE.QPBT.restrictToLine
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  calc
    (_root_.MIPStarRE.QPBT.polynomialOnLine L line (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)).natDegree ≤ 1 :=
      _root_.MIPStarRE.QPBT.polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis L line haxis h
    _ ≤ L.d := L.hd
    _ < i.val := hi

/-! ## Evaluation of the restriction along the line -/











end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/Projector.lean. -/
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

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section















/-- On an axis-parallel line, Pauli line projectors vanish outside the
embedded degree-`d` subspace, because every restricted low-degree encoding has
degree at most `d` there. This is the ancillary half of the last assertion of
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem tauLineProj_eq_zero_of_axis (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) (haxis : line.kind = .axis)
    (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) (hf : ¬ f.FitsDegree P.d) :
    _root_.MIPStarRE.QPBT.tauLineProj P W line f = 0 := by
  classical
  unfold _root_.MIPStarRE.QPBT.tauLineProj
  apply Finset.sum_eq_zero
  intro e he
  exfalso
  apply hf
  rw [← (Finset.mem_filter.mp he).2]
  exact _root_.MIPStarRE.QPBT.restrictToLine_lowDegreeEncoding_fitsDegree_of_axis P.toLdParams line
    haxis e

/-! ## Interaction with the point projectors -/















/-! ## Perfect consistency on an EPR pair -/







end

end MIPStarRE.QPBT

/-!
# Expanded line measurements

This module constructs the expanded line measurements by convolving a strategy
line measurement with the Pauli-register line projectors, and records that the
result is a projective measurement whose effects vanish, on an axis-parallel
line, outside the embedded degree-`d` outcome space. It also introduces the
fine strategy--Pauli product measurement of which the expanded line
measurement is the addition postprocessing, and the evaluation-class and
point-effect families used by the consistency estimates.

## References

The declarations formalize `def:expanded-line-measurement`, whose paper
source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:552-556`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum









open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (haxis : line.kind = .axis) (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d))
    (hf : ¬ f.FitsDegree P.d) :
    S.expLineOp side W line f = 0 := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.expLineOp
  apply Finset.sum_eq_zero
  intro pair hpair
  have hsum : pair.1 + pair.2 = f := (Finset.mem_filter.mp hpair).2
  by_cases h1 : pair.1.FitsDegree P.d
  · have h2 : ¬ pair.2.FitsDegree P.d := by
      intro h2
      apply hf
      intro i hi
      rw [← hsum, Pi.add_apply, h1 i hi, h2 i hi, add_zero]
    rw [_root_.MIPStarRE.QPBT.tauLineProj_eq_zero_of_axis P W line haxis pair.2 h2,
      _root_.MIPStarRE.QPBT.heteroKron_zero_right]
  · rw [S.lineMeas_effect_eq_zero_of_axis side W line haxis pair.1 h1,
      _root_.MIPStarRE.QPBT.heteroKron_zero_left]
