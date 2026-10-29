-- Prove2me | solution 1 for MIPStarRE.QPBT.overlap_identity_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:04:38.667045+00:00
-- url     : https://prove2.me/submissions/47516e21-237e-4b2f-a7fd-f5539654c65f

-- Generated proof for MIPStarRE.QPBT.overlap_identity_of_mem.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
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
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective



























/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]































































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Observables/LineMeasurement/LinePointOverlap.lean. -/
/-!
# Overlap of expanded line and expanded point measurements

This module computes the diagonal overlap, on the expanded state, between an
expanded line measurement on one placement and the expanded point effects
selected by evaluation at the sampled point on the opposite placement. Each
product of convolution terms factorizes into a strategy overlap and an EPR
overlap; the EPR overlap of a Pauli line projector with a Pauli point projector
vanishes unless the line polynomial evaluates to the point value, and then
equals the EPR overlap of the line projector alone. Summing over the
convolution fibers identifies the expanded overlap with the overlap of the
strategy's evaluation classes and its completed point measurement. This is the
computation displayed in items 2 and 3 of the expanded-line consistency lemma.

The sections on the linearity of the state quadratic form, on register
placements, and on the completed point measurements collect formalization-only
auxiliaries: the source uses these facts without stating them.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Linearity of the state quadratic form -/

namespace DistanceCalculus

/-- The state quadratic form of the zero operator vanishes. -/
theorem stateQForm_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι) = 0 := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]

end DistanceCalculus



/-! ## The overlap identity -/







end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/Interchange.lean. -/
/-!
# Interchange of the tensor factors in the winning implications

This module collects the statements shared by the operator-distance companions
of the winning implications and by their factor-interchanged forms: transport of
the state-dependent distance along the interchange of the two tensor factors,
the constant-factor passage from consistency to distance, the reversed
verifier edges, and the clause-by-clause symmetry of the Pauli win predicate
on the ordered type pairs that the implications use.

## References

The declarations support the trailing clause of `lem:qld-win-implications` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:616-706`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`,
whose closing sentences at lines 227 and 263-264 state both companions.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Transport of the distance functional along the factor interchange -/

/-- The identity operator acts trivially on a state. Formalization-only support
for blueprint `def:strategy-observables`. -/
theorem applyOperatorToState_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ψ = ψ := by
  ext i
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]















/-! ## Reversed verifier edges

The Pauli type graph is a set of unordered pairs, so every ordered edge used by
the exact implications has its reverse in the graph. The reversed edges carry
the interchanged conclusions of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/













/-! ## Symmetry of the win predicate on the subtests used here

`def:pauli-win-predicate` lists every clause together with its mirror image, so
on each ordered type pair occurring in `lem:qld-win-implications` exchanging the
two questions and the two answers leaves the predicate unchanged. Paper
`08_classical_and_quantum_low_degree_tests.tex:1126-1225`, blueprint
`ch13_qpbt_test.tex:410-449`. -/













/-! ## Numeric bookkeeping -/





end WinImplications

end

end MIPStarRE.QPBT

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

/- Source helpers from QPBT/Observables/ExpandedPlacement.lean. -/
/-!
# Placing operators on the expanded state

The four register placements of `def:symmetric-equivalents` put an operator of
one player's expanded local space on one of the register pairs `AA'`, `BA''`,
`BB'` and `AB''` of the expanded state `psiHat`.  This module records how such
a placement acts on `psiHat`: after the shuffle of `eq:def-psihat` the placed
operator is a threefold tensor product, so a factorized operator whose Pauli
factor is an isometry has the same state-dependent norm as its strategy factor
placed on the original state.  No symmetry between the two players is used;
each of the four placements is treated explicitly.

## References

The declarations support `def:symmetric-equivalents` and `lem:qld-comm-cons`
in `blueprint/src/chapter/ch14_qpbt_observables.tex:1002-1031` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-505`.
-/

@[expose] public section

-- The unshuffled six-register index type of `eq:def-psihat` is a fourfold
-- iterated product; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default.
set_option synthInstance.maxSize 400

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Coordinate tensors -/









/-- The real quadratic form of the identity is the squared vector norm. -/
theorem stateQForm_one_eq_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm u (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) = ‖u‖ ^ 2 := by
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
  rw [_root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_one]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) u)



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/Evaluation.lean. -/
/-!
# Evaluation of line polynomials at a sampled point

This module records the elementary calculus of the partial evaluation
`evalOpt` of a coefficient-list line polynomial at a point: the evaluation of
a sum is the sum of the evaluations whenever both summands evaluate, a summand
of an evaluating sum evaluates whenever the other summand does, the value is
unique, and nothing evaluates at a point off the line. These facts underlie
the manipulation of the evaluation classes in items 2 and 3 of the
expanded-line consistency lemma.

Every declaration below is a formalization-only auxiliary: the source uses
these facts about evaluation without stating them.

## References

The evaluation classes `[eval_u(·) = a]` are `def:ideg-deg-polynomials`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:51-58`. They are
manipulated in `eq:qld-comm-line-pt-cons` and `eq:qld-comm-line-pt-cons2`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

/-- Coefficient-list evaluation is additive in the coefficient list. This
is the additivity behind the convolution of `def:expanded-line-measurement`. -/
theorem evalCoefficient_add {K : Type*} [Semiring K] {n : ℕ} (c d : Fin n → K)
    (t : K) : _root_.MIPStarRE.QPBT.evalCoefficient (c + d) t = _root_.MIPStarRE.QPBT.evalCoefficient c t + _root_.MIPStarRE.QPBT.evalCoefficient d t := by
  unfold _root_.MIPStarRE.QPBT.evalCoefficient
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, add_mul]



/-- The sum of two evaluating line polynomials evaluates to the sum of
their values. This is why the convolution outcome `f = f' + f''` evaluates
whenever both convolution factors do. -/
theorem EvaluatesTo.add {L : _root_.MIPStarRE.QPBT.LdParams} {c : ℕ} {line : _root_.MIPStarRE.QPBT.LineDesc L}
    {f g : _root_.MIPStarRE.QPBT.DegPoly L c} {u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L} {a b : _root_.MIPStarRE.QPBT.ScalarQ L}
    (hf : _root_.MIPStarRE.QPBT.EvaluatesTo line f u a) (hg : _root_.MIPStarRE.QPBT.EvaluatesTo line g u b) :
    _root_.MIPStarRE.QPBT.EvaluatesTo line (f + g) u (a + b) :=
  ⟨hf.1, fun t ht => by rw [_root_.MIPStarRE.QPBT.evalCoefficient_add, hf.2 t ht, hg.2 t ht]⟩

/-- If a sum and its second summand evaluate, the first summand evaluates to
the difference of their values. This is the converse direction used to identify
the convolution fibers of an evaluation class. -/
theorem EvaluatesTo.left_of_add {L : _root_.MIPStarRE.QPBT.LdParams} {c : ℕ} {line : _root_.MIPStarRE.QPBT.LineDesc L}
    {f g : _root_.MIPStarRE.QPBT.DegPoly L c} {u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L} {s b : _root_.MIPStarRE.QPBT.ScalarQ L}
    (hfg : _root_.MIPStarRE.QPBT.EvaluatesTo line (f + g) u s) (hg : _root_.MIPStarRE.QPBT.EvaluatesTo line g u b) :
    _root_.MIPStarRE.QPBT.EvaluatesTo line f u (s - b) :=
  ⟨hfg.1, fun t ht => by
    have h := hfg.2 t ht
    rw [_root_.MIPStarRE.QPBT.evalCoefficient_add, hg.2 t ht] at h
    exact eq_sub_of_add_eq h⟩

/-- The partial evaluation returns `some a` exactly when the polynomial
evaluates to `a`. This is the characterization that makes `evalOpt` the total
form of the evaluation classes of `def:ideg-deg-polynomials`. -/
theorem evalOpt_eq_some_iff {L : _root_.MIPStarRE.QPBT.LdParams} {c : ℕ} (line : _root_.MIPStarRE.QPBT.LineDesc L)
    (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) (f : _root_.MIPStarRE.QPBT.DegPoly L c) (a : _root_.MIPStarRE.QPBT.ScalarQ L) :
    _root_.MIPStarRE.QPBT.evalOpt line u f = some a ↔ _root_.MIPStarRE.QPBT.EvaluatesTo line f u a := by
  constructor
  · intro h
    unfold _root_.MIPStarRE.QPBT.evalOpt at h
    by_cases hex : ∃ a : _root_.MIPStarRE.QPBT.ScalarQ L, _root_.MIPStarRE.QPBT.EvaluatesTo line f u a
    · rw [dif_pos hex, Option.some_inj] at h
      rw [← h]
      exact Classical.choose_spec hex
    · rw [dif_neg hex] at h
      exact absurd h (by simp)
  · exact _root_.MIPStarRE.QPBT.WinImplications.evalOpt_eq_some_of_evaluatesTo line f u a



/-- The partial evaluation of a sum of two evaluating line polynomials is
the sum of their values. -/
theorem evalOpt_add_of_some {L : _root_.MIPStarRE.QPBT.LdParams} {c : ℕ} {line : _root_.MIPStarRE.QPBT.LineDesc L}
    {u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L} {f g : _root_.MIPStarRE.QPBT.DegPoly L c} {a b : _root_.MIPStarRE.QPBT.ScalarQ L}
    (hf : _root_.MIPStarRE.QPBT.evalOpt line u f = some a) (hg : _root_.MIPStarRE.QPBT.evalOpt line u g = some b) :
    _root_.MIPStarRE.QPBT.evalOpt line u (f + g) = some (a + b) :=
  (_root_.MIPStarRE.QPBT.evalOpt_eq_some_iff line u _ _).mpr
    (((_root_.MIPStarRE.QPBT.evalOpt_eq_some_iff line u f a).mp hf).add
      ((_root_.MIPStarRE.QPBT.evalOpt_eq_some_iff line u g b).mp hg))

/-- If a sum and its second summand evaluate, so does the first summand,
with the difference of the two values. -/
theorem evalOpt_left_of_add_some {L : _root_.MIPStarRE.QPBT.LdParams} {c : ℕ} {line : _root_.MIPStarRE.QPBT.LineDesc L}
    {u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L} {f g : _root_.MIPStarRE.QPBT.DegPoly L c} {s b : _root_.MIPStarRE.QPBT.ScalarQ L}
    (hfg : _root_.MIPStarRE.QPBT.evalOpt line u (f + g) = some s) (hg : _root_.MIPStarRE.QPBT.evalOpt line u g = some b) :
    _root_.MIPStarRE.QPBT.evalOpt line u f = some (s - b) :=
  (_root_.MIPStarRE.QPBT.evalOpt_eq_some_iff line u _ _).mpr
    (((_root_.MIPStarRE.QPBT.evalOpt_eq_some_iff line u _ s).mp hfg).left_of_add
      ((_root_.MIPStarRE.QPBT.evalOpt_eq_some_iff line u g b).mp hg))





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

















/-! ## Interaction with the point projectors -/

/-- On a point of the line, Pauli line projectors of non-evaluating
polynomials vanish: every restricted low-degree encoding evaluates there.
Formalization-only auxiliary for items 2 and 3 of `lem:qld-comm-line-cons`,
paper `14_analysis_of_the_pauli_basis_test.tex:534-545`. -/
theorem tauLineProj_eq_zero_of_evalOpt_none (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (hu : u ∈ line.pointSet)
    (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) (hf : _root_.MIPStarRE.QPBT.evalOpt line u f = none) :
    _root_.MIPStarRE.QPBT.tauLineProj P W line f = 0 := by
  classical
  unfold _root_.MIPStarRE.QPBT.tauLineProj
  apply Finset.sum_eq_zero
  intro e he
  exfalso
  have hev := _root_.MIPStarRE.QPBT.evalOpt_restrictToLine_lowDegreeEncoding P.toLdParams line e u hu
  rw [(Finset.mem_filter.mp he).2] at hev
  have hev' : _root_.MIPStarRE.QPBT.evalOpt line u f = some (dotProduct e (_root_.MIPStarRE.QPBT.indicatorVec u)) := hev
  rw [hf] at hev'
  exact absurd hev' (by simp)













/-! ## Perfect consistency on an EPR pair -/



/-- The EPR quadratic forms of the Pauli line projectors on one half sum to
one. Formalization-only auxiliary for the ancillary overlaps in
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:527-545`. -/
theorem sum_stateQForm_eprState_tauLineProj_one (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) :
    ∑ f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
          (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauLineProj P W line f) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) = 1 := by
  rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum,
    ← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left,
    _root_.MIPStarRE.QPBT.sum_tauLineProj_eq_one, _root_.MIPStarRE.QPBT.heteroKron_one_one,
    _root_.MIPStarRE.QPBT.stateQForm_one_eq_norm_sq, _root_.MIPStarRE.QPBT.eprState_norm]
  norm_num



end

end MIPStarRE.QPBT

/-!
# Overlap of expanded line and expanded point measurements

This module computes the diagonal overlap, on the expanded state, between an
expanded line measurement on one placement and the expanded point effects
selected by evaluation at the sampled point on the opposite placement. Each
product of convolution terms factorizes into a strategy overlap and an EPR
overlap; the EPR overlap of a Pauli line projector with a Pauli point projector
vanishes unless the line polynomial evaluates to the point value, and then
equals the EPR overlap of the line projector alone. Summing over the
convolution fibers identifies the expanded overlap with the overlap of the
strategy's evaluation classes and its completed point measurement. This is the
computation displayed in items 2 and 3 of the expanded-line consistency lemma.

The sections on the linearity of the state quadratic form, on register
placements, and on the completed point measurements collect formalization-only
auxiliaries: the source uses these facts without stating them.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



/-! ## Linearity of the state quadratic form -/

open MIPStarRE.QPBT.DistanceCalculus





open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





















/-! ## Effects of the completed measurement families -/















/-! ## Factorization of opposite placements with distinct Pauli factors -/















/-! ## The overlap identity -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    {ιL ιP : Type*} [Fintype ιL] [DecidableEq ιL] [Fintype ιP] [DecidableEq ιP]
    (LM : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) ιL)
    (PM : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams) ιP)
    (Φ : _root_.LIDT.MIPStarRE.Quantum.Op (ιL × _root_.MIPStarRE.QPBT.PauliRegister P) → _root_.LIDT.MIPStarRE.Quantum.Op (ιP × _root_.MIPStarRE.QPBT.PauliRegister P) → ℝ)
    (Ψ : _root_.LIDT.MIPStarRE.Quantum.Op ιL → _root_.LIDT.MIPStarRE.Quantum.Op ιP → ℝ)
    (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) (u : Fin P.m → _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)
    (hu : u ∈ line.pointSet)
    (hΦ0 : ∀ X, Φ X 0 = 0)
    (hΦl : ∀ (s : Finset (_root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) ×
        _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)))
      (X : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) × _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) →
        _root_.LIDT.MIPStarRE.Quantum.Op (ιL × _root_.MIPStarRE.QPBT.PauliRegister P)) (Y : _root_.LIDT.MIPStarRE.Quantum.Op (ιP × _root_.MIPStarRE.QPBT.PauliRegister P)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y)
    (hΦr : ∀ (X : _root_.LIDT.MIPStarRE.Quantum.Op (ιL × _root_.MIPStarRE.QPBT.PauliRegister P))
      (t : Finset (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams × _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams))
      (Y : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams × _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams → _root_.LIDT.MIPStarRE.Quantum.Op (ιP × _root_.MIPStarRE.QPBT.PauliRegister P)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j))
    (hΦfact : ∀ (f' f'' : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) (b' b'' : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams),
      Φ (_root_.MIPStarRE.QPBT.heteroKron (LM.effect f') (_root_.MIPStarRE.QPBT.tauLineProj P W line f''))
          (_root_.MIPStarRE.QPBT.heteroKron (PM.effect b') (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b'')) =
        Ψ (LM.effect f') (PM.effect b') *
          (if _root_.MIPStarRE.QPBT.evalOpt line u f'' = some b'' then
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
              (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauLineProj P W line f'') (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)))
          else 0))
    (hΨl : ∀ (s : Finset (_root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)))
      (A : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) → _root_.LIDT.MIPStarRE.Quantum.Op ιL) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιP),
      Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B)
    (hΨ0 : ∀ A, Ψ A 0 = 0) :
    (∑ f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d),
      Φ (∑ p ∈ Finset.univ.filter
          (fun p : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) ×
            _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2 = f),
          _root_.MIPStarRE.QPBT.heteroKron (LM.effect p.1) (_root_.MIPStarRE.QPBT.tauLineProj P W line p.2))
        ((_root_.MIPStarRE.QPBT.evalOpt line u f).elim 0 (fun a =>
          ∑ q ∈ Finset.univ.filter
            (fun q : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams × _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams => q.1 + q.2 = a),
            _root_.MIPStarRE.QPBT.heteroKron (PM.effect q.1) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u q.2)))) =
      ∑ o : Option (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams),
        Ψ ((LM.postprocess (_root_.MIPStarRE.QPBT.evalOpt line u)).effect o)
          ((PM.postprocess some).effect o) := by
  let c : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) → ℝ := fun f'' =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauLineProj P W line f'') (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)))
  let Pt : Option (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams) → _root_.LIDT.MIPStarRE.Quantum.Op ιP := fun o => (PM.postprocess some).effect o
  have hPt_none : Pt none = 0 := by
    simp only [Pt]
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
    apply Finset.sum_eq_zero
    intro a ha
    exact absurd (Finset.mem_filter.mp ha).2 (by simp)
  have hPt_some (b : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams) : Pt (some b) = PM.effect b := by
    simp only [Pt]
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
    simp [Finset.filter_eq']
  have hc : ∑ f'', c f'' = 1 := _root_.MIPStarRE.QPBT.sum_stateQForm_eprState_tauLineProj_one P W line
  have hc0 : ∀ f'', _root_.MIPStarRE.QPBT.evalOpt line u f'' = none → c f'' = 0 := by
    intro f'' h
    simp only [c]
    rw [_root_.MIPStarRE.QPBT.tauLineProj_eq_zero_of_evalOpt_none P W line u hu f'' h,
      _root_.MIPStarRE.QPBT.heteroKron_zero_left, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_zero]
  have hterm : ∀ (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d))
      (p : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) × _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)),
      p.1 + p.2 = f →
      Φ (_root_.MIPStarRE.QPBT.heteroKron (LM.effect p.1) (_root_.MIPStarRE.QPBT.tauLineProj P W line p.2))
          ((_root_.MIPStarRE.QPBT.evalOpt line u f).elim 0 (fun a =>
            ∑ q ∈ Finset.univ.filter
              (fun q : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams × _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams => q.1 + q.2 = a),
              _root_.MIPStarRE.QPBT.heteroKron (PM.effect q.1) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u q.2))) =
        Ψ (LM.effect p.1) (Pt (_root_.MIPStarRE.QPBT.evalOpt line u p.1)) * c p.2 := by
    intro f p hp
    rcases hf : _root_.MIPStarRE.QPBT.evalOpt line u f with _ | a
    · rw [Option.elim_none, hΦ0]
      rcases h1 : _root_.MIPStarRE.QPBT.evalOpt line u p.1 with _ | a'
      · rw [hPt_none, hΨ0, zero_mul]
      · have h2 : _root_.MIPStarRE.QPBT.evalOpt line u p.2 = none := by
          rcases h2 : _root_.MIPStarRE.QPBT.evalOpt line u p.2 with _ | b
          · rfl
          · exfalso
            have hsum := _root_.MIPStarRE.QPBT.evalOpt_add_of_some h1 h2
            rw [hp, hf] at hsum
            exact absurd hsum (by simp)
        rw [hc0 p.2 h2, mul_zero]
    · rw [Option.elim_some, hΦr]
      simp_rw [hΦfact]
      rcases h2 : _root_.MIPStarRE.QPBT.evalOpt line u p.2 with _ | c''
      · have h1 : _root_.MIPStarRE.QPBT.evalOpt line u p.1 = none := by
          rcases h1 : _root_.MIPStarRE.QPBT.evalOpt line u p.1 with _ | a'
          · rfl
          · exfalso
            have hsum : _root_.MIPStarRE.QPBT.evalOpt line u (p.2 + p.1) = some a := by
              rw [add_comm, hp, hf]
            have h2' := _root_.MIPStarRE.QPBT.evalOpt_left_of_add_some hsum h1
            rw [h2] at h2'
            exact absurd h2' (by simp)
        rw [h1, hPt_none, hΨ0, zero_mul]
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [if_neg (by simp), mul_zero]
      · have hsum : _root_.MIPStarRE.QPBT.evalOpt line u (p.1 + p.2) = some a := by rw [hp, hf]
        have h1 : _root_.MIPStarRE.QPBT.evalOpt line u p.1 = some (a - c'') :=
          _root_.MIPStarRE.QPBT.evalOpt_left_of_add_some hsum h2
        rw [h1, hPt_some]
        rw [Finset.sum_eq_single (a - c'', c'')]
        · change Ψ (LM.effect p.1) (PM.effect (a - c'')) *
            (if some c'' = some c'' then c p.2 else 0) =
              Ψ (LM.effect p.1) (PM.effect (a - c'')) * c p.2
          rw [if_pos rfl]
        · intro q hq hne
          rw [if_neg, mul_zero]
          intro heq
          apply hne
          have hq2 : q.2 = c'' := (Option.some_inj.mp heq).symm
          have hq1 : q.1 + q.2 = a := (Finset.mem_filter.mp hq).2
          ext
          · change q.1 = a - c''
            rw [← hq1, hq2, add_sub_cancel_right]
          · exact hq2
        · intro hnot
          exfalso
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub_add_cancel a c''⟩)
  calc
    _ = ∑ f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d),
        ∑ p ∈ Finset.univ.filter
          (fun p : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) ×
            _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2 = f),
          Ψ (LM.effect p.1) (Pt (_root_.MIPStarRE.QPBT.evalOpt line u p.1)) * c p.2 := by
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [hΦl]
      exact Finset.sum_congr rfl fun p hp => hterm f p (Finset.mem_filter.mp hp).2
    _ = ∑ p : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) × _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d),
        Ψ (LM.effect p.1) (Pt (_root_.MIPStarRE.QPBT.evalOpt line u p.1)) * c p.2 :=
      Finset.sum_fiberwise Finset.univ
        (fun p : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) ×
          _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2)
        (fun p => Ψ (LM.effect p.1) (Pt (_root_.MIPStarRE.QPBT.evalOpt line u p.1)) * c p.2)
    _ = ∑ f' : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d),
        Ψ (LM.effect f') (Pt (_root_.MIPStarRE.QPBT.evalOpt line u f')) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun f' _ => ?_
      change ∑ y, Ψ (LM.effect f') (Pt (_root_.MIPStarRE.QPBT.evalOpt line u f')) * c y =
        Ψ (LM.effect f') (Pt (_root_.MIPStarRE.QPBT.evalOpt line u f'))
      rw [← Finset.mul_sum, hc, mul_one]
    _ = ∑ o : Option (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams),
        ∑ f' ∈ Finset.univ.filter
          (fun f' : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) => _root_.MIPStarRE.QPBT.evalOpt line u f' = o),
          Ψ (LM.effect f') (Pt o) := by
      rw [← Finset.sum_fiberwise Finset.univ (fun f' => _root_.MIPStarRE.QPBT.evalOpt line u f')
        (fun f' => Ψ (LM.effect f') (Pt (_root_.MIPStarRE.QPBT.evalOpt line u f')))]
      refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun f' hf' => ?_
      rw [(Finset.mem_filter.mp hf').2]
    _ = ∑ o : Option (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams),
        Ψ ((LM.postprocess (_root_.MIPStarRE.QPBT.evalOpt line u)).effect o) (Pt o) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, hΨl]
