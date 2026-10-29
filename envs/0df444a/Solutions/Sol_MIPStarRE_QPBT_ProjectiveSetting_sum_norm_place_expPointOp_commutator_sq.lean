-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.sum_norm_place_expPointOp_commutator_sq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:12:57.214633+00:00
-- url     : https://prove2.me/submissions/2b172885-2ecf-46ae-bd8f-749a5bcebd82

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.sum_norm_place_expPointOp_commutator_sq.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_CommutingObs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_sum_norm_sum_smul_sq_of_orthogonal
import Theorems.Thm_MIPStarRE_QPBT_sum_pairCharacter_mul_pairCharacter

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Distribution.IsProbability
end LIDT.MIPStarRE.LDT.Distribution.IsProbability
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace LIDT.MIPStarRE.Quantum.Measurement
end LIDT.MIPStarRE.Quantum.Measurement
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

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



/-! ## Fourier form of the point effects and of their commutator -/

/-- A uniform operator average is the normalized sum. -/
theorem averageOperatorOverDistribution_uniform_eq_inv_card_smul_sum
    {α ι : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype ι] [DecidableEq ι] (f : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f =
      (Fintype.card α : ℂ)⁻¹ • ∑ a, f a := by
  ext i j
  simp only [_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution, _root_.LIDT.MIPStarRE.LDT.uniformDistribution,
    _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset, Finset.mem_univ, if_true, Matrix.sum_apply,
    Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
    Finset.card_univ, one_div, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [Finset.mul_sum]

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-- The Fourier form of an expanded point effect as a normalized character
sum of the expanded observables.  This is the first display of
`def:expanded-point-measurement`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:384-418`. -/
theorem expPointOp_eq_inv_card_smul_sum (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    S.expPointOp side W u a =
      (Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) : ℂ)⁻¹ •
        ∑ r, _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * r)) • S.expObs side W r u := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointOp
  rw [_root_.MIPStarRE.QPBT.averageOperatorOverDistribution_uniform_eq_inv_card_smul_sum]

/-- Formalization-only auxiliary: the product of two normalized weighted sums
is the normalized double sum of the weighted products, indexed by pairs. -/
theorem smul_sum_mul_smul_sum {ι K : Type*} [Fintype K] [Fintype ι]
    (c : ℂ) (α β : K → ℂ) (X Z : K → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (c • ∑ r, α r • X r) * (c • ∑ s, β s • Z s) =
      (c * c) • ∑ rs : K × K, (α rs.1 * β rs.2) • (X rs.1 * Z rs.2) := by
  rw [Fintype.sum_prod_type, smul_mul_smul_comm, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [smul_mul_smul_comm]

/-- Formalization-only auxiliary: the product of two normalized weighted sums
in the opposite order, indexed by the same pairs. -/
theorem smul_sum_mul_smul_sum_swap {ι K : Type*} [Fintype K] [Fintype ι]
    (c : ℂ) (α β : K → ℂ) (X Z : K → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (c • ∑ s, β s • Z s) * (c • ∑ r, α r • X r) =
      (c * c) • ∑ rs : K × K, (α rs.1 * β rs.2) • (Z rs.2 * X rs.1) := by
  rw [Fintype.sum_prod_type_right, smul_mul_smul_comm, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
  rw [smul_mul_smul_comm, mul_comm (β s)]

/-- The commutator of two field-valued point effects is the Fourier transform
of the commutators of the expanded observables. -/
theorem expPointOp_commutator_eq (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (a b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    S.expPointOp side .X x a * S.expPointOp side .Z z b -
        S.expPointOp side .Z z b * S.expPointOp side .X x a =
      ((Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) : ℂ)⁻¹ *
          (Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) : ℂ)⁻¹) •
        ∑ rs : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
          (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * rs.1)) *
              _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (b * rs.2))) •
            (S.expObs side .X rs.1 x * S.expObs side .Z rs.2 z -
              S.expObs side .Z rs.2 z * S.expObs side .X rs.1 x) := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.expPointOp_eq_inv_card_smul_sum, _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointOp_eq_inv_card_smul_sum,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.smul_sum_mul_smul_sum, _root_.MIPStarRE.QPBT.ProjectiveSetting.smul_sum_mul_smul_sum_swap, ← smul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun rs _ => ?_
  rw [smul_sub]







end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/ExpandedCommutation.lean. -/
/-!
# Approximate commutation of the expanded point projections

The trace-coarse-grained expanded point projections approximately commute on
each of the four register placements.  The commutator of the two projections is
a scalar multiple of a factorized operator whose strategy factor is the twisted
commutator of the two point observables and whose Pauli factor is a product of
generalized Pauli observables; the latter is an isometry, so the placement
bookkeeping of `ExpandedPlacement` reduces the estimate to the twisted
commutation relation of `lem:qld-win-implications-obs` on the corresponding
player side.  Both player sides are treated explicitly.

## References

The declarations prove item 2 of `lem:qld-comm-cons` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Algebraic preliminaries -/





namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The commutator of two expanded point projections -/















/-! ## The approximate commutation on each placement -/

/-- The placement of a scalar multiple is the scalar multiple of the
placement. Paper `14_analysis_of_the_pauli_basis_test.tex:420-450`,
blueprint `ch14_qpbt_observables.tex:1002-1031`. -/
theorem place_smul (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement) (c : ℂ)
    (O : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)) :
    S.place p (c • O) = c • S.place p O := by
  ext i j
  cases p <;> simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.smul_apply, smul_eq_mul] <;> ring







end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/CommutingObs.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyCommObs
/-!
# Approximate commutation of the point observables on commuting tuples

This module carries out the commuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`: the chain of
consistency relations `eq:lc-11`, the commutation analysis
`lem:commutation-analysis`, and the expansion `eq:lc-12` of the observables in
terms of the trace-coarse-grained point projections.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-341`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications



/-! ## Algebraic preliminaries -/







/-! ## Pair/W self-consistency on commuting tuples -/





/-! ## The chained relation of Equation `eq:lc-11` -/



/-! ## The commutation analysis on commuting tuples -/









/-! ## From projections to observables -/

/-- Applying a scaled operator scales the resulting state. Formalization-only
support for `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`. -/
theorem applyOperatorToState_smul_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (c • M) v = c • _root_.MIPStarRE.QPBT.applyOperatorToState M v := by
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [map_smul, LinearMap.smul_apply]







end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Consistency.lean. -/
/-!
# Cross-player agreement of the Magic Square variable measurements

The rigidity theorem `thm:ms-rigidity` is false for arbitrary strategies of the
role-symmetric Magic Square game: its conclusion forces the two players'
`Variable_1` and `Variable_5` measurements to agree on the shared state, and the
game never tests that agreement.  The corrected statement adopted on issue
Dengnifer/MIPStarRE-QPBT-bak#172
(owner decision B5 on issue Dengnifer/MIPStarRE-QPBT-bak#26; the note is
`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`) assumes that
agreement, quantitatively.  The *variable-measurement agreement distance* at a
variable is the summed squared state-dependent distance between Alice's and
Bob's binary variable effects on the shared state, in the `≈_δ` convention of
`def:povm-distance`, and the corrected theorem bounds it at the paper's first
and fifth variables.

That distance is not the consistency defect of `def:consistency`, which is the
off-diagonal outcome weight of a pair of measurements (`consistencyDefect`); it
is the squared state-dependent distance `opFamilyDistSq` of
`def:povm-distance`.  In the declaration name `msVariableConsistencyDefect` the
word `Consistency` records the failure of the two players' variable
measurements to be consistent with one another, which is what the distance
measures, and not the defect of `def:consistency`; the blueprint states the
distinction as `rem:ms-variable-agreement-name`.  The name itself is kept
unchanged because the rigidity assembly of issue Dengnifer/MIPStarRE-QPBT-bak#105 is stated in terms
of it.

This file defines that distance on the original, possibly non-projective,
strategy and relates it to the reflections of the projective dilation on which
the self-testing argument operates.

* For a symmetric strategy whose variable measurements are consistent in the
  exact sense of `def:consistent-measurement`, the distance vanishes, so the
  corrected theorem specializes to the symmetric consistent strategies named in
  the owner decision.
* The two players' dilated variable reflections `msVarObsA S j` and
  `msVarObsB S j` are close on the dilated state whenever that distance is
  small.
  The loss is the leakage of the dilated observables out of the ground slice,
  which `Rigidity/Transfer.lean` controls by the cell-consistency masses of a
  strategy of value `1 - ε`.  This is the cross-player input that the
  swap-isometry extraction of issue Dengnifer/MIPStarRE-QPBT-bak#105 needs in order to compare the
  two
  players' extracted qubits.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
The consistency notions are `def:consistent-measurement` and `def:povm-distance`,
paper `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:144-174` and
`258-271`.  The variable indices are zero-based, so the paper's first and fifth
variables are the cells `0` and `4`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open MIPStarRE.QPBT.MagicSquareRigidity

noncomputable section

/-! ## The agreement distance of a variable measurement -/







/-! ## Exact consistency -/

/-- Formalization-only: the action on a state is additive over finite sums of
operators.  This is the `Finset` form of
`MagicSquareRigidity.applyOperatorToState_sum`, which sums over a `Fintype`;
the general form is the one `Measurement.postprocess_effect` needs, a
postprocessed effect being a sum over a fibre.  The two are kept apart because
the rigidity assembly of issue Dengnifer/MIPStarRE-QPBT-bak#105 already refers to this name; their
consolidation is issue Dengnifer/MIPStarRE-QPBT-bak#204. -/
theorem applyOperatorToState_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (∑ b ∈ s, M b) ψ = ∑ b ∈ s, _root_.MIPStarRE.QPBT.applyOperatorToState (M b) ψ := by
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState
  simp only [map_sum, LinearMap.sum_apply]











end

/-! ## Transfer to the dilated reflections -/



end MIPStarRE.QPBT

/- Source helpers from QPBT/Upstream.lean. -/
/-!
# Public helpers for the upstream LIDT interface

These finite-sum and measurement lemmas support the QPBT without modifying its LIDT dependency.
The marginal-state construction and rank-zero argument adapt the private proofs in
`LionSR/MIPStarRE`, commit `f382c801026f53a9efc260fdee707cb35e0adb15`, module
`MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair`.
The remaining lemmas are QPBT extensions of the upstream measurement and distribution APIs.
Their proofs use the public definitions and Mathlib finite-dimensional linear algebra.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder



namespace LIDT
namespace MIPStarRE.LDT



/-- A uniform average over a finite type is its normalized finite sum. -/
theorem avgOver_uniform_eq_inv_card_mul_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver _root_.LIDT.MIPStarRE.LDT.uniformDistribution _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset
  simp only [Finset.mem_univ, ite_true, Finset.card_univ, one_div, Finset.mul_sum]


end MIPStarRE.LDT
end LIDT

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













/-! ## Fourier form of the point effects and of their commutator -/



open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (p : _root_.MIPStarRE.QPBT.Placement) (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    ∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p
          (S.expPointOp p.side .X x ab.1 * S.expPointOp p.side .Z z ab.2 -
            S.expPointOp p.side .Z z ab.2 * S.expPointOp p.side .X x ab.1))
          S.psiHat‖ ^ 2 =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun rs => ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p
          (S.expObs p.side .X rs.1 x * S.expObs p.side .Z rs.2 z -
            S.expObs p.side .Z rs.2 z * S.expObs p.side .X rs.1 x))
          S.psiHat‖ ^ 2) := by
  set v : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P →
      EuclideanSpace ℂ (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
    fun rs => _root_.MIPStarRE.QPBT.applyOperatorToState (S.place p
      (S.expObs p.side .X rs.1 x * S.expObs p.side .Z rs.2 z -
        S.expObs p.side .Z rs.2 z * S.expObs p.side .X rs.1 x)) S.psiHat
  set c : ℂ := (Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) : ℂ)⁻¹
  have hpt : ∀ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
      _root_.MIPStarRE.QPBT.applyOperatorToState (S.place p
          (S.expPointOp p.side .X x ab.1 * S.expPointOp p.side .Z z ab.2 -
            S.expPointOp p.side .Z z ab.2 * S.expPointOp p.side .X x ab.1))
          S.psiHat =
        (c * c) • ∑ rs : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
          (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (ab.1 * rs.1)) *
              _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (ab.2 * rs.2))) • v rs := by
    intro ab
    rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.expPointOp_commutator_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_smul, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_finsetSum,
      _root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_smul_op, _root_.MIPStarRE.QPBT.applyOperatorToState_finset_sum]
    congr 1
    refine Finset.sum_congr rfl fun rs _ => ?_
    rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_smul, _root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_smul_op]
  have hparseval := _root_.MIPStarRE.QPBT.sum_norm_sum_smul_sq_of_orthogonal
    (fun (ab rs : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) =>
      _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (ab.1 * rs.1)) *
        _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (ab.2 * rs.2)))
    ((Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) : ℝ) ^ 2)
    (fun rs rs' => _root_.MIPStarRE.QPBT.sum_pairCharacter_mul_pairCharacter rs rs') v
  have hq : (0 : ℝ) < (Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcnorm : ‖c * c‖ = ((Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) : ℝ) ^ 2)⁻¹ := by
    simp only [c, norm_mul, norm_inv, Complex.norm_natCast]
    rw [sq, mul_inv]
  calc ∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p
          (S.expPointOp p.side .X x ab.1 * S.expPointOp p.side .Z z ab.2 -
            S.expPointOp p.side .Z z ab.2 * S.expPointOp p.side .X x ab.1))
          S.psiHat‖ ^ 2
      = ∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
          ‖c * c‖ ^ 2 * ‖∑ rs : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
            (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (ab.1 * rs.1)) *
              _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (ab.2 * rs.2))) • v rs‖ ^ 2 := by
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [hpt, norm_smul, mul_pow]
    _ = ‖c * c‖ ^ 2 * (((Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) : ℝ) ^ 2) *
          ∑ rs, ‖v rs‖ ^ 2) := by
        rw [← Finset.mul_sum, hparseval]
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P))
          (fun rs => ‖v rs‖ ^ 2) := by
        rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_prod, hcnorm]
        push_cast
        field_simp
