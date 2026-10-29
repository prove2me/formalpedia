-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.twisted_commutator_avg_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:09:24.799137+00:00
-- url     : https://prove2.me/submissions/8fc61ddb-50fc-464d-bd88-335fae7e729f

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.twisted_commutator_avg_le_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedCommutation
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_CommutingObs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_point_obs_twisted_commutation_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_point_obs_twisted_commutation_interchanged_explicit

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
end MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Games/Defs.lean. -/
/-!
# Games, tensor-product strategies, and value

This file provides the finite game carrier used by the Pauli basis test.  Pure
states are vectors in `EuclideanSpace`, and POVMs use the project's matrix
`Measurement` structure.

## References

The source-facing nodes are blueprint `def:game`, `def:povm-conventions`,
`def:tensor-product-strategy`, and `def:tensor-product-value`.
The paper origin is `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



attribute [instance] _root_.MIPStarRE.QPBT.Game.questionAFintype _root_.MIPStarRE.QPBT.Game.questionBFintype
  _root_.MIPStarRE.QPBT.Game.answerAFintype _root_.MIPStarRE.QPBT.Game.answerBFintype _root_.MIPStarRE.QPBT.Game.questionADecidableEq
  _root_.MIPStarRE.QPBT.Game.questionBDecidableEq _root_.MIPStarRE.QPBT.Game.answerADecidableEq _root_.MIPStarRE.QPBT.Game.answerBDecidableEq









attribute [instance] _root_.MIPStarRE.QPBT.Strategy.ιAFintype _root_.MIPStarRE.QPBT.Strategy.ιBFintype
  _root_.MIPStarRE.QPBT.Strategy.ιADecidableEq _root_.MIPStarRE.QPBT.Strategy.ιBDecidableEq



/-! ### Algebra of the tensor placement

The shared tensor-placement API.  These identities are used both by the perfect
Magic Square strategy (blueprint `thm:ms-from-ac`) and by the rigidity transfer
step (blueprint `thm:ms-rigidity`), so they live
with the definition rather than in either development. -/













/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`: the
tensor placement of possibly rectangular matrices respects differences in the
left factor.  This is the general form of `heteroKron_sub_left` below, needed
where the left factor is the matrix of an isometry between distinct index
types (blueprint
`thm:ms-rigidity`). -/
theorem kroneckerMap_sub_left {m n p q : Type*} (A B : Matrix m n ℂ) (C : Matrix p q ℂ) :
    Matrix.kroneckerMap (· * ·) (A - B) C =
      Matrix.kroneckerMap (· * ·) A C - Matrix.kroneckerMap (· * ·) B C := by
  ext p' q'
  simp [Matrix.kroneckerMap, sub_mul]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`: the
tensor placement of possibly rectangular matrices respects differences in the
right factor.  This is the general form of `heteroKron_sub_right` below. -/
theorem kroneckerMap_sub_right {m n p q : Type*} (A : Matrix m n ℂ) (B C : Matrix p q ℂ) :
    Matrix.kroneckerMap (· * ·) A (B - C) =
      Matrix.kroneckerMap (· * ·) A B - Matrix.kroneckerMap (· * ·) A C := by
  ext p' q'
  simp [Matrix.kroneckerMap, mul_sub]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects differences in the left factor. -/
theorem heteroKron_sub_left {ιA ιB : Type*} (A B : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (A - B) C = _root_.MIPStarRE.QPBT.heteroKron A C - _root_.MIPStarRE.QPBT.heteroKron B C :=
  _root_.MIPStarRE.QPBT.kroneckerMap_sub_left A B C

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects differences in the right factor. -/
theorem heteroKron_sub_right {ιA ιB : Type*} (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron A (B - C) = _root_.MIPStarRE.QPBT.heteroKron A B - _root_.MIPStarRE.QPBT.heteroKron A C :=
  _root_.MIPStarRE.QPBT.kroneckerMap_sub_right A B C

/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/








































end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/AnticommutingObs.lean. -/
/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/

/-- The unit-alphabet operator distance written as an average of squared
state-dependent norms. Formalization-only support for `def:povm-distance`,
blueprint `ch12_qpbt_games.tex:234-241`. -/
theorem opDistSq_eq_avgOver {X ι : Type*} [Fintype X] [DecidableEq X]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opDistSq μ M N ψ =
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M x - N x) ψ‖ ^ 2) := by
  unfold _root_.MIPStarRE.QPBT.opDistSq _root_.MIPStarRE.QPBT.opFamilyDistSq
  simp



















end WinImplications

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

/-- The left tensor placement is homogeneous in its left factor.
Formalization-only support for `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`. -/
theorem heteroKron_smul_left {ιA ιB : Type*} (c : ℂ) (M : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (c • M) B = c • _root_.MIPStarRE.QPBT.heteroKron M B := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, mul_assoc]





/-! ## Pair/W self-consistency on commuting tuples -/





/-! ## The chained relation of Equation `eq:lc-11` -/



/-! ## The commutation analysis on commuting tuples -/









/-! ## From projections to observables -/









end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Reflections.lean. -/
/-!
# Reflections and the state-dependent metric on operators

The self-testing argument for the Magic Square game manipulates `±1`-valued
observables rather than positive operator valued measures.  This file records
the algebra of such observables and the estimates that convert Born masses into
operator bounds.

Postprocessing a projective measurement along a binary relabelling of its
answers produces a *reflection*, that is, a self-adjoint involution; two
reflections coming from one and the same measurement commute, and their product
is the reflection attached to the sum of the two relabellings.  The reflections
of the source are the binary observables of the rest of the development, so this
file uses `MIPStarRE.QPBT.IsBinaryObservable` and its algebra, defined in
`MIPStarRE/QPBT/Combining/Linearity/Defs.lean`, rather than a second predicate of
its own.  Two operators are compared through the norm of the difference of their
actions on a fixed state, the relation `NormCloseOn` below.  That relation is the
unsquared Euclidean distance between `M ψ` and `N ψ`; it is *not* the
state-dependent distance `≈_δ` of the source, which bounds the squared quantity
`⟨ψ|(M - N)ᴴ (M - N)|ψ⟩` and is formalized in this development by `opDistSq`.
The comparison is symmetric, satisfies the triangle inequality, and is unchanged
by multiplication on the left by an isometric operator; `NormCloseOn.opDistSq_le`
converts it into the source's relation.  Finally, a real spectral combination of
the joint effects of the two players has state-dependent norm controlled by the
Born mass of the answer pairs carrying a nonzero coefficient; this is the step
that turns each rejection mass of the value-to-parity layer into an operator
estimate.

## References

The statements supported here are the operator relations in `thm:ms-rigidity`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Rectangular tensor placement -/



/-! ## The state-dependent norm -/



/-! ## Reflections

The *reflections* of `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:228-250`, are the self-adjoint involutions attached to
two-outcome projective measurements, which are exactly the binary observables
`MIPStarRE.QPBT.IsBinaryObservable` of
`MIPStarRE/QPBT/Combining/Linearity/Defs.lean`.  The Magic Square rigidity
argument therefore uses that predicate and its algebra directly:
`IsBinaryObservable.one`, `IsBinaryObservable.mul`,
`IsBinaryObservable.isometry`, `isBinaryObservable_heteroKron_one` and
`isBinaryObservable_one_heteroKron`. -/



/-! ## Closeness in the state-dependent norm -/





/-! ## Sign observables of a projective measurement -/



/-! ## Deviation of joint spectral combinations on the strategy state -/

section JointDefect

/-- Formalization-only: scalars pass through the second tensor factor. -/
theorem heteroKron_smul_right {ιA ιB : Type} (c : ℂ) (M : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (N : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron M (c • N) = c • _root_.MIPStarRE.QPBT.heteroKron M N := by
  unfold _root_.MIPStarRE.QPBT.heteroKron
  exact Matrix.kronecker_smul c M N





variable {G : _root_.MIPStarRE.QPBT.Game}













end JointDefect

end

end MIPStarRE.QPBT.MagicSquareRigidity

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



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



/-! ## Algebraic preliminaries -/





open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The commutator of two expanded point projections -/















/-! ## The approximate commutation on each placement -/

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
        (side : _root_.MIPStarRE.QPBT.PlayerSide), 0 ≤ ε →
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) (fun ω =>
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.placeStrategySide side (S.twistedCommutator side ω))
          S.toStrategy.ψ‖ ^ 2) ≤
        2 * (2 * (1024 * (2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
              1024 * Real.sqrt (4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) +
            (96 * (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
              3551040 * (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) + 4) *
            Real.sqrt ε := by
  intro P ε S side hε
  have hs : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  cases side with
  | alice =>
      have h := _root_.MIPStarRE.QPBT.WinImplications.point_obs_twisted_commutation_explicit P ε S hε
      rw [_root_.MIPStarRE.QPBT.WinImplications.opDistSq_eq_avgOver] at h
      refine le_trans (le_of_eq ?_) (le_trans h ?_)
      · refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ (fun ω => ?_)
        have hop : S.placeStrategySide .alice (S.twistedCommutator .alice ω) =
            _root_.MIPStarRE.QPBT.heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
                S.pointObs .alice .Z ω.2.2.2 ω.2.1)
                (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) -
              _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
                _root_.MIPStarRE.QPBT.heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
                  S.pointObs .alice .X ω.2.2.1 ω.1) 1 := by
          have h1 : _root_.MIPStarRE.QPBT.heteroKron (S.twistedCommutator .alice ω)
              (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) =
              _root_.MIPStarRE.QPBT.heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
                S.pointObs .alice .Z ω.2.2.2 ω.2.1) 1 -
                _root_.MIPStarRE.QPBT.heteroKron
                  (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
                    (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
                      S.pointObs .alice .X ω.2.2.1 ω.1)) 1 :=
            _root_.MIPStarRE.QPBT.heteroKron_sub_left _ _ _
          rw [← _root_.MIPStarRE.QPBT.WinImplications.heteroKron_smul_left]
          exact h1
        rw [hop]
      · have hcoeff : 0 ≤
            2 * (1024 * (2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
                1024 * Real.sqrt (4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) +
              (96 * (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
                3551040 * (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) + 4 := by
          positivity
        nlinarith
  | bob =>
      have h :=
        _root_.MIPStarRE.QPBT.WinImplications.point_obs_twisted_commutation_interchanged_explicit P ε S hε
      rw [_root_.MIPStarRE.QPBT.WinImplications.opDistSq_eq_avgOver] at h
      refine le_trans (le_of_eq ?_) (le_trans h ?_)
      · refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ (fun ω => ?_)
        have hop : S.placeStrategySide .bob (S.twistedCommutator .bob ω) =
            _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
                (S.pointObs .bob .X ω.2.2.1 ω.1 *
                  S.pointObs .bob .Z ω.2.2.2 ω.2.1) -
              _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
                _root_.MIPStarRE.QPBT.heteroKron 1 (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
                  S.pointObs .bob .X ω.2.2.1 ω.1) := by
          have h1 : _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
              (S.twistedCommutator .bob ω) =
              _root_.MIPStarRE.QPBT.heteroKron 1 (S.pointObs .bob .X ω.2.2.1 ω.1 *
                S.pointObs .bob .Z ω.2.2.2 ω.2.1) -
                _root_.MIPStarRE.QPBT.heteroKron 1
                  (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
                    (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
                      S.pointObs .bob .X ω.2.2.1 ω.1)) :=
            _root_.MIPStarRE.QPBT.heteroKron_sub_right _ _ _
          rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_smul_right]
          exact h1
        rw [hop]
      · have hcoeff : 0 ≤
            2 * (1024 * (2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
                1024 * Real.sqrt (4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) +
              (96 * (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
                3551040 * (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) + 4 := by
          positivity
        nlinarith
