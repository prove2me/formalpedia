-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.exp_point_comm_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:17:59.209654+00:00
-- url     : https://prove2.me/submissions/40b8308e-1c03-4b10-bb23-80bed7a78343

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.exp_point_comm_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Algebra_PauliTheorems
import Definitions.Def_QPBT_QPBT_Combining_Points_Commutation
import Definitions.Def_QPBT_QPBT_ExplicitConstants
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedCommutation
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_CommutingObs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_TwistedCommutation
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_norm_place_AA_prime_heteroKron_psiHat
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_norm_place_AB_prime_prime_heteroKron_psiHat
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_norm_place_BA_prime_prime_heteroKron_psiHat
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_norm_place_BB_prime_heteroKron_psiHat
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_sum_norm_place_expPointOp_commutator_sq
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_tauZ_mul_tauX
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_twisted_commutator_avg_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_Strategy_value_le_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
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



/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects differences in the left factor. -/
theorem heteroKron_sub_left {ιA ιB : Type*} (A B : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (A - B) C = _root_.MIPStarRE.QPBT.heteroKron A C - _root_.MIPStarRE.QPBT.heteroKron B C :=
  _root_.MIPStarRE.QPBT.kroneckerMap_sub_left A B C



/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/








































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











namespace ProjectiveSetting





variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The strategy factor of a placement -/



/-- The placement of a difference is the difference of the placements. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
theorem place_sub (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement)
    (O₁ O₂ : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)) :
    S.place p (O₁ - O₂) = S.place p O₁ - S.place p O₂ := by
  ext i j
  cases p <;> simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.sub_apply, sub_mul, mul_sub]

/-! ## The action of a placement on the expanded state -/





/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/

























/-- A factorized operator placed on one of the four register pairs has, on the
expanded state, the state-dependent norm of its strategy factor on the original
state, provided its Pauli factor is an isometry. This is the placement
bookkeeping behind `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:420-505`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
theorem norm_place_heteroKron_psiHat (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (p : _root_.MIPStarRE.QPBT.Placement) (T : _root_.LIDT.MIPStarRE.Quantum.Op (S.LocalSpace p.side)) (V : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))
    (hV : Vᴴ * V = 1) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p (_root_.MIPStarRE.QPBT.heteroKron T V)) S.psiHat‖ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.placeStrategySide p.side T) S.toStrategy.ψ‖ := by
  cases p with
  | AA' => exact _root_.MIPStarRE.QPBT.ProjectiveSetting.norm_place_AA_prime_heteroKron_psiHat S T V hV
  | BA'' => exact _root_.MIPStarRE.QPBT.ProjectiveSetting.norm_place_BA_prime_prime_heteroKron_psiHat S T V hV
  | BB' => exact _root_.MIPStarRE.QPBT.ProjectiveSetting.norm_place_BB_prime_heteroKron_psiHat S T V hV
  | AB'' => exact _root_.MIPStarRE.QPBT.ProjectiveSetting.norm_place_AB_prime_prime_heteroKron_psiHat S T V hV

end ProjectiveSetting

end

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



/-- Every strategy value is at most one. This is an alias of the Games-layer
`MIPStarRE.QPBT.Strategy.value_le_one`, which carries the single proof; the name
is kept here so the existing callers of this layer resolve unchanged.
Formalization-only support for `def:tensor-product-value`, blueprint
`ch12_qpbt_games.tex:71-82`. -/
theorem strategy_value_le_one {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) : S.value ≤ 1 :=
  _root_.MIPStarRE.QPBT.Strategy.value_le_one S

















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

/- Source helpers from QPBT/Observables/WinImplications/TwistedCommutation.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyTwisted
/-!
# The phase-signed commutation relation of the point observables

This module assembles the commuting and anticommuting halves into Equation
`eq:pts-obs-commutation` of `lem:qld-win-implications-obs`: on average over a
uniformly random tuple the two point observables commute up to the sign
`(-1)^gamma(omega)`, with error the square root of the test error.

## References

The declarations formalize the first assertion of
`lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-362`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications



/-! ## The unconditional bound on a difference of reflections -/

/-- The product of two isometries is an isometry. Formalization-only support
for `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`. -/
theorem mul_conjTranspose_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc
    Bᴴ * Aᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by noncomm_ring
    _ = Bᴴ * B := by rw [hA, mul_one]
    _ = 1 := hB



/-! ## Splitting the uniform average -/









/-! ## The twisted commutation relation -/



/-! ## The commuting half on Alice's factor -/









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

/- Source helpers from QPBT/Test/PauliBasisTest.lean. -/
/-!
# The Pauli basis test

This file supplies the finite question and answer alphabets, the typed
conditionally-linear question sampler, and the Boolean win predicate for the
Pauli basis test.  The quantitative soundness theorem is isolated in
`Soundness.lean`.

## References

The source-facing nodes are blueprint `def:admissible`,
`def:pauli-question-distribution`, and `def:pauli-win-predicate`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:908-1225`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section



















/- The nested sum is the fixed register order
`V_X ⊕ V_Z ⊕ V_I ⊕ V_V ⊕ V_{R_X} ⊕ V_{R_Z}` from the blueprint. -/


















































set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Deciding the cardinality unfolds the nested finite sum and product alphabets.
/-- The ordered carrier of the Pauli question graph has `86` edges: its
`26` loops occur once, while its `30` non-loop undirected edges occur in both
orientations. This finite computation supports the explicit quantitative
baseline for `thm:pauli`; the graph itself is unchanged. -/
theorem pauli_edge_card : Fintype.card _root_.MIPStarRE.QPBT.PauliEdge = 86 := by
  decide





































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



/-- The generalized Pauli observables are reflections. Blueprint
`ch11_qpbt_algebra.tex:596-644`, paper
`references/qpbt-paper/04_preliminaries.tex:1088-1089`. -/
theorem tauObservable_conjTranspose_mul_self {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι]
    [DecidableEq ι] (W : _root_.MIPStarRE.QPBT.PauliKind) (v : ι → K) :
    (_root_.MIPStarRE.QPBT.tauObservable W v)ᴴ * _root_.MIPStarRE.QPBT.tauObservable W v = 1 := by
  rw [_root_.MIPStarRE.QPBT.tauObservable_conjTranspose, _root_.MIPStarRE.QPBT.tauObservable_sq]

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The commutator of two expanded point projections -/





/-- The product of the two Pauli-register factors is an isometry. Blueprint
`ch11_qpbt_algebra.tex:596-644`, paper
`references/qpbt-paper/04_preliminaries.tex:1088-1095`. -/
theorem tauX_mul_tauZ_isometry (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ω : _root_.MIPStarRE.QPBT.PauliTuple P) :
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauX P ω * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauZ P ω)ᴴ * (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauX P ω * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauZ P ω) = 1 :=
  _root_.MIPStarRE.QPBT.WinImplications.mul_conjTranspose_mul_self
    (_root_.MIPStarRE.QPBT.tauObservable_conjTranspose_mul_self _ _)
    (_root_.MIPStarRE.QPBT.tauObservable_conjTranspose_mul_self _ _)





/-- The commutator of the two expanded observables factorizes with the twisted
commutator of the point observables on the strategy register. This is the
display following `eq:lc-23` in the proof of `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:487-505`, blueprint
`ch14_qpbt_observables.tex:1164-1175`. -/
theorem expObs_commutator (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (ω : _root_.MIPStarRE.QPBT.PauliTuple P) :
    S.expObs side .X ω.2.2.1 ω.1 * S.expObs side .Z ω.2.2.2 ω.2.1 -
        S.expObs side .Z ω.2.2.2 ω.2.1 * S.expObs side .X ω.2.2.1 ω.1 =
      _root_.MIPStarRE.QPBT.heteroKron (S.twistedCommutator side ω) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauX P ω * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauZ P ω) := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.expObs, _root_.MIPStarRE.QPBT.ProjectiveSetting.expObs, _root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul]
  rw [show _root_.MIPStarRE.QPBT.tauObservable .X (fun h => ω.2.2.1 * _root_.MIPStarRE.QPBT.indicatorVec ω.1 h) =
    _root_.MIPStarRE.QPBT.ProjectiveSetting.tauX P ω from rfl,
    show _root_.MIPStarRE.QPBT.tauObservable .Z (fun h => ω.2.2.2 * _root_.MIPStarRE.QPBT.indicatorVec ω.2.1 h) =
      _root_.MIPStarRE.QPBT.ProjectiveSetting.tauZ P ω from rfl]
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.tauZ_mul_tauX, _root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_smul_right,
    ← _root_.MIPStarRE.QPBT.WinImplications.heteroKron_smul_left,
    ← _root_.MIPStarRE.QPBT.heteroKron_sub_left, _root_.MIPStarRE.QPBT.ProjectiveSetting.twistedCommutator]



/-! ## The approximate commutation on each placement -/









end ProjectiveSetting

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













/-! ## Fourier form of the point effects and of their commutator -/



open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
      (p : _root_.MIPStarRE.QPBT.Placement),
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
        (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) => S.place p
          ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p.side .Z xz.2).effect ab.2))
        (fun xz ab => S.place p
          ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p.side .X xz.1).effect ab.1))
        S.psiHat ≤ _root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant * Real.sqrt ε := by
  intro P ε S p
  have hε : (0 : ℝ) ≤ ε := by
    have hv := _root_.MIPStarRE.QPBT.WinImplications.strategy_value_le_one S.toStrategy
    have hw := S.win
    linarith
  have hnorm : ∀ (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
      (rs : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P),
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p
          (S.expObs p.side .X rs.1 x * S.expObs p.side .Z rs.2 z -
            S.expObs p.side .Z rs.2 z * S.expObs p.side .X rs.1 x))
          S.psiHat‖ ^ 2 =
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (S.placeStrategySide p.side (S.twistedCommutator p.side (x, z, rs.1, rs.2)))
          S.toStrategy.ψ‖ ^ 2 := by
    intro x z rs
    rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.expObs_commutator S p.side (x, z, rs.1, rs.2),
      _root_.MIPStarRE.QPBT.ProjectiveSetting.norm_place_heteroKron_psiHat S p _ _ (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauX_mul_tauZ_isometry P (x, z, rs.1, rs.2))]
  have hfamily : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
      (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) => S.place p
        ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p.side .Z xz.2).effect ab.2))
      (fun xz ab => S.place p
        ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1))
      S.psiHat =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) (fun ω =>
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (S.placeStrategySide p.side (S.twistedCommutator p.side ω))
          S.toStrategy.ψ‖ ^ 2) := by
    unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
    calc _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P)) (fun xz =>
          ∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
            ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p
                ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
                  (S.pointMeasExp p.side .Z xz.2).effect ab.2) -
              S.place p ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
                (S.pointMeasExp p.side .X xz.1).effect ab.1)) S.psiHat‖ ^ 2)
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P)) (fun xz =>
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P))
              (fun rs => ‖_root_.MIPStarRE.QPBT.applyOperatorToState
                (S.placeStrategySide p.side
                  (S.twistedCommutator p.side (xz.1, xz.2, rs.1, rs.2)))
                S.toStrategy.ψ‖ ^ 2)) := by
          refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun xz => ?_
          rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ (hnorm xz.1 xz.2),
            ← _root_.MIPStarRE.QPBT.ProjectiveSetting.sum_norm_place_expPointOp_commutator_sq S p xz.1 xz.2]
          refine Finset.sum_congr rfl fun ab _ => ?_
          rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_sub]
          rfl
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P × (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P)))
            (fun q => ‖_root_.MIPStarRE.QPBT.applyOperatorToState
              (S.placeStrategySide p.side
                (S.twistedCommutator p.side (q.1.1, q.1.2, q.2.1, q.2.2)))
              S.toStrategy.ψ‖ ^ 2) :=
          (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (fun (xz : _root_.MIPStarRE.QPBT.PointPair P)
            (rs : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) => ‖_root_.MIPStarRE.QPBT.applyOperatorToState
              (S.placeStrategySide p.side
                (S.twistedCommutator p.side (xz.1, xz.2, rs.1, rs.2)))
              S.toStrategy.ψ‖ ^ 2)).symm
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) (fun ω =>
            ‖_root_.MIPStarRE.QPBT.applyOperatorToState
              (S.placeStrategySide p.side (S.twistedCommutator p.side ω))
              S.toStrategy.ψ‖ ^ 2) := by
          rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (Equiv.prodAssoc (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
            (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P))]
          rfl
  rw [hfamily]
  have h := _root_.MIPStarRE.QPBT.ProjectiveSetting.twisted_commutator_avg_le_explicit P ε S p.side hε
  rw [_root_.MIPStarRE.QPBT.pauli_edge_card] at h
  convert h using 1 <;>
    simp only [_root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant, _root_.MIPStarRE.QPBT.pauliBaselineCommutatorConstant,
      Nat.cast_ofNat] <;> ring
