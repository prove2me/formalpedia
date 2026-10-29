-- Prove2me | solution 1 for MIPStarRE.QPBT.pauliMagicMeasurement_var_effect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:56:53.937363+00:00
-- url     : https://prove2.me/submissions/5f93f9d2-747a-4047-969c-2da7c55c32db

-- Generated proof for MIPStarRE.QPBT.pauliMagicMeasurement_var_effect.
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
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Basic
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Measurements
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Observables
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

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









/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
is additive in the left factor. -/
theorem heteroKron_add_left {ιA ιB : Type*} (A B : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (A + B) C = _root_.MIPStarRE.QPBT.heteroKron A C + _root_.MIPStarRE.QPBT.heteroKron B C := by
  ext p q
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, add_mul]



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

/- Source helpers from QPBT/Test/MagicSquareTheorems/PerfectStrategy/Measurements.lean. -/
/-!
# Measurements of the perfect Magic Square strategy

This module turns the operator table of `thm:ms-from-ac` into a measurement
family.  It forms the joint measurement of two commuting binary projective
measurements, records the post-processing identities for injective
relabellings, encodes a constraint answer as the parity triple determined by
two freely chosen bits, and assembles the nine cell measurements into the
Magic Square measurement family, closing with the multiplication rule relating
a constraint outcome to the outcomes of its incident variables.

## References

The source statement is blueprint
`thm:ms-from-ac`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section







































/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): on a variable question the global measurement
family reproduces the corresponding cell measurement: its effect at the answer
`bit b` is the effect of `P j` at `b`. -/
theorem msStrategyMeasurement_var_bit
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (j : Fin 9) (b : ZMod 2) :
    (_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm (.var j)).effect (.bit b) =
      (P j).effect b := by
  exact postprocess_effect_of_injective (P j) _root_.MIPStarRE.QPBT.MsAnswer.bit
    bit_embedding_injective b

















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

section Kron



/-- Formalization-only: scalars pass through the first factor. -/
theorem heteroKron_smul_left {ιA ιB : Type} (c : ℂ) (M : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (N : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (c • M) N = c • _root_.MIPStarRE.QPBT.heteroKron M N := by
  unfold _root_.MIPStarRE.QPBT.heteroKron
  exact Matrix.smul_kronecker c M N





end Kron

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



end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Marginals.lean. -/
/-!
# Transporting the first logical pair through the two-qubit controlled swap

The bit-measurement conclusions of `thm:ms-rigidity` compare each player's
variable-0 and variable-4 measurements, conjugated by the two-qubit
controlled-swap embedding, with the marginals of the two-qubit Pauli basis over
the first register coordinate.  `Rigidity/TwoQubitIntertwine.lean` identifies
those marginals with the spectral effects of the two-qubit Pauli observables.
This file carries the one-qubit intertwining relations of `Rigidity/Swap.lean`
through the *second* controlled swap, which is the remaining step.

The transport is expressed at the level of the matrix of the embedding.  The
phase observable is transported exactly, because the residual factors of the
first swap absorb their controlling observable with the sign of the register
label and the residual factors of the second swap are untouched.  For the shift
observable the transport defect `D` satisfies the exact identity
`Dᴴ D = (1/2) · GᴴG`, where `G` is the anticommutator of the first pair: the
residual factors of the second swap form a complete family and therefore drop
out of `Dᴴ D`, leaving the one-qubit computation of `Rigidity/Swap.lean`.  The
spectral effects of the two observables inherit these estimates with a further
factor `1/4`, and tensoring with the other player's embedding preserves them
because that embedding is an isometry.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the cited robust self-test is Coladangelo--Stark, arXiv:1709.09267v2,
Theorem 6.9, `references/cs-paper/self-testing.tex:660-730`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Matrix products with a register operator placed on the left -/









/-! ## Block decomposition of a Gram matrix -/



/-! ## The matrix of the two-qubit controlled swap -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]







/-! ## The shift transport defect -/











/-! ## The spectral effects of the transported observables -/





/-! ## Transport on the joint state -/

variable {ιA ιB κA κB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]













/-! ## Magic Square specialization -/

/-- The spectral effects of a left-placed reflection are the placed spectral
effects. -/
theorem reflectionEffect_heteroKron_left (Z : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (b : ZMod 2) :
    _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.reflectionEffect Z b) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) =
      _root_.MIPStarRE.QPBT.reflectionEffect (_root_.MIPStarRE.QPBT.heteroKron Z (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB)) b := by
  rcases _root_.MIPStarRE.QPBT.zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [_root_.MIPStarRE.QPBT.reflectionEffect, if_pos]
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_smul_left, _root_.MIPStarRE.QPBT.heteroKron_add_left, _root_.MIPStarRE.QPBT.heteroKron_one_one]
  · simp only [_root_.MIPStarRE.QPBT.reflectionEffect, if_neg one_ne_zero]
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_smul_left, _root_.MIPStarRE.QPBT.heteroKron_sub_left, _root_.MIPStarRE.QPBT.heteroKron_one_one]



























end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# The honest Pauli basis measurements of the completeness proof

This module builds the measurements used by the honest strategy of
`lem:pauli-completeness`: the generalized Pauli basis measurement in a fixed
basis `W`, and its coarse-graining by the binary trace
`h ↦ tr(g_h(u_W) r_W)` which the source calls `A` (for `W = X`) and `B`
(for `W = Z`).  The main results are the observable identity

  `A_0 - A_1 = τ^W(ind_m(u_W) r_W)`

of `eq:finally-got-an-observable`, and the resulting commutation law

  `𝒪_A 𝒪_B = (-1)^γ 𝒪_B 𝒪_A`

with `γ` the phase bit `eq:gamma-value`.  When `γ ≠ 0` the two observables
anticommute, so `thm:ms-from-ac` produces the Magic Square part of the honest
strategy.

## References

The construction is the strategy displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`;
blueprint `lem:pauli-completeness`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]
  [Fintype ι] [DecidableEq ι]

/-! ### The generalized Pauli basis measurement -/









/-! ### Symmetry and Hermiticity of the generalized Pauli observables -/



/-! ### Orthogonality of the generalized Pauli projectors

The generalized Pauli projectors in a fixed basis are pairwise orthogonal, so
every coarse-graining of a Pauli basis measurement is again projective.  This is
the projectivity used throughout the honest strategy of `lem:pauli-completeness`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`.
-/








/-! ### The honest Pair/W measurements

For an ambient question `ω = (u_X, u_Z, r_X, r_Z)` the honest player measures
the Pauli register in basis `W` and reports the binary trace
`tr(g_h(u_W) r_W)` of the resulting label.  These are the measurements `A` and
`B` of the proof of `lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1277-1286`.
-/

















/-! ### The honest Point/W measurements -/







/-! ### Honest line measurements -/



















/-! ### The commutation law of the honest pair -/







/-! ### The pointwise Magic Square measurement -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (hgamma : _root_.MIPStarRE.QPBT.pauliPairGamma P z ≠ 0) (b : ZMod 2) :
    (_root_.MIPStarRE.QPBT.pauliMagicMeasurement P z hgamma (.var 0)).effect (.bit b) =
        _root_.MIPStarRE.QPBT.heteroKron
          ((_root_.MIPStarRE.QPBT.pauliTraceMeasurement P .X (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliRXBlock z)).effect b)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ZMod 2)) ∧
      (_root_.MIPStarRE.QPBT.pauliMagicMeasurement P z hgamma (.var 4)).effect (.bit b) =
        _root_.MIPStarRE.QPBT.heteroKron
          ((_root_.MIPStarRE.QPBT.pauliTraceMeasurement P .Z (_root_.MIPStarRE.QPBT.pauliZBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z)).effect b)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ZMod 2)) := by
  constructor
  · unfold _root_.MIPStarRE.QPBT.pauliMagicMeasurement
    rw [_root_.MIPStarRE.QPBT.msStrategyMeasurement_var_bit]
    change _root_.MIPStarRE.QPBT.reflectionEffect
        (_root_.MIPStarRE.QPBT.heteroKron
          (_root_.MIPStarRE.QPBT.obsOf (_root_.MIPStarRE.QPBT.pauliTraceMeasurement P .X (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliRXBlock z)))
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ZMod 2))) b = _
    rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.reflectionEffect_heteroKron_left,
      _root_.MIPStarRE.QPBT.reflectionEffect_obsOf_measurement]
  · unfold _root_.MIPStarRE.QPBT.pauliMagicMeasurement
    rw [_root_.MIPStarRE.QPBT.msStrategyMeasurement_var_bit]
    change _root_.MIPStarRE.QPBT.reflectionEffect
        (_root_.MIPStarRE.QPBT.heteroKron
          (_root_.MIPStarRE.QPBT.obsOf (_root_.MIPStarRE.QPBT.pauliTraceMeasurement P .Z (_root_.MIPStarRE.QPBT.pauliZBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z)))
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ZMod 2))) b = _
    rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.reflectionEffect_heteroKron_left,
      _root_.MIPStarRE.QPBT.reflectionEffect_obsOf_measurement]
