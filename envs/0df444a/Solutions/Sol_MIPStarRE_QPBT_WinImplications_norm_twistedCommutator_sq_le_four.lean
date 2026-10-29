-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.norm_twistedCommutator_sq_le_four
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:45:52.036468+00:00
-- url     : https://prove2.me/submissions/311d58ef-91ab-48e6-b0e4-440f8ba54205

-- Generated proof for MIPStarRE.QPBT.WinImplications.norm_twistedCommutator_sq_le_four.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_CommutingObs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_PointObs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_TwistedCommutation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

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

/-- The tensor placement respects the adjoint. Formalization-only support for
`fact:add-a-proj`, blueprint `ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_conjTranspose {ιA ιB : Type*} (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    (_root_.MIPStarRE.QPBT.heteroKron A B)ᴴ = _root_.MIPStarRE.QPBT.heteroKron Aᴴ Bᴴ := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.conjTranspose_apply]

/-- Placing an isometry on the first factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_left_isometry {ιA ιB : Type*} [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB] (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA)
    (hA : Aᴴ * A = 1) :
    (_root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB))ᴴ * _root_.MIPStarRE.QPBT.heteroKron A 1 = 1 := by
  rw [_root_.MIPStarRE.QPBT.WinImplications.heteroKron_conjTranspose, _root_.MIPStarRE.QPBT.heteroKron_mul, hA, Matrix.conjTranspose_one,
    one_mul, _root_.MIPStarRE.QPBT.heteroKron_one_one]







/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/





















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

/- Source helpers from QPBT/Observables/WinImplications/PointObs.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyPointObs
/-!
# Self-consistency of the strategy point observables

This module converts the trace-coarse-grained point consistency of item 1 of
`lem:qld-win-implications` into the observable relation
`eq:pts-obs-consistency` of `lem:qld-win-implications-obs`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:294-308`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications



/-! ## Linearity of the tensor placement -/





/-- The binary phase character has unit modulus. Paper
`references/qpbt-paper/04_preliminaries.tex:1052-1081`. -/
theorem norm_phaseSign (t : ZMod 2) : ‖_root_.MIPStarRE.QPBT.phaseSign t‖ = 1 := by
  by_cases ht : t = 0 <;> simp [_root_.MIPStarRE.QPBT.phaseSign, ht]

/-! ## The point observable as a binary observable -/



/-! ## Trace-coarse-grained point self-consistency -/







/-! ## The observable consistency relation -/



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

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Transfer.lean. -/
/-!
# Transfer of rigidity bounds along the projective dilation

The self-testing argument behind `thm:ms-rigidity` is carried out for the
projective dilation `msDilatedStrategy S` of an arbitrary Magic Square strategy
`S`.  Its conclusions are state-dependent bounds for the *dilated* projectors,
conjugated by local isometries `φ_A`, `φ_B` out of the enlarged local spaces.
The witness for the original strategy is obtained by composing these isometries
with the ground embeddings, and the operators appearing in its bounds are the
conjugates of the *original* effects, that is, of the compressions `Π P Π` of
the dilated projectors `P` to the ground slice (`Π` the ground projection).

Naimark dilation preserves Born probabilities but not state-dependent `≈_δ`
estimates in general (`references/ldt-paper/orthonormalization.tex:82-101`,
blueprint `ex:easy-but-long`), so `Π P Π` and `P` need not act
alike on the dilated state.  Their difference on the dilated state `ψ'` is the
*leakage* `(1 - Π) P ψ'` of `P` out of the ground slice, and the point of this
file is that in the Magic Square game this leakage is controlled by the
cell-consistency defect of the value-to-parity layer: the dilated effect
`P ⊗ 1` almost agrees with the partner effect `1 ⊗ Q` on the other side, and
`(1 - Π) ⊗ 1` annihilates `1 ⊗ Q ψ'`.  Combined with the closeness of
`(φ_A ⊗ φ_B) ψ'` to the ideal state and the fact that all operators involved
are contractions, this pulls every bound of `thm:ms-rigidity` back from the
dilated strategy to the original one with explicit constants.

## Main statements

* `ms_effect_transfer_A`, `ms_effect_transfer_B`: the bit-measurement distances
  of the original strategy are bounded by three times those of the dilated
  strategy plus `216 ε + 24 η²`, where `η` bounds the state closeness.
* `ms_anticommutator_transfer_A`, `ms_anticommutator_transfer_B`: the
  anticommutator defects transfer with the bound `3 · (dilated) + 15552 ε +
  48 η²`.
* `ms_state_transfer`: the state closeness is unchanged.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Cell consistency of the postprocessed effects -/





/-! ## The dilated effects on the enlarged ground spaces -/









/-! ## Compressions of the dilated postprocessed effects -/

















/-! ## Transfer of the effect estimates -/















/-! ## Transfer of the anticommutator estimates -/



/-- The action on states respects differences of operators. -/
theorem applyOperatorToState_sub_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (M - N) v =
      _root_.MIPStarRE.QPBT.applyOperatorToState M v - _root_.MIPStarRE.QPBT.applyOperatorToState N v := by
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]





























end

end MIPStarRE.QPBT.MagicSquareRigidity

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



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications



/-! ## The unconditional bound on a difference of reflections -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyTwisted

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {ιL ιR : Type} [Fintype ιL] [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR]
    (OX OZ : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.LIDT.MIPStarRE.Quantum.Op ιL) (χ : EuclideanSpace ℂ (ιL × ιR))
    (hχ : ‖χ‖ = 1) (hOX : ∀ ω, (OX ω)ᴴ * OX ω = 1)
    (hOZ : ∀ ω, (OZ ω)ᴴ * OZ ω = 1) (ω : _root_.MIPStarRE.QPBT.PauliTuple P) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
          _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
            _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ ^ 2 ≤ 4 := by
  have hXZ := _root_.MIPStarRE.QPBT.WinImplications.heteroKron_left_isometry (ιB := ιR) (OX ω * OZ ω)
    (_root_.MIPStarRE.QPBT.WinImplications.mul_conjTranspose_mul_self (hOX ω) (hOZ ω))
  have hZX := _root_.MIPStarRE.QPBT.WinImplications.heteroKron_left_isometry (ιB := ιR) (OZ ω * OX ω)
    (_root_.MIPStarRE.QPBT.WinImplications.mul_conjTranspose_mul_self (hOZ ω) (hOX ω))
  have h1 : ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ = 1 := by
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_of_isometry hXZ]
    exact hχ
  have h2 : ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
        _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ = 1 := by
    rw [_root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_smul_op, norm_smul, _root_.MIPStarRE.QPBT.WinImplications.norm_phaseSign,
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_of_isometry hZX, hχ, one_mul]
  have hsub : ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
        _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ ≤ 2 := by
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub_op]
    calc
      _ ≤ ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ +
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
              _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  nlinarith [hsub, norm_nonneg (_root_.MIPStarRE.QPBT.applyOperatorToState
    (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
      _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
        _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ)]
