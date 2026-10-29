-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.sum_stateQForm_reverse_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:32:48.109923+00:00
-- url     : https://prove2.me/submissions/2f9faa9e-468a-4e29-a3bb-3f7efe923efa

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.sum_stateQForm_reverse_eq.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Theorems.Thm_MIPStarRE_QPBT_outcomeWeight_sum_eq_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

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

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean. -/
/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ex:easy-but-long`).

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

/-! ## Contractions and their action on states -/



































/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/

/-- Tensor placement distributes over a finite sum in the left factor. -/
theorem heteroKron_finset_sum_left {β ιA ιB : Type*} (s : Finset β)
    (A : β → _root_.LIDT.MIPStarRE.Quantum.Op ιA) (C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (∑ b ∈ s, A b) C = ∑ b ∈ s, _root_.MIPStarRE.QPBT.heteroKron (A b) C :=
  _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left s A C

/-- Tensor placement distributes over a finite sum in the right factor. -/
theorem heteroKron_finset_sum_right {β ιA ιB : Type*} (s : Finset β)
    (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (C : β → _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron A (∑ b ∈ s, C b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.heteroKron A (C b) :=
  _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right s A C

/-- The state quadratic form is additive over finite sums. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) :=
  _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum ψ s M



/-! ## Matrices of isometries -/





















/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

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



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Cell consistency of the postprocessed effects -/

theorem solution (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (i : Fin 6) (k : Fin 3) :
    ∑ b : ZMod 2, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.ψ (_root_.MIPStarRE.QPBT.heteroKron
        (((S.A (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k))).postprocess _root_.MIPStarRE.QPBT.msBitOrZero).effect b)
        (((S.B (.constraint i)).postprocess (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k)).effect b)) =
      1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.reverseCellMismatchMass S i k := by
  classical
  have hterm : ∀ b : ZMod 2, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.ψ (_root_.MIPStarRE.QPBT.heteroKron
        (((S.A (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k))).postprocess _root_.MIPStarRE.QPBT.msBitOrZero).effect b)
        (((S.B (.constraint i)).postprocess (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k)).effect b)) =
      ∑ a : _root_.MIPStarRE.QPBT.msGame.AnswerA, ∑ c : _root_.MIPStarRE.QPBT.msGame.AnswerB,
        if _root_.MIPStarRE.QPBT.msBitOrZero a = b then
          (if _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k c = b then
            _root_.MIPStarRE.QPBT.outcomeWeight S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) (.constraint i) a c else 0)
        else 0 := by
    intro b
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_finset_sum_left, _root_.MIPStarRE.QPBT.MagicSquareRigidity.stateQForm_finset_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_finset_sum_right, _root_.MIPStarRE.QPBT.MagicSquareRigidity.stateQForm_finset_sum, Finset.sum_filter]
      rfl
    · simp
  have htotal := _root_.MIPStarRE.QPBT.outcomeWeight_sum_eq_one S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) (.constraint i)
  unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.reverseCellMismatchMass _root_.MIPStarRE.QPBT.outcomeEventWeight
  simp_rw [hterm]
  rw [Finset.sum_comm, eq_sub_iff_add_eq, ← htotal, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  by_cases h : _root_.MIPStarRE.QPBT.msBitOrZero a = _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k c
  · simp [h]
  · simp [h, Ne.symm h]
