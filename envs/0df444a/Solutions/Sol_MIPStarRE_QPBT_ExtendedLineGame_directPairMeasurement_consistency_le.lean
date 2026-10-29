-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement_consistency_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:53:00.086574+00:00
-- url     : https://prove2.me/submissions/fc3e1810-440f-4142-a154-5ab823cfb797

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement_consistency_le.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_PairMeasurement
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_PairPointConsistency
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_RetainedPointMass
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_WrongVariableMass
import Definitions.Def_QPBT_QPBT_Combining_PairCompletion
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Submeasurement_total_le_one
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_retainedPointMismatch_eq
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_completedPairMeasurement_effect

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
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.PolynomialImageBounds
end MIPStarRE.QPBT.PolynomialImageBounds
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/ExtendedLineGame/PairPointConsistency.lean. -/
/-!
# Point consistency of the completed polynomial-pair measurements

The polynomial-pair completion is applied to the actual rounded outcomes. Its missing
mass and retained point mismatch are kept separate until the final bound.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`,
`eq:qld-sgg-completeness` and `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.ExtendedLineGame

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section

private theorem place_add {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement)
    (A B : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)) :
    S.place p (A + B) = S.place p A + S.place p B := by
  ext i j
  cases p <;> simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.add_apply, add_mul, mul_add]






















end

end MIPStarRE.QPBT.ExtendedLineGame

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

/-- A positive semidefinite operator has nonnegative state quadratic form. This
is the formalization-only order fact `lem:distance-qform-nonnegative`, used for
the nonnegative overlap terms in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {M : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hM : 0 ≤ M) :
    0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  calc
    0 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ 0 := by simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
    _ ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hM ψ

/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the state quadratic form is additive in its operator. -/
theorem stateQForm_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M + N) = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M + _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ N := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]























/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rfl



































end MIPStarRE.QPBT.DistanceCalculus

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





/-! ## The action of a placement on the expanded state -/

/-- The expanded state is the shuffle of the coordinate tensor of the strategy
state with the two EPR ancillas. This is `eq:def-psihat`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`ch14_qpbt_observables.tex:895-918`. -/
theorem psiHat_eq_reindexState (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    S.psiHat = _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.vecTensor S.toStrategy.ψ (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))) := rfl

/-- The expanded strategy state is normalized. -/
theorem psiHat_norm (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : ‖S.psiHat‖ = 1 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_eq_reindexState, _root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.vecTensor_norm_eq,
    _root_.MIPStarRE.QPBT.vecTensor_norm_eq, S.toStrategy.ψ_norm, _root_.MIPStarRE.QPBT.eprState_norm]
  norm_num

/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/



























end ProjectiveSetting

end

end MIPStarRE.QPBT

/-!
# Point consistency of the completed polynomial-pair measurements

The polynomial-pair completion is applied to the actual rounded outcomes. Its missing
mass and retained point mismatch are kept separate until the final bound.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`,
`eq:qld-sgg-completeness` and `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/



open scoped BigOperators MatrixOrder

open MIPStarRE.QPBT.ExtendedLineGame

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus MIPStarRE.QPBT.PolynomialImageBounds

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopposite : p1.IsOpposite p2)
    (R : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : _root_.MIPStarRE.QPBT.Measurement.IsProjective R) (pair₀ : _root_.MIPStarRE.QPBT.PolyPair P) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
      (fun x a => S.place p1 (((_root_.MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement R pair₀).postprocess
        (_root_.MIPStarRE.QPBT.evalAt W x)).effect a))
      (fun x a => S.place p2 ((S.pointMeasExp p2.side W x).effect a)) S.psiHat ≤
      _root_.MIPStarRE.QPBT.ExtendedLineGame.separatedPolynomialMass S p1 R + _root_.MIPStarRE.QPBT.ExtendedLineGame.retainedPointMismatch S p1 p2 R W := by
  classical
  let C := _root_.MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement R pair₀
  let B := fun x => S.pointMeasExp p2.side W x
  have hdiag (x : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
      (∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place p1 ((C.postprocess (_root_.MIPStarRE.QPBT.evalAt W x)).effect a) * S.place p2 ((B x).effect a))) =
      ∑ pair : _root_.MIPStarRE.QPBT.PolyPair P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place p1 (C.effect pair) * S.place p2 ((B x).effect (_root_.MIPStarRE.QPBT.evalAt W x pair))) := by
    simp_rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, S.place_finsetSum, Finset.sum_mul,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    calc
      _ = ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, ∑ pair ∈ Finset.univ.filter
          (fun pair => _root_.MIPStarRE.QPBT.evalAt W x pair = a), _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          (S.place p1 (C.effect pair) * S.place p2 ((B x).effect (_root_.MIPStarRE.QPBT.evalAt W x pair))) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro pair hp
        rw [(Finset.mem_filter.mp hp).2]
      _ = _ := Finset.sum_fiberwise Finset.univ (_root_.MIPStarRE.QPBT.evalAt W x) _
  have hretained (x : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
      (∑ pair : _root_.MIPStarRE.QPBT.PolyPair P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place p1 (R.effect (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair)) *
          S.place p2 ((B x).effect (_root_.MIPStarRE.QPBT.evalAt W x pair)))) ≤
      ∑ pair : _root_.MIPStarRE.QPBT.PolyPair P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place p1 (C.effect pair) * S.place p2 ((B x).effect (_root_.MIPStarRE.QPBT.evalAt W x pair))) := by
    apply Finset.sum_le_sum
    intro pair _
    dsimp only [C, _root_.MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement]
    rw [_root_.MIPStarRE.QPBT.completedPairMeasurement_effect, place_add, add_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_add]
    have heffect : (_root_.MIPStarRE.QPBT.combinedPairSubmeasurement P
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.canonicalPolynomialMeasurement R)).effect pair =
        R.effect (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair) :=
      _root_.MIPStarRE.QPBT.ExtendedLineGame.canonicalPolynomialMeasurement_effect R (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P pair)
    rw [heffect]
    apply le_add_of_nonneg_right
    apply _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg
    apply Commute.mul_nonneg
    · apply S.place_nonneg
      split_ifs
      · exact sub_nonneg.mpr (_root_.MIPStarRE.QPBT.combinedPairSubmeasurement P
          (_root_.MIPStarRE.QPBT.ExtendedLineGame.canonicalPolynomialMeasurement R)).total_le_one
      · exact le_rfl
    · exact S.place_nonneg p2 ((B x).pos _)
    · exact S.place_comm p1 p2 hopposite _ _
  have hbound : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
      (fun x a => S.place p1 ((C.postprocess (_root_.MIPStarRE.QPBT.evalAt W x)).effect a))
      (fun x a => S.place p2 ((B x).effect a)) S.psiHat ≤
      1 - _root_.MIPStarRE.QPBT.ExtendedLineGame.retainedPointOverlap S p1 p2 R W := by
    unfold _root_.MIPStarRE.QPBT.consistencyDefect
    simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm]
    have heq (x : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq
      (S.placedMeasurement p1 (C.postprocess (_root_.MIPStarRE.QPBT.evalAt W x)))
      (S.placedMeasurement p2 (B x)) S.psiHat
    simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] at heq
    simp_rw [heq, hdiag]
    have h := _root_.LIDT.MIPStarRE.LDT.avgOver_mono (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) _ _
      (fun x => sub_le_sub_left (hretained x) 1)
    simpa only [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const, _root_.MIPStarRE.QPBT.ExtendedLineGame.retainedPointOverlap, B] using h
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.retainedPointMismatch_eq S p1 p2 hopposite R hR W]
  linarith
