-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.retainedPointMismatch_le_ordered_error
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:57:06.787986+00:00
-- url     : https://prove2.me/submissions/80c427f7-0c71-477b-8c8c-8f8d47359222

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.retainedPointMismatch_le_ordered_error.
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
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_RetainedPointMass
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_RoundedPolynomialEstimates
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_ScalarPolynomial
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_PolynomialImageBounds
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_directCombinedEmbedding_read
import Theorems.Thm_MIPStarRE_QPBT_PolynomialImageBounds_point_mismatch_le_ordered_error
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_conjTranspose
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_mul

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

/- Source helpers from QPBT/Combining/ExtendedLineGame/ScalarNonlinearMass.lean. -/
/-!
# Scalar-nonlinear mass of the actual rounded measurements

The full polynomial-outcome ordered estimate is composed with the concentration
bound for scalar-nonlinear outcomes. Opposite placements commute; no symmetry of the
player spaces is required. Projectivity retains the actual outcome masses.

## References

`eq:qld-g-42`, `eq:qld-g-prime`, and `eq:qld-g-prime-bound`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1283-1326`.
This is only scalar-linearity concentration; the variable-separation estimates
and retained overlaps are separate results.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section

namespace ExtendedLineGame





/-- Opposite placements commute, identifying the residual on the actual
projected state with the ordered-error residual. This supports both orders
of `eq:qld-g-42/43` and blueprint `lem:qld-4-7`. -/
theorem placed_residual {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopposite : p1.IsOpposite p2)
    (R : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p1.side)) (T : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p2.side)) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (S.place p1 R) S.psiHat -
      _root_.MIPStarRE.QPBT.applyOperatorToState (S.place p2 T)
        (_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p1 R) S.psiHat) =
      _root_.MIPStarRE.QPBT.applyOperatorToState (S.place p1 R * (1 - S.place p2 T)) S.psiHat := by
  rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, ← S.place_comm p1 p2 hopposite R T, mul_sub, mul_one]
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply]












end ExtendedLineGame

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLineGame/WrongVariableMass.lean. -/
/-!
# Wrong-variable mass of rounded polynomial outcomes

The two block orders use the actual projected state vectors and the full
ordered-error sum. A common exceptional coefficient controls all outcomes
of the fixed-block measurement before their weights are summed.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1328-1368`,
`eq:qld-g-separable`, `eq:qld-g-48`, `eq:qld-g-2`, and the two wrong-variable
mass bounds. This supports blueprint `lem:qld-4-7`; it does not establish
the subsequent retained overlaps or global polynomial-pair witness.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section

namespace ExtendedLineGame



/-- Exact placement and order transport for the common joint scalar sample.
This also transports the retained-overlap calculation in `lem:qld-4-7`. -/
theorem placed_fiber_orderedIndicator {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement) (reverse : Bool)
    (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (v : Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator
      (S.placedMeasurement p (S.pointMeasExp p.side (if reverse then .Z else .X) x))
      (S.placedMeasurement p (S.pointMeasExp p.side (if reverse then .X else .Z) z))
      (v 0) (v 1) a =
    let y := _root_.MIPStarRE.QPBT.ExtendedLineGame.fiberQuestionEquiv P reverse ((z, x), v)
    S.place p (∑ ab ∈ Finset.univ.filter (fun ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P =>
        y.2.1 * ab.1 + y.2.2 * ab.2 = a),
      if reverse then
        (S.pointMeasExp p.side .Z y.1.2).effect ab.2 *
          (S.pointMeasExp p.side .X y.1.1).effect ab.1
      else
        (S.pointMeasExp p.side .X y.1.1).effect ab.1 *
          (S.pointMeasExp p.side .Z y.1.2).effect ab.2) := by
  dsimp only
  rw [S.place_finsetSum, Finset.sum_filter]
  simp only [_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator, _root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect]
  cases reverse
  · simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.fiberQuestionEquiv, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul]
  · apply Fintype.sum_equiv (Equiv.prodComm (_root_.MIPStarRE.QPBT.PauliScalar P) (_root_.MIPStarRE.QPBT.PauliScalar P))
    intro ab
    simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.fiberQuestionEquiv, add_comm, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul]



























end ExtendedLineGame

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Points/PlacementSupport.lean. -/
/-!
# Placement calculus on the expanded state

This module records the algebra of the four register placements used by the
combining argument: a placement is a unital `*`-homomorphism, placements on
opposite register pairs commute, and the crosswise exchange of the two EPR
pairs of the expanded state carries the placement `AA'` to `AB''` and `BA''`
to `BB'` while fixing the expanded state.  The last fact transfers every
state-dependent distance between the two bipartition schemes of
`def:symmetric-equivalents` without assuming a symmetric strategy.

## References

The placements are those of `def:symmetric-equivalents`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
placement module proves EPR-exchange invariance for the involution
`(A' B'')(A'' B')`, which fixes `A` and `B`, in
`ProjectiveSetting.reindexState_eprCrossSwap_psiHat`; its use for
`lem:qld-4-10` is analyzed in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## Placements as reindexed tensor factors -/













/-! ## The placement is a unital `*`-homomorphism -/





















/-- A placed projective measurement is projective. -/
theorem placedMeasurement_isProjective (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (p : _root_.MIPStarRE.QPBT.Placement) {α : Type*} [Fintype α]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p.side))
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (S.placedMeasurement p M) := by
  intro a
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · change S.place p (M.effect a) * S.place p (M.effect a) =
      S.place p (M.effect a)
    rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul, (hM a).isIdempotentElem.eq]
  · change star (S.place p (M.effect a)) = S.place p (M.effect a)
    rw [Matrix.star_eq_conjTranspose, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_conjTranspose,
      (hM a).isSelfAdjoint.isHermitian.eq]

end ProjectiveSetting

end

end MIPStarRE.QPBT

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









/-- The quadratic form of the identity is the squared vector norm. -/
theorem stateQForm_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) = ‖ψ‖ ^ 2 := by
  have hone : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ψ = ψ := by
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, hone]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) ψ)





















































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

/- Source helpers from QPBT/Combining/PolynomialImageBounds.lean. -/
/-!
# Indicator-weighted ordered products

This module proves the local norm calculation in `eq:qld-g-prime`. The state
vector is not assumed normalized: its squared norm controls the exceptional
coefficient, so the estimate can be summed over all polynomial outcomes.
The measurements act on an arbitrary finite space, which includes either
player's placed expanded measurements.

The coefficient-polynomial argument also bounds mass outside the scalar-linear
image, with its actual ordered-correlation error displayed in the conclusion.
These are auxiliary estimates, not the global polynomial-pair construction.
The remaining block-separation and construction obligations are recorded in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex` and issue Dengnifer/MIPStarRE-QPBT-bak#513.

Only the dependency chain needed for these estimates is exposed; supporting
lemmas remain private.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1289-1326`,
  especially `eq:qld-g-42`, `eq:qld-g-43`, and `eq:qld-g-prime`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace PolynomialImageBounds

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]





















/-- Completeness and projectivity preserve total squared state mass. This is
the normalization used after summing `eq:qld-g-prime` over polynomial labels. -/
theorem sum_projective_state_norm_sq {Γ : Type*} [Fintype Γ]
    (S : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ι) (hS : _root_.MIPStarRE.QPBT.Measurement.IsProjective S)
    (ψ : EuclideanSpace ℂ ι) :
    ∑ g : Γ, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.effect g) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  simp_rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian,
    fun g => (hS g).isIdempotentElem.eq]
  change (∑ g : Γ, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (S.effect g)) = ‖ψ‖ ^ 2
  rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, S.sum_eq_one, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one]

























end PolynomialImageBounds

end

end MIPStarRE.QPBT

/-!
# Retained point mismatch on the faithful combining image

The outcome sum ranges over the actual bounded polynomial-pair embedding.
The projected vectors and both heterogeneous placements are preserved.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1360-1404`,
`eq:qld-s-good-and-bad` through `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/



open scoped BigOperators MatrixOrder

open MIPStarRE.QPBT.ExtendedLineGame

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus MIPStarRE.QPBT.PolynomialImageBounds

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopposite : p1.IsOpposite p2)
    (R : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : _root_.MIPStarRE.QPBT.Measurement.IsProjective R) (reverse : Bool) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.retainedPointMismatch S p1 p2 R (if reverse then .Z else .X) ≤
      2 * _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError S p1 p2 R reverse + 4 / P.q := by
  classical
  let ψ := fun g => _root_.MIPStarRE.QPBT.applyOperatorToState (S.place p1 (R.effect g)) S.psiHat
  let X := fun x : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P => S.placedMeasurement p2
    (S.pointMeasExp p2.side (if reverse then .Z else .X) x)
  let Z := fun z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P => S.placedMeasurement p2
    (S.pointMeasExp p2.side (if reverse then .X else .Z) z)
  let A := fun (z x : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (v : Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P) g =>
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator (X x) (Z z) (v 0) (v 1)
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P (_root_.MIPStarRE.QPBT.ExtendedLineGame.fiberQuestionEquiv P reverse ((z, x), v)) g)) (ψ g)
  have hmass : ∑ g, ‖ψ g‖ ^ 2 = 1 := by
    simpa only [ψ, _root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] using
      _root_.MIPStarRE.QPBT.PolynomialImageBounds.sum_projective_state_norm_sq (S.placedMeasurement p1 R)
        (S.placedMeasurement_isProjective p1 R hR) S.psiHat
  have hretained : ∑ pair, ‖ψ (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair)‖ ^ 2 ≤ 1 := by
    rw [← hmass, ← Finset.sum_image (f := fun g => ‖ψ g‖ ^ 2) (fun a _ b _ h =>
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P).injective h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intros; exact sq_nonneg _)
  have hread (z x : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (v : Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P)
      (pair : _root_.MIPStarRE.QPBT.PolyPair P) :
      _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P (_root_.MIPStarRE.QPBT.ExtendedLineGame.fiberQuestionEquiv P reverse ((z, x), v))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair) =
      v 0 * _root_.MIPStarRE.QPBT.evalAt (if reverse then .Z else .X) x pair +
        v 1 * _root_.MIPStarRE.QPBT.evalAt (if reverse then .X else .Z) z pair := by
    rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding_read]
    cases reverse <;> simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.fiberQuestionEquiv, finTwoArrowEquiv, add_comm]
  have hpoint (z x : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
      (∑ pair : _root_.MIPStarRE.QPBT.PolyPair P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (1 - (X x).effect (_root_.MIPStarRE.QPBT.evalAt (if reverse then .Z else .X) x pair))
          (ψ (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair))‖ ^ 2) ≤
      2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun v =>
        ∑ g, ‖ψ g - A z x v g‖ ^ 2) + 4 / P.q := by
    have h (pair : _root_.MIPStarRE.QPBT.PolyPair P) := _root_.MIPStarRE.QPBT.PolynomialImageBounds.point_mismatch_le_ordered_error (X x) (Z z)
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      (_root_.MIPStarRE.QPBT.evalAt (if reverse then .Z else .X) x pair)
      (_root_.MIPStarRE.QPBT.evalAt (if reverse then .X else .Z) z pair) (ψ (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair))
    simp_rw [← hread z x] at h
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun pair _ => h pair)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← _root_.LIDT.MIPStarRE.LDT.avgOver_sum] at hs
    have herr : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun v =>
        ∑ pair, ‖ψ (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair) -
          A z x v (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair)‖ ^ 2) ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun v =>
        ∑ g, ‖ψ g - A z x v g‖ ^ 2) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      intro v
      rw [← Finset.sum_image (f := fun g => ‖ψ g - A z x v g‖ ^ 2)
        (fun a _ b _ h => (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P).injective h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intros; exact sq_nonneg _)
    have hcard : Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) = P.q :=
      @_root_.LIDT.MIPStarRE.LDT.FieldModel.card P.q P.model.toFieldModel
    have hc := mul_le_mul_of_nonneg_left hretained
      (show 0 ≤ 4 * (Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) : ℝ)⁻¹ by positivity)
    rw [hcard, mul_one] at hc
    change _ ≤ 2 * _ + 4 * (Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) : ℝ)⁻¹ * _ at hs
    rw [hcard] at hs
    change _ ≤ 2 * _root_.LIDT.MIPStarRE.LDT.avgOver _ (fun v => ∑ pair,
      ‖ψ (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair) - A z x v (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair)‖ ^ 2) +
      4 * (P.q : ℝ)⁻¹ * _ at hs
    rw [div_eq_mul_inv]
    linarith
  have hfull :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun z =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun v =>
            ∑ g, ‖ψ g - A z x v g‖ ^ 2))) =
        _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError S p1 p2 R reverse := by
    rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (fun z x =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun v =>
        ∑ g, ‖ψ g - A z x v g‖ ^ 2))]
    rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod
      (fun zx : (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) =>
        fun v => ∑ g, ‖ψ g - A zx.1 zx.2 v g‖ ^ 2)]
    unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (_root_.MIPStarRE.QPBT.ExtendedLineGame.fiberQuestionEquiv P reverse).symm]
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    rintro ⟨⟨z, x⟩, v⟩
    apply Finset.sum_congr rfl
    intro g _
    dsimp only [A, X, Z]
    rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.placed_fiber_orderedIndicator]
    dsimp only [ψ]
    rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.placed_residual S p1 p2 hopposite]
    rfl
  have h := _root_.LIDT.MIPStarRE.LDT.avgOver_mono (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) _ _ fun z =>
    _root_.LIDT.MIPStarRE.LDT.avgOver_mono (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) _ _ (hpoint z)
  simp only [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul, hfull] at h
  exact h
