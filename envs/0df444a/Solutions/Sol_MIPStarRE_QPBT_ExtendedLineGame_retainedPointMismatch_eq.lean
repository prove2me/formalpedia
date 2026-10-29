-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.retainedPointMismatch_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:12:57.068971+00:00
-- url     : https://prove2.me/submissions/f2bcb14a-621f-4c17-a3d0-669a3a47ded9

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.retainedPointMismatch_eq.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
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
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
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

/- Source helpers from QPBT/Combining/ExtendedLineGame/PairMeasurement.lean. -/
/-!
# Transport of the polynomial-pair completion

The actual singleton outcomes are transported by the canonical field
equivalence before applying the algebraic completion.
Every original outcome is retained, including those outside the combining image.

## References

Paper `eq:qld-sgg-completeness` and the completion paragraph of `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.ExtendedLineGame

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section















/-- The faithful image predicate is exactly membership in the actual pair embedding. -/
theorem mem_range_directCombinedEmbedding (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (g : _root_.MIPStarRE.QPBT.DirectPolyTuple P.extendedDirectLd) :
    g ∈ Set.range (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P) ↔
      ∃ pair : _root_.MIPStarRE.QPBT.PolyPair P,
        MvPolynomial.map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1 =
          _root_.MIPStarRE.QPBT.combinePoly pair.1.1 pair.2.1 := by
  constructor
  · rintro ⟨pair, rfl⟩
    refine ⟨pair, ?_⟩
    exact congrArg Subtype.val ((_root_.MIPStarRE.QPBT.ExtendedLineGame.directPolynomialEquiv P).apply_symm_apply
      (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P pair))
  · rintro ⟨pair, hp⟩
    refine ⟨pair, ?_⟩
    apply (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPolynomialEquiv P).injective
    exact ((_root_.MIPStarRE.QPBT.ExtendedLineGame.directPolynomialEquiv P).apply_symm_apply _).trans (Subtype.ext hp.symm)



end

end MIPStarRE.QPBT.ExtendedLineGame

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

/-- The quadratic form of `Wᴴ M W` in `ψ` is the quadratic form of `M` in
`W ψ`.  This is the conjugation identity behind the placed-sandwich
rewritings: conjugating transfers the outer operator to the state vector.
It is formalization-only auxiliary content, shared by the overlap-gap estimate
and the sandwich self-consistency argument. -/
theorem stateQForm_conjTranspose_mul_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (W M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Wᴴ * M * W) = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState W ψ) M := by
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  congr 1
  change inner ℂ ψ (Matrix.toEuclideanLin Wᴴ _) =
    inner ℂ (Matrix.toEuclideanLin W ψ) _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]



















































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

/- Source helpers from QPBT/Combining/OverlapGap.lean. -/
/-!
# Replacing one factor of a measurement-weighted overlap

The scalar estimates used to combine the two Pauli bases compare averaged
overlaps whose left factor is one complete measurement and whose right factors
are operator families at small state-dependent distance.  This module records
the corresponding Cauchy--Schwarz estimate.  The right-hand families are
arbitrary, so the estimate covers an ordered product of point effects, which
is not itself a measurement.

## References

The estimate is `lem:overlap-gap-distance` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; it is the Cauchy--Schwarz
step at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1147-1166`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## The Cauchy--Schwarz inequality weighted by a positive operator -/







/-! ## Quadratic forms against projections -/



/-- For a projection `B` commuting with `A`, the quadratic form of `A` in
`B ψ` is the quadratic form of `A B` in `ψ`. -/
theorem stateQForm_applyOperatorToState_eq_of_isProj {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) {A B : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hB : _root_.LIDT.MIPStarRE.Quantum.IsProj B)
    (hAB : Commute A B) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState B ψ) A = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A * B) := by
  rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_conjTranspose_mul_mul, hB.isSelfAdjoint.isHermitian.eq,
    ← hAB.eq, mul_assoc, hB.isIdempotentElem.eq]







/-! ## Replacing a factor under the weight of a measurement -/











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





private theorem retained_mass_eq {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement)
    (R : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p.side))
    (hR : _root_.MIPStarRE.QPBT.Measurement.IsProjective R) :
    (∑ pair : _root_.MIPStarRE.QPBT.PolyPair P,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p (R.effect (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair)))
        S.psiHat‖ ^ 2) = 1 - _root_.MIPStarRE.QPBT.ExtendedLineGame.separatedPolynomialMass S p R := by
  classical
  let w := fun g => ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p (R.effect g)) S.psiHat‖ ^ 2
  have hmass : ∑ g, w g = 1 := by
    simpa only [w, _root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] using
      _root_.MIPStarRE.QPBT.PolynomialImageBounds.sum_projective_state_norm_sq (S.placedMeasurement p R)
        (S.placedMeasurement_isProjective p R hR) S.psiHat
  have hgood : Finset.univ.image (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P) =
      Finset.univ.filter (fun g => ∃ pair : _root_.MIPStarRE.QPBT.PolyPair P,
        MvPolynomial.map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1 =
          _root_.MIPStarRE.QPBT.combinePoly pair.1.1 pair.2.1) := by
    ext g
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    exact _root_.MIPStarRE.QPBT.ExtendedLineGame.mem_range_directCombinedEmbedding P g
  change (∑ pair, w (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair)) = _
  rw [← Finset.sum_image (f := w) (fun a _ b _ h =>
    (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P).injective h), hgood]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun g => ∃ pair : _root_.MIPStarRE.QPBT.PolyPair P,
      MvPolynomial.map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1 =
        _root_.MIPStarRE.QPBT.combinePoly pair.1.1 pair.2.1) w
  rw [hmass] at hsplit
  exact eq_sub_of_add_eq hsplit


















end

end MIPStarRE.QPBT.ExtendedLineGame

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
    (hR : _root_.MIPStarRE.QPBT.Measurement.IsProjective R) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.retainedPointMismatch S p1 p2 R W =
      1 - _root_.MIPStarRE.QPBT.ExtendedLineGame.separatedPolynomialMass S p1 R - _root_.MIPStarRE.QPBT.ExtendedLineGame.retainedPointOverlap S p1 p2 R W := by
  have hpoint (x : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (pair : _root_.MIPStarRE.QPBT.PolyPair P) :
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (1 - S.place p2 ((S.pointMeasExp p2.side W x).effect (_root_.MIPStarRE.QPBT.evalAt W x pair)))
        (_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p1 (R.effect (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair)))
          S.psiHat)‖ ^ 2 =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p1 (R.effect (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair)))
        S.psiHat‖ ^ 2 - _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          (S.place p1 (R.effect (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair)) *
            S.place p2 ((S.pointMeasExp p2.side W x).effect (_root_.MIPStarRE.QPBT.evalAt W x pair))) := by
    have hM := S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ W x)
      (_root_.MIPStarRE.QPBT.evalAt W x pair)
    have hG := S.placedMeasurement_isProjective p1 R hR (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair)
    simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect] at hM hG
    have hcomm := S.place_comm p1 p2 hopposite
      (R.effect (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair))
      ((S.pointMeasExp p2.side W x).effect (_root_.MIPStarRE.QPBT.evalAt W x pair))
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq]
    change _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm _ _ = _
    have hsub (ψ : EuclideanSpace ℂ (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB))
        (A B : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A - B) = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ A - _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ B := by
      simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
    rw [hM.one_sub.isSelfAdjoint.isHermitian.eq, hM.one_sub.isIdempotentElem.eq,
      hsub, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one,
      _root_.MIPStarRE.QPBT.stateQForm_applyOperatorToState_eq_of_isProj S.psiHat hG hcomm.symm, hcomm]
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.retainedPointMismatch _root_.MIPStarRE.QPBT.ExtendedLineGame.retainedPointOverlap
  simp_rw [hpoint, Finset.sum_sub_distrib, _root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
  rw [retained_mass_eq S p1 R hR]
