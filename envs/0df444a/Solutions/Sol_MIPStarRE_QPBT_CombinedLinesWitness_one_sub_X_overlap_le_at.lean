-- Prove2me | solution 1 for MIPStarRE.QPBT.CombinedLinesWitness.one_sub_X_overlap_le_at
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:10:09.759969+00:00
-- url     : https://prove2.me/submissions/3d62dee8-99a0-41f1-9a8d-158e587cf310

-- Generated proof for MIPStarRE.QPBT.CombinedLinesWitness.one_sub_X_overlap_le_at.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Combining_ZEvalDeficit
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_conjTranspose
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_mul
import Theorems.Thm_MIPStarRE_QPBT_one_sub_overlap_le_of_consistencyDefect

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

/- Source helpers from QPBT/Combining/Lines/ConsistencyPositivity.lean. -/
/-!
# Positivity of the consistency defect on opposite placements

The error-inflation estimates for restricted line distributions apply to
nonnegative averages.  This module supplies the missing nonnegativity: the
integrand of `consistencyDefect` for two complete measurements placed on
opposite registers is a state quadratic form of a positive operator.  Indeed,
after separating the two placements along the corresponding tensor
bipartition, the off-diagonal sum is
`∑_a (place p₁ E_a) (place p₂ (∑_{b ≠ a} F_b))`, a sum of products of
positive operators supported on complementary registers.  The placement
algebra itself — additivity, the image of zero, positivity and the commutation
of opposite placements — is supplied by the placement identities proved in
`MIPStarRE.QPBT.Combining.Points.PlacementSupport` and
`MIPStarRE.QPBT.Observables.LineMeasurement.LinePointOverlap`.

## References

The consistency defect is blueprint `def:consistency`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`.  The
placements and their bipartitions are blueprint `def:expanded-state`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
nonnegativity is the hypothesis of items 1 and 2 of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-- Positive operators placed on a directed opposite pair of registers have a
positive product.  Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`,
blueprint `def:expanded-state`. -/
theorem place_mul_place_nonneg (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement) (hopp : p₁.IsOpposite p₂)
    {X : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p₁.side)}
    {Y : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p₂.side)}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ S.place p₁ X * S.place p₂ Y := by
  exact Commute.mul_nonneg (S.place_nonneg p₁ hX) (S.place_nonneg p₂ hY)
    (S.place_comm p₁ p₂ hopp X Y)





end ProjectiveSetting

/-! ## Nonnegativity of the pointwise consistency defect -/





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



namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





















/-! ## Effects of the completed measurement families -/





/-- The completed expanded point measurement agrees with the expanded point
measurement on proper values. -/
theorem pointMeasExpOption_effect_some (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointMeasExpOption side W u).effect (some b) =
      (S.pointMeasExp side W u).effect b := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [Finset.filter_eq']

/-- The completed expanded point measurement assigns zero to `none`. -/
theorem pointMeasExpOption_effect_none (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointMeasExpOption side W u).effect none = 0 := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  apply Finset.sum_eq_zero
  intro a ha
  exact absurd (Finset.mem_filter.mp ha).2 (by simp)







/-! ## Factorization of opposite placements with distinct Pauli factors -/













end ProjectiveSetting

/-! ## The overlap identity -/







end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ZEvalDeficit.lean. -/
/-!
# Z-point deficits of the evaluated pair-line measurement

This module bounds the deficit of the overlap between the evaluated paired-line
measurement and the expanded Z-point measurement. The proof inserts the completed
joint point measurement, replaces it by the X-then-Z ordered product, and sums
the X effects. It uses evaluated consistency and the distance from the joint
point measurement to that ordered product. The bound holds first over any
probability law on pairs of line-point pairs and then over a product of restricted
line-point laws, whose point marginal is the uniform pair.

The estimates hold for arbitrary opposite placements, with first-player
specializations; register commutation requires no symmetry of the state.
The completed-outcome and real-overlap lemmas are also available for other
calculations. The concrete X-deficit argument is separate, in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z deficit supports blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`; the
consistency input is `lem:qld-xz-lines` and the ordered products are those of
`lem:qld-4-10`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Completed point pairs -/



/-- The completed joint measurement has the joint effect on a pair of
evaluations. -/
theorem completedPair_effect_some {β γ d : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] [Fintype d] [DecidableEq d]
    (Q : _root_.LIDT.MIPStarRE.Quantum.Measurement (β × γ) d) (bc : β × γ) :
    (Q.postprocess fun ab => (some ab.1, some ab.2)).effect (some bc.1, some bc.2) =
      Q.effect bc := by
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
    show (Finset.univ.filter fun cd : β × γ =>
        (some cd.1, some cd.2) = (some bc.1, some bc.2)) = {bc} by
      ext cd; simp [Prod.ext_iff, eq_comm]]
  simp

/-- The completed joint measurement vanishes on outcomes outside the image of
the completion. -/
theorem completedPair_effect_eq_zero {β γ d : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] [Fintype d] [DecidableEq d]
    (Q : _root_.LIDT.MIPStarRE.Quantum.Measurement (β × γ) d) (o : Option β × Option γ)
    (ho : ∀ bc : β × γ, (some bc.1, some bc.2) ≠ o) :
    (Q.postprocess fun ab => (some ab.1, some ab.2)).effect o = 0 := by
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact Finset.sum_eq_zero fun bc hbc =>
    absurd (Finset.mem_filter.mp hbc).2 (ho bc)

/-- The completion of a projective joint measurement is projective. -/
theorem completedPair_isProjective {β γ d : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] [Fintype d] [DecidableEq d]
    (Q : _root_.LIDT.MIPStarRE.Quantum.Measurement (β × γ) d) (hQ : _root_.MIPStarRE.QPBT.Measurement.IsProjective Q) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (Q.postprocess fun ab => (some ab.1, some ab.2)) := by
  intro o
  by_cases h : ∃ bc : β × γ, (some bc.1, some bc.2) = o
  · obtain ⟨bc, rfl⟩ := h
    rw [_root_.MIPStarRE.QPBT.completedPair_effect_some]
    exact hQ bc
  · push Not at h
    rw [_root_.MIPStarRE.QPBT.completedPair_effect_eq_zero Q o h]
    exact IsStarProjection.zero _

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-- A placed projection is a projection. -/
theorem place_isProj (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement)
    {E : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)} (hE : _root_.LIDT.MIPStarRE.Quantum.IsProj E) :
    _root_.LIDT.MIPStarRE.Quantum.IsProj (S.place p E) := by
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · change S.place p E * S.place p E = S.place p E
    rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul, hE.isIdempotentElem.eq]
  · rw [Matrix.star_eq_conjTranspose, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_conjTranspose,
      hE.isSelfAdjoint.isHermitian.eq]

/-- Every effect of the completed expanded point measurement is a projection,
the `none` effect being zero. -/
theorem pointMeasExpOption_isProj (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (o : Option (_root_.MIPStarRE.QPBT.PauliScalar P)) :
    _root_.LIDT.MIPStarRE.Quantum.IsProj ((S.pointMeasExpOption side W u).effect o) := by
  cases o with
  | none =>
    rw [S.pointMeasExpOption_effect_none]
    exact IsStarProjection.zero _
  | some a =>
    rw [S.pointMeasExpOption_effect_some]
    exact S.pointMeasExp_isProjective side W u a






end ProjectiveSetting

/-! ## The abstract one-point deficit -/



/-! ## The two placed deficits -/





/-! ## The two deficits over a product of restricted line-point laws -/











end

end MIPStarRE.QPBT

/-!
# X-point deficit from joint line consistency

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder



open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ δP : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
  {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness S points δP)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second)
    (ν : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.MIPStarRE.QPBT.LinePointPairSample P)) (hν : ν.IsProbability) (η ζ : ℝ)
    (hcons : _root_.MIPStarRE.QPBT.consistencyDefect ν
      (fun s o => S.place first
        (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
          (_root_.MIPStarRE.QPBT.evalOpt s.1.1 s.1.2 fs.1, _root_.MIPStarRE.QPBT.evalOpt s.2.1 s.2.2 fs.2)).effect o))
      (fun s o => S.place second
        (((points.Q second.side s.1.2 s.2.2).postprocess fun ab =>
          (some ab.1, some ab.2)).effect o))
      S.psiHat ≤ η)
    (hXZ : _root_.MIPStarRE.QPBT.opFamilyDistSq ν
      (fun s o => S.place second
        (((points.Q second.side s.1.2 s.2.2).postprocess fun ab =>
          (some ab.1, some ab.2)).effect o))
      (fun s o => S.place second
        ((S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2))
      S.psiHat ≤ ζ) :
    1 - _root_.LIDT.MIPStarRE.LDT.avgOver ν (fun s =>
      ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          (S.place first
            (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
              (_root_.MIPStarRE.QPBT.evalOpt s.1.1 s.1.2 fs.1, _root_.MIPStarRE.QPBT.evalOpt s.2.1 s.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1))) ≤
      2 * Real.sqrt η + 2 * Real.sqrt ζ := by
  have hQproj : ∀ s : _root_.MIPStarRE.QPBT.LinePointPairSample P,
      _root_.MIPStarRE.QPBT.Measurement.IsProjective (S.placedMeasurement second
        ((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))) :=
    fun s => S.placedMeasurement_isProjective _ _
      (_root_.MIPStarRE.QPBT.completedPair_isProjective _ (points.projective _ _ _))
  have hRproj : ∀ (s : _root_.MIPStarRE.QPBT.LinePointPairSample P)
      (o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P)),
      _root_.LIDT.MIPStarRE.Quantum.IsProj (S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1)) :=
    fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _)
  have hWR : ∀ (s : _root_.MIPStarRE.QPBT.LinePointPairSample P)
      (o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P)),
      S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1) *
        S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1) =
      S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
        (S.pointMeasExpOption second.side .X s.1.2).effect o.1) := by
    intro s o
    have hlocal : (S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
        (S.pointMeasExpOption second.side .X s.1.2).effect o.1 =
        (S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1 := by
      rw [mul_assoc, (S.pointMeasExpOption_isProj second.side .X s.1.2 o.1).isIdempotentElem.eq]
    exact (_root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul S second _ _).symm.trans
      (congrArg (S.place second) hlocal)
  have hnonneg : ∀ (s : _root_.MIPStarRE.QPBT.LinePointPairSample P)
      (o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P)),
      0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place first
          (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
            (_root_.MIPStarRE.QPBT.evalOpt s.1.1 s.1.2 fs.1, _root_.MIPStarRE.QPBT.evalOpt s.2.1 s.2.2 fs.2)).effect o) *
          S.place second
            (((points.Q second.side s.1.2 s.2.2).postprocess fun ab =>
              (some ab.1, some ab.2)).effect o)) :=
    fun s o => _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg _ (S.place_mul_place_nonneg first second hopposite
      (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
        (_root_.MIPStarRE.QPBT.evalOpt s.1.1 s.1.2 fs.1, _root_.MIPStarRE.QPBT.evalOpt s.2.1 s.2.2 fs.2)).pos o)
      (((points.Q second.side s.1.2 s.2.2).postprocess fun ab =>
        (some ab.1, some ab.2)).pos o))
  have hdist : _root_.MIPStarRE.QPBT.opFamilyDistSq ν
      (fun s o => S.place second
        (((points.Q second.side s.1.2 s.2.2).postprocess fun ab =>
          (some ab.1, some ab.2)).effect o))
      (fun s o => (S.place second
        ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1))ᴴ)
      S.psiHat ≤ ζ := by
    refine le_of_eq_of_le ?_ hXZ
    unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun s => Finset.sum_congr rfl fun o _ => ?_
    have hlocal : ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1)ᴴ =
        (S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2 := by
      rw [Matrix.conjTranspose_mul,
        (S.pointMeasExpOption_isProj second.side .X s.1.2 o.1).isSelfAdjoint.isHermitian.eq,
        (S.pointMeasExpOption_isProj second.side .Z s.2.2 o.2).isSelfAdjoint.isHermitian.eq]
    have hplace : (S.place second
        ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
          (S.pointMeasExpOption second.side .X s.1.2).effect o.1))ᴴ =
        S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1 *
          (S.pointMeasExpOption second.side .Z s.2.2).effect o.2) :=
      (_root_.MIPStarRE.QPBT.ProjectiveSetting.place_conjTranspose S second _).symm.trans
        (congrArg (S.place second) hlocal)
    dsimp only
    rw [hplace]
  exact _root_.MIPStarRE.QPBT.one_sub_overlap_le_of_consistencyDefect ν
    (fun s => S.placedMeasurement first
      ((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
        (_root_.MIPStarRE.QPBT.evalOpt s.1.1 s.1.2 fs.1, _root_.MIPStarRE.QPBT.evalOpt s.2.1 s.2.2 fs.2)))
    (fun s => S.placedMeasurement second
      ((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2)))
    (fun s o => S.place second ((S.pointMeasExpOption second.side .X s.1.2).effect o.1))
    (fun s o => S.place second
      ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2 *
        (S.pointMeasExpOption second.side .X s.1.2).effect o.1))
    S.psiHat hν S.psiHat_norm hQproj hRproj
    (fun s o => S.place_comm first second hopposite _ _)
    (fun s o => S.place_comm first second hopposite _ _)
    (fun s o => S.place_comm first second hopposite _ _)
    hWR hnonneg η ζ hcons hdist
