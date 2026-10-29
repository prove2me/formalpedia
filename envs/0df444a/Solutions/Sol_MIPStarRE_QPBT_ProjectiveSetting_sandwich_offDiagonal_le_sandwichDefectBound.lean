-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.sandwich_offDiagonal_le_sandwichDefectBound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:13:59.430925+00:00
-- url     : https://prove2.me/submissions/16fbc0e4-b454-4b4c-9f3f-0351b08ac398

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.sandwich_offDiagonal_le_sandwichDefectBound.
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
import Definitions.Def_QPBT_QPBT_Combining_Points_Commutation
import Definitions.Def_QPBT_QPBT_Combining_Points_Consistency
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Points_Sandwich
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_conjTranspose
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_mul
import Theorems.Thm_MIPStarRE_QPBT_sandwich_defect_pointwise_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

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
# Self-consistency of the sandwich POVM

The sandwich POVM `R^{x,z}_{a,b} = M^Z_b M^X_a M^Z_b` of
`MIPStarRE/QPBT/Combining/Points/Sandwich.lean` is approximately self-consistent
between opposite register placements.  The source establishes this by a
Cauchy--Schwarz chain (displays `eq:qld-rw-self-cons-1` to
`eq:qld-rw-self-cons-4`); here an exact identity is used instead.  Writing
`P_1, P_2` for the two placements of an operator `P`,
`W_b = (M^Z_b)_1 (M^Z_b)_2`, and `D^W_c = (M^W_c)_1 - (M^W_c)_2`, the
consistency defect of the two placed sandwiches equals
`(1/2) ∑_b ‖D^Z_b ψ‖^2 + (1/2) ∑_{a,b} ‖D^X_a W_b ψ‖^2`,
by two applications of the identity
`∑_c ⟨w, P_c Q_c w⟩ = ‖w‖^2 - (1/2) ∑_c ‖(P_c - Q_c) w‖^2` for projective
measurements.  The second sum is then bounded by the self-consistency of `M^X`
and the commutators on the two placements, since
`D^X_a W_b = W_b D^X_a + (M^Z_b)_2 K^1_{a,b} - (M^Z_b)_1 K^2_{a,b}`, where
`K^i_{a,b}` is the placed commutator of `M^X_a` and `M^Z_b`.

## Main results

* `sandwich_overlap_identity`: the exact expression of the overlap of two
  placed sandwiches.
* `sandwich_defect_pointwise_le`: the pointwise bound on the consistency
  defect of the sandwich for a fixed point pair.
* `ProjectiveSetting.sandwichDefectBound`,
  `ProjectiveSetting.sandwich_offDiagonal_le_sandwichDefectBound`, and
  `ProjectiveSetting.avg_sandwichDefectBound_le`: the bound as a function of
  the point pair, the pointwise estimate, and the average.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`,
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:851-880`
(`lem:qld-4-10`, first step); the identity route is explained in
`docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Quadratic-form identities -/









/-! ## The overlap of two placed sandwiches -/



variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]











/-! ## The bound for the placed sandwiches -/

open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement) (hopp : p₁.IsOpposite p₂) (xz : _root_.MIPStarRE.QPBT.PointPair P) :
    (∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P, ∑ ab' : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
      if ab = ab' then 0 else _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place p₁ ((S.sandwichPoint p₁.side xz.1 xz.2).effect ab) *
          S.place p₂ ((S.sandwichPoint p₂.side xz.1 xz.2).effect ab'))) ≤
      S.sandwichDefectBound p₁ p₂ xz := by
  have hdefect := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq
    (S.placedMeasurement p₁ (S.sandwichPoint p₁.side xz.1 xz.2))
    (S.placedMeasurement p₂ (S.sandwichPoint p₂.side xz.1 xz.2)) S.psiHat
  simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect] at hdefect
  rw [hdefect, _root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_norm]
  have hkey := _root_.MIPStarRE.QPBT.sandwich_defect_pointwise_le S.psiHat
    (S.placedMeasurement p₁ (S.pointMeasExp p₁.side .X xz.1))
    (S.placedMeasurement p₂ (S.pointMeasExp p₂.side .X xz.1))
    (S.placedMeasurement p₁ (S.pointMeasExp p₁.side .Z xz.2))
    (S.placedMeasurement p₂ (S.pointMeasExp p₂.side .Z xz.2))
    (S.placedMeasurement_isProjective p₁ _ (S.pointMeasExp_isProjective _ _ _))
    (S.placedMeasurement_isProjective p₂ _ (S.pointMeasExp_isProjective _ _ _))
    (S.placedMeasurement_isProjective p₁ _ (S.pointMeasExp_isProjective _ _ _))
    (S.placedMeasurement_isProjective p₂ _ (S.pointMeasExp_isProjective _ _ _))
    (fun a b => S.place_comm p₁ p₂ hopp _ _)
    (fun a b => S.place_comm p₁ p₂ hopp _ _)
    (fun b => S.place_comm p₁ p₂ hopp _ _)
  simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect, _root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_norm] at hkey
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.sandwichDefectBound
  simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.sandwichPoint_effect, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul]
  simpa only [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul] using hkey
