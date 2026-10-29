-- Prove2me | solution 1 for MIPStarRE.QPBT.subline_remove_x_factor_at_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:32:47.811229+00:00
-- url     : https://prove2.me/submissions/66e6ea32-1f1c-4f9e-b6c0-2fbfcb742b3e

-- Generated proof for MIPStarRE.QPBT.subline_remove_x_factor_at_explicit.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_SubLineXDeficit
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
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
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_isProbability
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_conjTranspose
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_mul
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_one_sub_avgOver_xPointOverlap_le_at
import Theorems.Thm_MIPStarRE_QPBT_abs_overlap_gap_le_sqrt_one_sub_of_isProj
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_integrand_nonneg
import Theorems.Thm_MIPStarRE_QPBT_regroup_line_answer_sum_at
import Theorems.Thm_MIPStarRE_QPBT_sqrt_deficit_bound_le

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











/-! ## Replacing a factor under the weight of a measurement -/





/-- The deficit form of the Cauchy--Schwarz estimate with the product family
`C B` supplied as one family `CB`, which is convenient when the product is
formed on a local space before being placed. -/
theorem abs_overlap_gap_le_sqrt_one_sub_of_isProj' {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (B C CB : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hB : ∀ x a, _root_.LIDT.MIPStarRE.Quantum.IsProj (B x a)) (hC : ∀ x a, _root_.LIDT.MIPStarRE.Quantum.IsProj (C x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a))
    (hAC : ∀ x a, Commute ((A x).effect a) (C x a))
    (hCB : ∀ x a, CB x a = C x a * B x a) :
    |avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * CB x a)) -
        _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt (1 - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
        ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * B x a))) := by
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ => by rw [hCB]]
  exact _root_.MIPStarRE.QPBT.abs_overlap_gap_le_sqrt_one_sub_of_isProj μ A B C ψ hμ hψ hB hC hAB hAC





end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/SubLineXDeficit.lean. -/
/-!
# X-point subline averages

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

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ δP : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
  {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ}

/-- The sub-line average, with a uniform affine parameter on the extended
line, of a sum over line answers of an overlap with a point family that
depends on the two evaluations of the answer, as the average against the
product of the sub-line law and the uniform parameter of the overlap of the
evaluated pair-line measurement with that family.  Blueprint
`lem:qld-4-13-established`. -/
theorem SubLineWitness.avgOver_regrouped_eq_at {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {ε δQ δP : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε} {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ}
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness P) (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness S points δP)
    (first second : _root_.MIPStarRE.QPBT.Placement)
    (G : (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) → (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) →
      Option (_root_.MIPStarRE.QPBT.PauliScalar P) → Option (_root_.MIPStarRE.QPBT.PauliScalar P) →
      _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace second.side)) :
    _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
          (fun t =>
            let u := _root_.MIPStarRE.QPBT.directPointToPauli P
              (sample.1.base + t • sample.1.direction)
            let x := _root_.MIPStarRE.QPBT.projX u
            let z := _root_.MIPStarRE.QPBT.projZ u
            ∑ fX, ∑ fZ,
              (inner ℂ S.psiHat ((EuclideanSpace.equiv
                (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                  ((S.place first
                      ((lines.T first.side sample.2.1 sample.2.2).effect
                        (fX, fZ)) *
                    S.place second
                      (G x z (_root_.MIPStarRE.QPBT.evalOpt sample.2.1 x fX)
                        (_root_.MIPStarRE.QPBT.evalOpt sample.2.2 z fZ))).mulVec
                          S.psiHat))).re)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod sublines.D
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)))
        (fun s => ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
            ((S.placedMeasurement first
              ((lines.T first.side s.1.2.1 s.1.2.2).postprocess (fun fs =>
                (_root_.MIPStarRE.QPBT.evalOpt s.1.2.1 (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
                  _root_.MIPStarRE.QPBT.evalOpt s.1.2.2 (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction))) fs.2)))).effect o *
              S.place second
                (G (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction)))
                  (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction))) o.1 o.2))) := by
  rw [_root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
  refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun sample => ?_
  refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun t => ?_
  exact (_root_.MIPStarRE.QPBT.regroup_line_answer_sum_at lines first second sample.2.1 sample.2.2 _ _ (G _ _)).symm

/-! ## The mixture form of a one-point sub-line average -/








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





























































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 2: state-dependent squared distance between operator families is
nonnegative. -/
theorem opFamilyDistSq_nonneg {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    0 ≤ _root_.MIPStarRE.QPBT.opFamilyDistSq μ M N ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x)
    (Finset.sum_nonneg fun a _ => sq_nonneg _)





























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

/-- The expanded point effect selected by a line answer is the completed
expanded point effect at the partial evaluation of the answer. This
identifies the two presentations of item 2 and item 3 of
`lem:qld-comm-line-cons`, blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`. -/
theorem pointMeasExpOption_effect_evalOpt (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) :
    (S.pointMeasExpOption side W u).effect (_root_.MIPStarRE.QPBT.evalOpt line u f) =
      S.expPointEffectAtLineAnswer side W line u f := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointEffectAtLineAnswer
  cases _root_.MIPStarRE.QPBT.evalOpt line u f with
  | none => exact S.pointMeasExpOption_effect_none side W u
  | some a => exact S.pointMeasExpOption_effect_some side W u a





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
# Estimates for the extended-line construction

This construction uses the directly indexed extended-line space, the answer
alphabet obtained from the field by adjoining an undefined-evaluation outcome,
and the corrected sum-form convention for polynomial errors.

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

theorem solution
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε δQ δP : ℝ)
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ)
    (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness S points δP) (sublines : _root_.MIPStarRE.QPBT.SubLineWitness P)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second) :
    |avgOver sublines.D (fun sample =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) (fun t =>
          let u := _root_.MIPStarRE.QPBT.directPointToPauli P
            (sample.1.base + t • sample.1.direction)
          let x := _root_.MIPStarRE.QPBT.projX u
          let z := _root_.MIPStarRE.QPBT.projZ u
          ∑ fX, ∑ fZ,
            (inner ℂ S.psiHat ((EuclideanSpace.equiv
              (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                ((S.place first
                    ((lines.T first.side sample.2.1 sample.2.2).effect (fX, fZ)) *
                  S.place second
                    (S.expPointEffectAtLineAnswer second.side .Z sample.2.2 z fZ *
                      S.expPointEffectAtLineAnswer second.side .X sample.2.1 x fX)).mulVec
                        S.psiHat))).re)) -
      _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) (fun t =>
          let u := _root_.MIPStarRE.QPBT.directPointToPauli P
            (sample.1.base + t • sample.1.direction)
          let z := _root_.MIPStarRE.QPBT.projZ u
          ∑ fX, ∑ fZ,
            (inner ℂ S.psiHat ((EuclideanSpace.equiv
              (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                ((S.place first
                    ((lines.T first.side sample.2.1 sample.2.2).effect (fX, fZ)) *
                  S.place second
                    (S.expPointEffectAtLineAnswer second.side .Z sample.2.2 z fZ)).mulVec
                      S.psiHat))).re))| ≤
      2 * Real.sqrt (P.m : ℝ) *
        (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ)) := by
  classical
  have hside := sublines.avgOver_regrouped_eq_at lines first second
  have hprob : (_root_.MIPStarRE.QPBT.Distribution.prod sublines.D
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))).IsProbability :=
    _root_.MIPStarRE.QPBT.Distribution.prod_isProbability _ _ sublines.isProbability
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _)
  have hδP : 0 ≤ δP := by
    refine le_trans ?_ (lines.consistent first second hopposite)
    unfold _root_.MIPStarRE.QPBT.consistencyDefect
    exact _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg _ _ fun s =>
      _root_.MIPStarRE.QPBT.consistencyDefect_integrand_nonneg S first second hopposite
        ((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
          (_root_.MIPStarRE.QPBT.evalOpt s.1.1 s.1.2 fs.1, _root_.MIPStarRE.QPBT.evalOpt s.2.1 s.2.2 fs.2))
        ((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))
  have hδQ : 0 ≤ δQ :=
    le_trans (_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) (points.self_consistent first second hopposite)
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  simp only [← _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption_effect_evalOpt]
  rw [hside (fun x z o1 o2 => (S.pointMeasExpOption second.side .Z z).effect o2 *
      (S.pointMeasExpOption second.side .X x).effect o1),
    hside (fun x z o1 o2 => (S.pointMeasExpOption second.side .Z z).effect o2)]
  have hcs := _root_.MIPStarRE.QPBT.abs_overlap_gap_le_sqrt_one_sub_of_isProj'
    (_root_.MIPStarRE.QPBT.Distribution.prod sublines.D
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)))
    (fun s => S.placedMeasurement first
      ((lines.T first.side s.1.2.1 s.1.2.2).postprocess (fun fs =>
        (_root_.MIPStarRE.QPBT.evalOpt s.1.2.1 (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
          _root_.MIPStarRE.QPBT.evalOpt s.1.2.2 (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction))) fs.2))))
    (fun (s : _root_.MIPStarRE.QPBT.SubLineTriple P × _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
        (o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P)) =>
      S.place second ((S.pointMeasExpOption second.side .X
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
          (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))
    (fun (s : _root_.MIPStarRE.QPBT.SubLineTriple P × _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
        (o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P)) =>
      S.place second ((S.pointMeasExpOption second.side .Z
        (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
          (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2))
    (fun (s : _root_.MIPStarRE.QPBT.SubLineTriple P × _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
        (o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P)) =>
      S.place second
        ((S.pointMeasExpOption second.side .Z
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2 *
          (S.pointMeasExpOption second.side .X
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))
    S.psiHat hprob S.psiHat_norm
    (fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
    (fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
    (fun s o => S.place_comm first second hopposite _ _)
    (fun s o => S.place_comm first second hopposite _ _)
    (fun s o => _root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul S second _ _)
  refine hcs.trans ?_
  have hrew : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod sublines.D
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)))
      (fun s => ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          ((S.placedMeasurement first
            ((lines.T first.side s.1.2.1 s.1.2.2).postprocess (fun fs =>
              (_root_.MIPStarRE.QPBT.evalOpt s.1.2.1 (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
                  (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
                _root_.MIPStarRE.QPBT.evalOpt s.1.2.2 (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
                  (s.1.1.base + s.2 • s.1.1.direction))) fs.2)))).effect o *
            S.place second ((S.pointMeasExpOption second.side .X
              (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
                (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))) =
      _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
          (fun t => _root_.MIPStarRE.QPBT.xPointOverlapAt lines first second (sample.2, _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
            (sample.1.base + t • sample.1.direction))))) := by
    rw [_root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun sample => _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun t => ?_
    exact _root_.MIPStarRE.QPBT.regroup_line_answer_sum_at lines first second sample.2.1 sample.2.2 _ _
      (fun o1 _ => (S.pointMeasExpOption second.side .X (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
        (sample.1.base + t • sample.1.direction)))).effect o1)
  refine (Real.sqrt_le_sqrt ?_).trans (_root_.MIPStarRE.QPBT.sqrt_deficit_bound_le _ _ _ hm hδP hδQ)
  have hX := sublines.one_sub_avgOver_xPointOverlap_le_at lines first second hopposite
  rw [← hrew] at hX
  exact hX
