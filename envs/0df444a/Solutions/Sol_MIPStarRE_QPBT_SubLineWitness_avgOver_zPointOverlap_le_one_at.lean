-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.avgOver_zPointOverlap_le_one_at
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:34:37.628977+00:00
-- url     : https://prove2.me/submissions/c9222e88-75e8-4614-9b90-86ab3e75bf2e

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.avgOver_zPointOverlap_le_one_at.
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
import Definitions.Def_QPBT_QPBT_Combining_SubLineZDeficit
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Combining_ZEvalDeficit
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_isProbability
import Theorems.Thm_MIPStarRE_QPBT_Distribution_restrict_isProbability
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_conjTranspose
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_mul
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_exists_avgOver_Z_eq_mixture
import Theorems.Thm_MIPStarRE_QPBT_avgOver_sum_stateQForm_mul_le_one
import Theorems.Thm_MIPStarRE_QPBT_regroup_line_answer_sum_at

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/Defs.lean. -/
/-!
# Polynomial combination and restricted line distributions

This file contains the concrete definitions at the foundation of the
Chapter 15 combining argument.  A pair of bounded individual-degree
polynomials is embedded into the two coordinate blocks of an extended
polynomial.  On lines, explicit affine reparameterizations are composed with
coefficient-list polynomials.  The original-dimensional restricted line laws
are formed before decoding, while their field seed is still present.

## References

The combining map is blueprint
`def:combine-map`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`.
The restricted laws are blueprint `def:ith-restricted-line`,
with paper origin in the same source at lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

























































/-- Every restricted axis-line law has total mass one. -/
theorem restrictedALineDist_isProbability (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) :
    (_root_.MIPStarRE.QPBT.restrictedALineDist L i).IsProbability := by
  unfold _root_.MIPStarRE.QPBT.restrictedALineDist _root_.MIPStarRE.QPBT.restrictedALinePreDist
  exact (_root_.MIPStarRE.QPBT.Distribution.restrict_isProbability
    (_root_.MIPStarRE.QPBT.clDistribution (_root_.MIPStarRE.QPBT.ldALineCL L) (_root_.MIPStarRE.QPBT.ldPointCL L))
    (_root_.MIPStarRE.QPBT.restrictedLineSeedEvent L i) (_root_.MIPStarRE.QPBT.restrictedALineSeedEvent_positive L i)).map _

/-- Every restricted diagonal-line law has total mass one. -/
theorem restrictedDLineDist_isProbability (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) :
    (_root_.MIPStarRE.QPBT.restrictedDLineDist L i).IsProbability := by
  unfold _root_.MIPStarRE.QPBT.restrictedDLineDist _root_.MIPStarRE.QPBT.restrictedDLinePreDist
  exact (_root_.MIPStarRE.QPBT.Distribution.restrict_isProbability
    (_root_.MIPStarRE.QPBT.clDistribution (_root_.MIPStarRE.QPBT.ldDLineCL L) (_root_.MIPStarRE.QPBT.ldPointCL L))
    (_root_.MIPStarRE.QPBT.restrictedLineSeedEvent L i) (_root_.MIPStarRE.QPBT.restrictedDLineSeedEvent_positive L i)).map _

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/SubLineZDeficit.lean. -/
/-!
# Sub-line averages of the Z-point overlap

The Z-point overlap of the paired-line measurement depends on the two source
lines and the Z block of the sampled extended point. The separate projected-point
mixture properties of the directly indexed sub-line law identify each one-point
marginal as a mixture of restricted product laws. Both marginal averaging
identities are recorded here. Regrouping line answers by their evaluations
then transfers the Z-overlap deficit from
`MIPStarRE.QPBT.Combining.ZEvalDeficit` to this law.

The Z-overlap estimates hold for arbitrary opposite placements, with separate
first-player specializations. The concrete X-overlap deficit instead uses the
exact X marginal of the X-Z-X sandwich and is proved in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z estimates support blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`.
The separate marginal identities encode the analogue of Property 2 of
`lem:qld-sublines` for the directly indexed law; source-distribution transport
remains separate.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Regrouping the line answers by their evaluations -/









/-! ## The two one-point overlaps -/

section Overlaps

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ δP : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
  {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ}





/-- At a pair of line-point pairs, the `Z`-point overlap is the overlap of the
evaluated pair-line measurement with the completed `Z`-point measurement; the
`X`-point of the first pair only labels the evaluation classes. -/
theorem zPointOverlap_eq_at (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness S points δP)
    (first second : _root_.MIPStarRE.QPBT.Placement)
    (w : _root_.MIPStarRE.QPBT.LinePointPairSample P) :
    _root_.MIPStarRE.QPBT.zPointOverlapAt lines first second ((w.1.1, w.2.1), w.2.2) =
      ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          (S.place first
            (((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
              (_root_.MIPStarRE.QPBT.evalOpt w.1.1 w.1.2 fs.1, _root_.MIPStarRE.QPBT.evalOpt w.2.1 w.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .Z w.2.2).effect o.2)) :=
  (_root_.MIPStarRE.QPBT.regroup_line_answer_sum_at lines first second w.1.1 w.2.1 w.1.2 w.2.2
    (fun _ o2 => (S.pointMeasExpOption second.side .Z w.2.2).effect o2)).symm
















end Overlaps

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

/-- Every restricted line-point law has total mass one. -/
theorem restrictedLinePointDist_isProbability (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) (i : Fin P.m) :
    (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kind i).IsProbability := by
  cases kind
  · change (_root_.MIPStarRE.QPBT.restrictedALineDist P.toLdParams i).IsProbability
    exact _root_.MIPStarRE.QPBT.restrictedALineDist_isProbability P.toLdParams i
  · change (_root_.MIPStarRE.QPBT.restrictedDLineDist P.toLdParams i).IsProbability
    exact _root_.MIPStarRE.QPBT.restrictedDLineDist_isProbability P.toLdParams i









end

end MIPStarRE.QPBT

/-!
# Sub-line averages of the Z-point overlap

The Z-point overlap of the paired-line measurement depends on the two source
lines and the Z block of the sampled extended point. The separate projected-point
mixture properties of the directly indexed sub-line law identify each one-point
marginal as a mixture of restricted product laws. Both marginal averaging
identities are recorded here. Regrouping line answers by their evaluations
then transfers the Z-overlap deficit from
`MIPStarRE.QPBT.Combining.ZEvalDeficit` to this law.

The Z-overlap estimates hold for arbitrary opposite placements, with separate
first-player specializations. The concrete X-overlap deficit instead uses the
exact X marginal of the X-Z-X sandwich and is proved in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z estimates support blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`.
The separate marginal identities encode the analogue of Property 2 of
`lem:qld-sublines` for the directly indexed law; source-distribution transport
remains separate.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Regrouping the line answers by their evaluations -/









/-! ## The two one-point overlaps -/



variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ δP : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
  {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ}

theorem solution (sublines : _root_.MIPStarRE.QPBT.SubLineWitness P)
    (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness S points δP)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second) :
    _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (fun t => _root_.MIPStarRE.QPBT.zPointOverlapAt lines first second (sample.2, _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) ≤ 1 := by
  obtain ⟨components, hcomp, hmix⟩ :=
    _root_.MIPStarRE.QPBT.SubLineWitness.exists_avgOver_Z_eq_mixture P sublines (_root_.MIPStarRE.QPBT.zPointOverlapAt lines first second)
  rw [hmix]
  have hc : ∀ c : _root_.MIPStarRE.QPBT.SubLineComponent P,
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.restrictedLinePointDist P c.1 c.2.1)
          (_root_.MIPStarRE.QPBT.restrictedLinePointDist P c.1 c.2.2))
        (fun w => _root_.MIPStarRE.QPBT.zPointOverlapAt lines first second ((w.1.1, w.2.1), w.2.2)) ≤ 1 := by
    intro c
    have h := _root_.MIPStarRE.QPBT.avgOver_sum_stateQForm_mul_le_one
      (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.restrictedLinePointDist P c.1 c.2.1)
        (_root_.MIPStarRE.QPBT.restrictedLinePointDist P c.1 c.2.2))
      (fun w : _root_.MIPStarRE.QPBT.LinePointPairSample P => S.placedMeasurement first
        ((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
          (_root_.MIPStarRE.QPBT.evalOpt w.1.1 w.1.2 fs.1, _root_.MIPStarRE.QPBT.evalOpt w.2.1 w.2.2 fs.2)))
      (fun (w : _root_.MIPStarRE.QPBT.LinePointPairSample P)
          (o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P)) =>
        S.place second ((S.pointMeasExpOption second.side .Z w.2.2).effect o.2))
      S.psiHat
      (_root_.MIPStarRE.QPBT.Distribution.prod_isProbability _ _
        (_root_.MIPStarRE.QPBT.restrictedLinePointDist_isProbability P c.1 c.2.1)
        (_root_.MIPStarRE.QPBT.restrictedLinePointDist_isProbability P c.1 c.2.2))
      S.psiHat_norm
      (fun w o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
      (fun w o => S.place_comm first second hopposite _ _)
    simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect] at h
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun w => _root_.MIPStarRE.QPBT.zPointOverlap_eq_at lines first second w]
    exact h
  calc
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver components (fun _ => (1 : ℝ)) := _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ hc
    _ = 1 := _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability components hcomp 1
