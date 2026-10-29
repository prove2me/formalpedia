-- Prove2me | solution 1 for MIPStarRE.QPBT.pullingMeas_eval_point_consistent_bob
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:18:01.540383+00:00
-- url     : https://prove2.me/submissions/533ca71a-96f8-4149-8bba-de75488f7a19

-- Generated proof for MIPStarRE.QPBT.pullingMeas_eval_point_consistent_bob.
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
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_BlockMeasurement
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Extraction_PointConsistency
import Definitions.Def_QPBT_QPBT_Extraction_PullingMeasurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_LinePointOverlap
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_consistencyDefect_eq_one_sub_overlap
import Theorems.Thm_MIPStarRE_QPBT_pullingMeas_eval_effect
import Theorems.Thm_MIPStarRE_QPBT_sum_marginalPoly_eval_mul

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
namespace MIPStarRE.QPBT.GlobalPairWitness
end MIPStarRE.QPBT.GlobalPairWitness
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Extraction/Consistency.lean. -/
/-!
# Consistency of the pulled-apart Pauli measurements

This module records the two estimates by which the polynomial marginals absorb
the expanded point measurements, with all heterogeneous placements written
explicitly. It also defines the mass of non-encoding marginal outcomes and
states the support estimate needed by the corrected decoder calculation.

The marginal agreement estimates and reverse-placement correlation transports
are developed from a supplied global polynomial-pair witness.

## References

The marginal estimates formalize blueprint
`lem:qld-constructing-the-paulis-helper`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1609-1664`.
The non-encoding support obligation contributes to blueprint
`lem:qld-construct-the-paulis`, from paper lines 1458-1608; see
`docs/paper-gaps/qpbt_decoding-identity.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus
open ProjectiveSetting

noncomputable section

/-! ## Absorption of expanded point measurements -/





namespace GlobalPairWitness

/-- Evaluating a single-basis marginal is the same finite postprocessing as
evaluating the corresponding component of the joint polynomial outcome. This
is the coarse-graining in the proof of blueprint
`lem:qld-constructing-the-paulis-helper`, paper
`14_analysis_of_the_pauli_basis_test.tex:1626-1637`. -/
theorem marginalPoly_postprocess_eval {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (point : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (w.marginalPoly side W).postprocess (fun poly => MvPolynomial.eval point poly.1) =
      (w.Smeas side).postprocess (_root_.MIPStarRE.QPBT.evalAt W point) := by
  rw [_root_.MIPStarRE.QPBT.GlobalPairWitness.marginalPoly, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
  cases W <;> rfl

end GlobalPairWitness





/-- Bob's evaluated marginal on `BB'` retains the witness consistency with
Alice's expanded point measurement on `AB''`. This is the reverse-player
direct placement of paper `14_analysis_of_the_pauli_basis_test.tex:1626-1637`,
supporting blueprint `lem:qld-constructing-the-paulis-helper`; no register
transfer is used. -/
theorem marginalPoly_pointMeas_consistent_bob {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {epsilon deltaG : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
      (fun point answer => S.place .BB'
        (((w.marginalPoly .bob W).postprocess
          (fun poly => MvPolynomial.eval point poly.1)).effect answer))
      (fun point answer => S.place .AB''
        ((S.pointMeasExp .alice W point).effect answer)) S.psiHat ≤ deltaG := by
  simpa only [w.marginalPoly_postprocess_eval] using w.point_consistent_bob W



























/-! ## Non-encoding support -/





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/PointConsistency.lean. -/
/-!
# Point consistency after decoding polynomial outcomes

This module expands the overlap of an original point measurement with a
pulled-apart measurement. The decoded polynomial is kept explicit, so the
calculation does not use the decoder identity outside the encoding image.

## References

These are auxiliary identities for blueprint `lem:qld-construct-the-paulis`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`.
The restriction on the decoder identity is recorded in
`docs/paper-gaps/qpbt_decoding-identity.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ}



/-- The point factor on `A` and the factors on `BB'B''` can be regrouped as
the factors on `BB'` and `AB''`, without moving any register. -/
theorem placePlayer_alice_mul_placeSide_bob_tensor (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
    (A : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob))
    (T : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) :
    S.placePlayer .alice A * S.placeSide .bob (_root_.MIPStarRE.QPBT.heteroKron B T) =
      S.place .BB' B * S.place .AB'' (_root_.MIPStarRE.QPBT.heteroKron A T) := by
  classical
  ext row col
  simp [_root_.MIPStarRE.QPBT.ProjectiveSetting.placePlayer, _root_.MIPStarRE.QPBT.ProjectiveSetting.placeSide, _root_.MIPStarRE.QPBT.sixRegExtractionEquiv, _root_.MIPStarRE.QPBT.reindexOp, _root_.MIPStarRE.QPBT.heteroKron,
    Matrix.kronecker, _root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> ac_rfl



/-- The convolution formula with its second outcome solved for. This is the
third line of the overlap calculation in paper lines 1483--1492. -/
theorem pointMeasExp_effect_eq_sum_sub (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointMeasExp side W u).effect a =
      ∑ b : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas side W u).effect b)
        (_root_.MIPStarRE.QPBT.tauDotProj W (_root_.MIPStarRE.QPBT.indicatorVec u) (a - b)) := by
  classical
  change S.expPointOp side W u a = _
  rw [S.expPointOp_eq_convolution]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  have h (c : _root_.MIPStarRE.QPBT.PauliScalar P) : b + c = a ↔ c = a - b := by
    rw [eq_sub_iff_add_eq, add_comm]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

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

/- Source helpers from QPBT/Extraction/PullingPointConsistency.lean. -/
/-!
# Point overlaps for the difference-polynomial measurement

Evaluation of the difference polynomial gives `g(u) - g_h(u)`. Unlike
evaluation after decoding, this formula holds for every polynomial outcome.
The resulting point overlaps are the ones supplied by the global witness.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1495-1545`,
  especially `eq:qld-pulling-2b` and `eq:qld-pulling-12`.
- The point-placement and convolution identities identify these overlaps with
  the two consistency relations of the supplied global measurement.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the extraction obligations of this chapter. These
  identities do not construct the global witness. This module was
  originally filed under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section





/-- The reverse-player overlap uses the witness's Bob point-consistency relation, with
the original `BB'` and `AB''` placements retained. -/
theorem sum_pointMeas_mul_pullingMeas_eval {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, S.placePlayer .alice ((S.pointMeas .alice W u).effect a) *
      S.placeSide .bob
        (((_root_.MIPStarRE.QPBT.pullingMeas w .bob W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a)) =
      ∑ g : _root_.MIPStarRE.QPBT.Poly P, S.place .BB' ((w.marginalPoly .bob W).effect g) *
        S.place .AB'' ((S.pointMeasExp .alice W u).effect (_root_.MIPStarRE.QPBT.evalPoly g u)) := by
  simp_rw [_root_.MIPStarRE.QPBT.pullingMeas_eval_effect (S := S) w .bob W u]
  simp only [S.placeSide_bob_finset_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [S.placePlayer_alice_mul_placeSide_bob_tensor]
  rw [← Finset.mul_sum, ← S.place_finset_sum, S.pointMeasExp_effect_eq_sum_sub .alice W u]

end

end MIPStarRE.QPBT

/-!
# Evaluated consistency of the difference-polynomial measurements

The exact overlap identities identify the consistency with the opposite
player's point measurement with the consistency supplied by the global witness.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1495-1545`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the extraction obligations of this chapter; the
  global
  witness is supplied here, not constructed. This module was originally
  filed under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {epsilon deltaG : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob
        (((_root_.MIPStarRE.QPBT.pullingMeas w .bob W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a)) S.psiHat ≤
        deltaG := by
  let mu := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
  let pulled := fun u => S.blockMeasurement .bob
    ((_root_.MIPStarRE.QPBT.pullingMeas w .bob W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u))
  let point := fun u => S.placedMeasurement .AA' (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (S.pointMeas .alice W u))
  let marginal := fun u => S.placedMeasurement .BB'
    ((w.marginalPoly .bob W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u))
  let expanded := fun u => S.placedMeasurement .AB'' (S.pointMeasExp .alice W u)
  have hp := _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap mu point pulled S.psiHat
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) S.psiHat_norm
  have hm := _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap mu marginal expanded S.psiHat
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) S.psiHat_norm
  have heq : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (point u).effect a)
      (fun u a => (pulled u).effect a) S.psiHat =
      _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (marginal u).effect a)
        (fun u a => (expanded u).effect a) S.psiHat := by
    rw [hp, hm]
    apply congrArg (1 - ·)
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro u
    simp only [pulled, point, marginal, expanded, _root_.MIPStarRE.QPBT.ProjectiveSetting.blockMeasurement_effect,
      _root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect]
    change (∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
      (S.placePlayer .alice ((S.pointMeas .alice W u).effect a) * S.placeSide .bob
        (((_root_.MIPStarRE.QPBT.pullingMeas w .bob W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a))) = _
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, _root_.MIPStarRE.QPBT.sum_pointMeas_mul_pullingMeas_eval]
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    exact congrArg (_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat)
      (_root_.MIPStarRE.QPBT.sum_marginalPoly_eval_mul w .BB' W u
        (fun a => S.place .AB'' ((S.pointMeasExp .alice W u).effect a))).symm
  have hbound := _root_.MIPStarRE.QPBT.marginalPoly_pointMeas_consistent_bob w W
  change _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (marginal u).effect a)
    (fun u a => (expanded u).effect a) S.psiHat ≤ deltaG at hbound
  exact heq.le.trans hbound
