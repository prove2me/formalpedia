-- Prove2me | solution 1 for MIPStarRE.QPBT.tildeM_consistencyDefect_le_deltaG_add_nonencoding
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:13:29.181139+00:00
-- url     : https://prove2.me/submissions/41313ec0-a5f5-4c9f-b277-92a2aca43160

-- Generated proof for MIPStarRE.QPBT.tildeM_consistencyDefect_le_deltaG_add_nonencoding.
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
import Definitions.Def_QPBT_QPBT_Extraction_Consistency
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_consistencyDefect_eq_one_sub_overlap
import Theorems.Thm_MIPStarRE_QPBT_marginal_eval_overlap_le_decoded_add_nonencoding
import Theorems.Thm_MIPStarRE_QPBT_sum_marginalPoly_eval_mul
import Theorems.Thm_MIPStarRE_QPBT_tildeM_consistencyDefect_eq_one_sub_decoded_overlap

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

/-- Placing a tensor with an identity on Bob's last register recovers `BB'`. -/
theorem placeSide_bob_tensor_one (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
    (B : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) :
    S.placeSide .bob (_root_.MIPStarRE.QPBT.heteroKron B (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) = S.place .BB' B := by
  ext row col
  simp [_root_.MIPStarRE.QPBT.ProjectiveSetting.placeSide, _root_.MIPStarRE.QPBT.sixRegExtractionEquiv, _root_.MIPStarRE.QPBT.reindexOp, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> rfl







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

/-!
# Supplied-witness point consistency for extraction

The two point estimates combine the point-consistency relations of a supplied
global polynomial-pair measurement with encoding support and polynomial
collision bounds.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
* `docs/paper-gaps/qpbt_decoding-identity.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeM w .bob W (_root_.MIPStarRE.QPBT.indicatorVec u) a)) S.psiHat ≤
      deltaG + _root_.MIPStarRE.QPBT.nonencodingMarginalMass w .bob W := by
  classical
  let mu := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
  let evaluated := fun u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P =>
    S.placedMeasurement .BB' ((w.marginalPoly .bob W).postprocess
      (fun g => MvPolynomial.eval u g.1))
  let expanded := fun u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P =>
    S.placedMeasurement .AB'' (S.pointMeasExp .alice W u)
  have hdefect := _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap mu evaluated expanded S.psiHat
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) S.psiHat_norm
  have hw := _root_.MIPStarRE.QPBT.marginalPoly_pointMeas_consistent_bob w W
  change _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (evaluated u).effect a)
    (fun u a => (expanded u).effect a) S.psiHat ≤ deltaG at hw
  rw [hdefect] at hw
  have hregroup (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
      (∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        ((evaluated u).effect a * (expanded u).effect a)) =
      ∑ g : _root_.MIPStarRE.QPBT.Poly P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place .BB' ((w.marginalPoly .bob W).effect g) *
          S.place .AB'' ((S.pointMeasExp .alice W u).effect
            (MvPolynomial.eval u g.1))) := by
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    change _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
      (∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, S.place .BB'
        (((w.marginalPoly .bob W).postprocess
          (fun g => MvPolynomial.eval u g.1)).effect a) *
            S.place .AB'' ((S.pointMeasExp .alice W u).effect a)) = _
    exact (congrArg (_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat)
      (_root_.MIPStarRE.QPBT.sum_marginalPoly_eval_mul w .BB' W u
        (fun a => S.place .AB'' ((S.pointMeasExp .alice W u).effect a)))).trans
      (_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum _ _ _)
  simp only [hregroup] at hw
  have hcompare := _root_.LIDT.MIPStarRE.LDT.avgOver_mono mu _ _
    (fun u => _root_.MIPStarRE.QPBT.marginal_eval_overlap_le_decoded_add_nonencoding w W u)
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability mu
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _)] at hcompare
  have hmass_eq : _root_.MIPStarRE.QPBT.nonencodingMarginalMass w .bob W =
      ∑ g ∈ Finset.univ.filter (fun g : _root_.MIPStarRE.QPBT.Poly P => ¬ _root_.MIPStarRE.QPBT.IsEncoding g),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat (S.place .BB' ((w.marginalPoly .bob W).effect g)) := by
    unfold _root_.MIPStarRE.QPBT.nonencodingMarginalMass
    simp only [S.placeSide_bob_tensor_one]
    rfl
  rw [← hmass_eq] at hcompare
  rw [_root_.MIPStarRE.QPBT.tildeM_consistencyDefect_eq_one_sub_decoded_overlap]
  dsimp only [mu] at hw hcompare
  linarith
