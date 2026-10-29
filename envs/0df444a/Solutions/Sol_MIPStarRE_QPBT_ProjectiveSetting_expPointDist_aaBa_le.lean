-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.expPointDist_aaBa_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:33:09.647595+00:00
-- url     : https://prove2.me/submissions/e68b3ade-3433-44b7-b44a-f3aff2757df0

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.expPointDist_aaBa_le.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_pointTauConsistency_aaBa_eq
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_postprocess_le
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_two_mul_consistencyDefect
import Theorems.Thm_MIPStarRE_QPBT_point_self_consistency_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/ExpandedDefs.lean. -/
/-!
# Expanded registers and point measurements

This module adjoins two EPR pairs to a heterogeneous Pauli-basis-test strategy,
records the four register placements used in the analysis, and defines the
expanded point observables and measurements. Fourier inversion identifies their
effects with a convolution of projectors and proves completeness and projectivity.

## References

The constructions formalize blueprint `def:expanded-state`,
`def:expanded-observables`, `def:expanded-point-measurement`, and
`def:expanded-point-trace-projection`. Their paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-418`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section













namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





















































/-- The expanded point measurement is the addition postprocessing of its fine
strategy--Pauli product measurement. This is the data-processing presentation
used in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:390-411`,
blueprint `lem:expanded-point-measurement-properties`. -/
theorem pointMeasExp_effect_eq_pointTauMeas_postprocess
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointMeasExp side W u).effect a =
      ((S.pointTauMeas side W u).postprocess (fun p => p.1 + p.2)).effect a := by
  change S.expPointOp side W u a = _
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointOp_eq_convolution S side W u a



















end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/PointConsistency.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.pauliEdgeNonemptyPointConsistency
/-!
# Expanded point consistency and commutation

This module records the quantitative conclusions for the expanded point
measurements on each of the four register placements. No symmetry-transfer
principle is assumed: the four placements occur explicitly in the statements.

## References

The declarations formalize blueprint
`lem:qld-comm-cons`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:452-505`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section



/-! ## Consistency of the unexpanded point measurements -/





/-- Postprocessing a measurement after adjoining an identity register agrees
effectwise with adjoining that register after postprocessing. -/
theorem leftPlacedMeasurement_postprocess_effect
    {α β ι κ : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (f : α → β) (b : β) :
    ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := κ) M).postprocess f).effect b =
      _root_.MIPStarRE.QPBT.heteroKron ((M.postprocess f).effect b) (1 : _root_.LIDT.MIPStarRE.Quantum.Op κ) := by
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  change (∑ a ∈ Finset.univ.filter (fun a => f a = b),
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := κ) (M.effect a)) =
    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := κ)
      (∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a)
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum _ _

-- The statements below are indexed by the fourfold iterated product of
-- `eq:def-psihat`; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default, which the
-- `synthInstance.maxSize` settings below supply declaration by declaration.


















end


end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/Interchange.lean. -/
/-!
# Interchange of the tensor factors in the winning implications

This module collects the statements shared by the operator-distance companions
of the winning implications and by their factor-interchanged forms: transport of
the state-dependent distance along the interchange of the two tensor factors,
the constant-factor passage from consistency to distance, the reversed
verifier edges, and the clause-by-clause symmetry of the Pauli win predicate
on the ordered type pairs that the implications use.

## References

The declarations support the trailing clause of `lem:qld-win-implications` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:616-706`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`,
whose closing sentences at lines 227 and 263-264 state both companions.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Transport of the distance functional along the factor interchange -/



/-- Reindexing an operator is computed entrywise, hence commutes with
subtraction. Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_sub {ι ι' : Type*} (e : ι ≃ ι') (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι') :
    _root_.MIPStarRE.QPBT.reindexOp e (M - N) = _root_.MIPStarRE.QPBT.reindexOp e M - _root_.MIPStarRE.QPBT.reindexOp e N := rfl



/-- Coordinates of an operator applied to a reindexed state. Formalization-only
support for the interchanged conclusions of `lem:qld-win-implications`,
blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem applyOperatorToState_reindexState_ofLp {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (T : _root_.LIDT.MIPStarRE.Quantum.Op κ) (ψ : EuclideanSpace ℂ ι) (k : κ) :
    (_root_.MIPStarRE.QPBT.applyOperatorToState T (_root_.MIPStarRE.QPBT.reindexState e ψ)).ofLp k =
      (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.reindexOp e T) ψ).ofLp (e.symm k) := by
  change (T *ᵥ (_root_.MIPStarRE.QPBT.reindexState e ψ).ofLp) k = (_root_.MIPStarRE.QPBT.reindexOp e T *ᵥ ψ.ofLp) (e.symm k)
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
    ← e.sum_comp (fun l : κ => T k l * (_root_.MIPStarRE.QPBT.reindexState e ψ).ofLp l)]
  apply Finset.sum_congr rfl
  intro j _
  simp [_root_.MIPStarRE.QPBT.reindexState, _root_.MIPStarRE.QPBT.reindexOp]

/-- Reindexing a state and its operator preserves the length of the image.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem norm_applyOperatorToState_reindexState {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (T : _root_.LIDT.MIPStarRE.Quantum.Op κ) (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState T (_root_.MIPStarRE.QPBT.reindexState e ψ)‖ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.reindexOp e T) ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← e.symm.sum_comp (fun i : ι =>
      ‖(_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.reindexOp e T) ψ).ofLp i‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro k _
  rw [_root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_reindexState_ofLp]



/-- Consistency bounds the state-dependent distance of two oppositely placed
measurement families. This is the first item of `fact:agreement`, blueprint
`ch12_qpbt_games.tex:260-276`, in the placed form used by the trailing clause
of `lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:699-701`,
paper `14_analysis_of_the_pauli_basis_test.tex:263-264`. -/
theorem opFamilyDistSq_placed_le_two_mul_consistencyDefect
    {X α ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ ≤
      2 * _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ :=
  _root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect μ
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (A x))
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (B x)) ψ

/-- Consistency at level `c` gives operator distance at level `2 * c` for two
oppositely placed measurement families. This is the quantitative form of
`fact:agreement`, blueprint `ch12_qpbt_games.tex:260-276`, used by the trailing
clause of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:699-701`, paper
`14_analysis_of_the_pauli_basis_test.tex:263-264`. -/
theorem opFamilyDistSq_placed_le_of_consistencyDefect_le
    {X α ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) {c : ℝ}
    (h : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
      (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ ≤ c) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
      (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ ≤ 2 * c := by
  have hstep := _root_.MIPStarRE.QPBT.WinImplications.opFamilyDistSq_placed_le_two_mul_consistencyDefect μ A B ψ
  linarith

/-! ## Reversed verifier edges

The Pauli type graph is a set of unordered pairs, so every ordered edge used by
the exact implications has its reverse in the graph. The reversed edges carry
the interchanged conclusions of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/













/-! ## Symmetry of the win predicate on the subtests used here

`def:pauli-win-predicate` lists every clause together with its mirror image, so
on each ordered type pair occurring in `lem:qld-win-implications` exchanging the
two questions and the two answers leaves the predicate unchanged. Paper
`08_classical_and_quantum_low_degree_tests.tex:1126-1225`, blueprint
`ch13_qpbt_test.tex:410-449`. -/













/-! ## Numeric bookkeeping -/





end WinImplications

end

end MIPStarRE.QPBT

/-!
# Expanded point consistency and commutation

This module records the quantitative conclusions for the expanded point
measurements on each of the four register placements. No symmetry-transfer
principle is assumed: the four placements occur explicitly in the statements.

## References

The declarations formalize blueprint
`lem:qld-comm-cons`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:452-505`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum





/-! ## Consistency of the unexpanded point measurements -/







-- The statements below are indexed by the fourfold iterated product of
-- `eq:def-psihat`; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default, which the
-- `synthInstance.maxSize` settings below supply declaration by declaration.
open MIPStarRE.QPBT.ProjectiveSetting

/-! ## Fine-product consistency on the two bipartitions -/





/-! ## Data processing and transport back to the six registers -/
attribute [local instance] _root_.MIPStarRE.QPBT.pauliEdgeNonemptyPointConsistency

set_option synthInstance.maxSize 400 in

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => S.place .AA' ((S.pointMeasExp .alice W u).effect a))
        (fun u a => S.place .BA'' ((S.pointMeasExp .bob W u).effect a))
        S.psiHat ≤ 2 * ((Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε) := by
  let X := Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P
  let R := _root_.MIPStarRE.QPBT.PauliRegister P
  let μ := _root_.LIDT.MIPStarRE.LDT.uniformDistribution X
  let e := _root_.MIPStarRE.QPBT.ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let add : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P → _root_.MIPStarRE.QPBT.PauliScalar P :=
    fun p => p.1 + p.2
  let fineA : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P)
      (S.toStrategy.ιA × R) := fun u => S.pointTauMeas .alice W u
  let fineB : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P)
      ((S.toStrategy.ιB × R) × (R × R)) := fun u =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.pointTauMeas .bob W u)
  have hfine :
      _root_.MIPStarRE.QPBT.consistencyDefect μ
          (fun u p => _root_.MIPStarRE.QPBT.heteroKron ((fineA u).effect p)
            (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun u p => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × R))
            ((fineB u).effect p))
          (_root_.MIPStarRE.QPBT.reindexState e S.psiHat) ≤ (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
    calc
      _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
          (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect a) 1)
          (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeas .bob W u).effect a))
          S.toStrategy.ψ := by
        convert _root_.MIPStarRE.QPBT.ProjectiveSetting.pointTauConsistency_aaBa_eq S W using 1
        all_goals rfl
      _ ≤ (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := _root_.MIPStarRE.QPBT.point_self_consistency_le S W
  have hcoarse :
      _root_.MIPStarRE.QPBT.consistencyDefect μ
          (fun u a => _root_.MIPStarRE.QPBT.heteroKron (((fineA u).postprocess add).effect a)
            (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun u a => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × R))
            (((fineB u).postprocess add).effect a))
          (_root_.MIPStarRE.QPBT.reindexState e S.psiHat) ≤ (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε :=
    le_trans (_root_.MIPStarRE.QPBT.consistencyDefect_postprocess_le μ fineA fineB
      (_root_.MIPStarRE.QPBT.reindexState e S.psiHat) add) hfine
  have hdist := _root_.MIPStarRE.QPBT.WinImplications.opFamilyDistSq_placed_le_of_consistencyDefect_le
    μ (fun u => (fineA u).postprocess add)
      (fun u => (fineB u).postprocess add) (_root_.MIPStarRE.QPBT.reindexState e S.psiHat) hcoarse
  have hAeff (u : X) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
      ((fineA u).postprocess add).effect a =
        (S.pointMeasExp .alice W u).effect a := by
    convert
      (S.pointMeasExp_effect_eq_pointTauMeas_postprocess .alice W u a).symm
        using 1 <;> rfl
  have hBeff (u : X) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
      ((fineB u).postprocess add).effect a =
        _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeasExp .bob W u).effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (R × R)) := by
    calc
      _ = _root_.MIPStarRE.QPBT.heteroKron
          (((S.pointTauMeas .bob W u).postprocess add).effect a)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (R × R)) := by
        convert _root_.MIPStarRE.QPBT.leftPlacedMeasurement_postprocess_effect
          (S.pointTauMeas .bob W u) add a using 1 <;> rfl
      _ = _ := by
        rw [← S.pointMeasExp_effect_eq_pointTauMeas_postprocess .bob W u a]
  have hnorm (u : X) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (S.place .AA' ((S.pointMeasExp .alice W u).effect a) -
            S.place .BA'' ((S.pointMeasExp .bob W u).effect a)) S.psiHat‖ =
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron (((fineA u).postprocess add).effect a) 1 -
            _root_.MIPStarRE.QPBT.heteroKron 1 (((fineB u).postprocess add).effect a))
          (_root_.MIPStarRE.QPBT.reindexState e S.psiHat)‖ := by
    let OA : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × R) :=
      (S.pointMeasExp .alice W u).effect a
    let OB : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιB × R) :=
      (S.pointMeasExp .bob W u).effect a
    have hop :
        _root_.MIPStarRE.QPBT.reindexOp e
            (_root_.MIPStarRE.QPBT.heteroKron OA
                (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιB × R) × (R × R))) -
              _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × R))
                (_root_.MIPStarRE.QPBT.heteroKron OB (1 : _root_.LIDT.MIPStarRE.Quantum.Op (R × R)))) =
          S.place .AA' OA - S.place .BA'' OB := by
      rw [_root_.MIPStarRE.QPBT.WinImplications.reindexOp_sub,
        _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_left, _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_right]
    rw [hAeff, hBeff, _root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState]
    change ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place .AA' OA - S.place .BA'' OB)
        S.psiHat‖ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.reindexOp e
          (_root_.MIPStarRE.QPBT.heteroKron OA (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιB × R) × (R × R))) -
            _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × R))
              (_root_.MIPStarRE.QPBT.heteroKron OB (1 : _root_.LIDT.MIPStarRE.Quantum.Op (R × R))))) S.psiHat‖
    rw [hop]
  change _root_.MIPStarRE.QPBT.opFamilyDistSq μ
      (fun u a => S.place .AA' ((S.pointMeasExp .alice W u).effect a))
      (fun u a => S.place .BA'' ((S.pointMeasExp .bob W u).effect a))
      S.psiHat ≤ _
  calc
    _ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron (((fineA u).postprocess add).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 (((fineB u).postprocess add).effect a))
        (_root_.MIPStarRE.QPBT.reindexState e S.psiHat) := by
      unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro u
      apply Finset.sum_congr rfl
      intro a _
      rw [hnorm]
    _ ≤ 2 * ((Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε) := hdist
