-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.pointTauConsistency_aaBa_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:28:55.958814+00:00
-- url     : https://prove2.me/submissions/12d147fb-63f8-4107-9166-0668bbf702ab

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.pointTauConsistency_aaBa_eq.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_consistencyDefect_eq_one_sub_overlap
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_stateQForm_place_AA_prime_mul_BA_prime_prime
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_sum_tauPointProj_pair_stateQForm_eprState
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_stateQForm_reindexState

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
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A 1 * _root_.MIPStarRE.QPBT.heteroKron 1 B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  congr 1
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor A B































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

/- Source helpers from QPBT/Observables/WinImplications/FactorTransport.lean. -/
/-!
# Transport of the winning implications to the interchanged tensor factor

This module carries the state-dependent functionals of the winning
implications across the interchange of the two tensor factors.  The
factor-interchanged conclusions of `lem:qld-win-implications` are stated with
the second player on the left factor and the reindexed state
`ProjectiveSetting.swappedState`; the lemmas here identify those quantities
with the ones proved on `S.toStrategy.psi`, so that the second pass of
`lem:qld-win-implications-obs` can reuse the first pass verbatim on the
interchanged side.

## References

The declarations support the trailing clause of `lem:qld-win-implications` and
the second assertion of `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:701-703`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:227,309-362`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reindexing the identity and the strategy state -/





/-! ## Transport of the consistency defect -/



/-- Reindexing an operator along an equivalence is multiplicative.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M N : _root_.LIDT.MIPStarRE.Quantum.Op κ) :
    _root_.MIPStarRE.QPBT.reindexOp e (M * N) = _root_.MIPStarRE.QPBT.reindexOp e M * _root_.MIPStarRE.QPBT.reindexOp e N := by
  ext i j
  change (M * N) (e i) (e j) = ∑ k : ι, M (e i) (e k) * N (e k) (e j)
  rw [Matrix.mul_apply, ← e.sum_comp (fun l : κ => M (e i) l * N l (e j))]





/-! ## Transport of the phase-signed operator distance -/





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
attribute [local instance] _root_.MIPStarRE.QPBT.pauliEdgeNonemptyPointConsistency

set_option synthInstance.maxSize 400 in

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u p => _root_.MIPStarRE.QPBT.heteroKron ((S.pointTauMeas .alice W u).effect p)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) ×
            (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))))
        (fun u p => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
          (_root_.MIPStarRE.QPBT.heteroKron ((S.pointTauMeas .bob W u).effect p)
            (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))))
        (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ := by
  let X := Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P
  let R := _root_.MIPStarRE.QPBT.PauliRegister P
  let μ := _root_.LIDT.MIPStarRE.LDT.uniformDistribution X
  let e := _root_.MIPStarRE.QPBT.ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let fineA : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P)
      (S.toStrategy.ιA × R) := fun u => S.pointTauMeas .alice W u
  let fineB : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P)
      ((S.toStrategy.ιB × R) × (R × R)) := fun u =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.pointTauMeas .bob W u)
  let A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P)
      ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R))) :=
    fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (fineA u)
  let B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P)
      ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R))) :=
    fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (fineB u)
  let pointA : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P)
      (S.toStrategy.ιA × S.toStrategy.ιB) := fun u =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (S.pointMeas .alice W u)
  let pointB : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P)
      (S.toStrategy.ιA × S.toStrategy.ιB) := fun u =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (S.pointMeas .bob W u)
  have hμ : μ.IsProbability := _root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability X
  have hgroup : ‖_root_.MIPStarRE.QPBT.reindexState e S.psiHat‖ = 1 := by
    rw [_root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_norm]
  have hfine :
      _root_.MIPStarRE.QPBT.consistencyDefect μ (fun u p => (A u).effect p)
          (fun u p => (B u).effect p) (_root_.MIPStarRE.QPBT.reindexState e S.psiHat) =
        1 - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun u => ∑ p,
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.reindexState e S.psiHat)
            ((A u).effect p * (B u).effect p)) :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ A B _ hμ hgroup
  have hpoint :
      _root_.MIPStarRE.QPBT.consistencyDefect μ (fun u a => (pointA u).effect a)
          (fun u a => (pointB u).effect a) S.toStrategy.ψ =
        1 - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun u => ∑ a,
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ
            ((pointA u).effect a * (pointB u).effect a)) :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ pointA pointB _ hμ
      S.toStrategy.ψ_norm
  change _root_.MIPStarRE.QPBT.consistencyDefect μ (fun u p => (A u).effect p)
      (fun u p => (B u).effect p) (_root_.MIPStarRE.QPBT.reindexState e S.psiHat) =
    _root_.MIPStarRE.QPBT.consistencyDefect μ (fun u a => (pointA u).effect a)
      (fun u a => (pointB u).effect a) S.toStrategy.ψ
  rw [hfine, hpoint]
  congr 1
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro u
  have hterm (p : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) :
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.reindexState e S.psiHat)
          ((A u).effect p * (B u).effect p) =
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ
            (_root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect p.1)
              ((S.pointMeas .bob W u).effect p.1)) *
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
            (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u p.2) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u p.2)) := by
    let OA : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × R) :=
      (S.pointTauMeas .alice W u).effect p
    let OB : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιB × R) :=
      (S.pointTauMeas .bob W u).effect p
    have hop :
        _root_.MIPStarRE.QPBT.reindexOp e (_root_.MIPStarRE.QPBT.heteroKron OA
          (_root_.MIPStarRE.QPBT.heteroKron OB (1 : _root_.LIDT.MIPStarRE.Quantum.Op (R × R)))) =
        S.place .AA' OA * S.place .BA'' OB := by
      rw [show _root_.MIPStarRE.QPBT.heteroKron OA (_root_.MIPStarRE.QPBT.heteroKron OB (1 : _root_.LIDT.MIPStarRE.Quantum.Op (R × R))) =
          _root_.MIPStarRE.QPBT.heteroKron OA 1 *
            _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.heteroKron OB (1 : _root_.LIDT.MIPStarRE.Quantum.Op (R × R))) by
        rw [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one, Matrix.one_mul]]
      rw [_root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul,
        _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_left, _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_right]
    simp only [A, B, fineA, fineB, _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement,
      _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne]
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq,
      _root_.MIPStarRE.QPBT.WinImplications.stateQForm_reindexState]
    change _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (_root_.MIPStarRE.QPBT.reindexOp e (_root_.MIPStarRE.QPBT.heteroKron OA (_root_.MIPStarRE.QPBT.heteroKron OB (1 : _root_.LIDT.MIPStarRE.Quantum.Op (R × R))))) = _
    rw [hop]
    convert _root_.MIPStarRE.QPBT.ProjectiveSetting.stateQForm_place_AA_prime_mul_BA_prime_prime S
        ((S.pointMeas .alice W u).effect p.1)
        ((S.pointMeas .bob W u).effect p.1) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u p.2)
      (Matrix.nonneg_iff_posSemidef.mp
        ((S.pointMeas .alice W u).pos p.1)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        ((S.pointMeas .bob W u).pos p.1)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        ((_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointMeas W u).pos p.2)).isHermitian using 1
    all_goals simp [OA, OB]
    all_goals rfl
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : _root_.MIPStarRE.QPBT.PauliScalar P, ∑ y : _root_.MIPStarRE.QPBT.PauliScalar P,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ
            (_root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect x)
              ((S.pointMeas .bob W u).effect x)) *
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState R)
            (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u y) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u y))) =
      (∑ x : _root_.MIPStarRE.QPBT.PauliScalar P,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ
          (_root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect x)
            ((S.pointMeas .bob W u).effect x))) *
        ∑ y : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState R)
          (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u y) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u y)) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ
          ((pointA u).effect a * (pointB u).effect a) := by
      rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.sum_tauPointProj_pair_stateQForm_eprState, mul_one]
      simp only [pointA, pointB, _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement,
        _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne]
      simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq]
