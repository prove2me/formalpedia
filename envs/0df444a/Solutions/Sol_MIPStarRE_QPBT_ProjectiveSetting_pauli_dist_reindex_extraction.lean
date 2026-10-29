-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.pauli_dist_reindex_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:24:57.627841+00:00
-- url     : https://prove2.me/submissions/bb3b1d4b-b1cc-42c6-915d-2ea7eb01f13c

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.pauli_dist_reindex_extraction.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

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
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Extraction/StateExtraction.lean. -/
/-!
# Normalized state extraction from a supplied global witness

The Pauli disagreement estimate is transported to auxiliary/EPR coordinates.
Averaging and the EPR projection identity then select a normalized auxiliary
state, including the case where the unnormalized projection vanishes.

## References

Blueprint `lem:qld-unitary`, Item 1; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1715-1783`;
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix Classical

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum LIDT.MIPStarRE.LDT DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)

private theorem reindex_extracted_left (T : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm
      (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
        (_root_.MIPStarRE.QPBT.heteroKron T (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)))) =
      S.placeSide .alice (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) T) := by
  classical
  ext row col
  change (if ((row.1.1, row.1.2.1), (row.2.1, row.2.2.1)) =
      ((col.1.1, col.1.2.1), (col.2.1, col.2.2.1)) then (1 : ℂ) else 0) *
      (T row.1.2.2 col.1.2.2 * if row.2.2.2 = col.2.2.2 then 1 else 0) =
    ((if (row.1.1, row.1.2.1) = (col.1.1, col.1.2.1) then 1 else 0) *
      T row.1.2.2 col.1.2.2) *
      (if ((row.2.1, row.2.2.1), row.2.2.2) =
        ((col.2.1, col.2.2.1), col.2.2.2) then 1 else 0)
  simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]
  split_ifs <;> rfl

private theorem reindex_extracted_right (T : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm
      (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
        (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) T)) =
      S.placeSide .bob (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) T) := by
  classical
  ext row col
  change (if ((row.1.1, row.1.2.1), (row.2.1, row.2.2.1)) =
      ((col.1.1, col.1.2.1), (col.2.1, col.2.2.1)) then (1 : ℂ) else 0) *
      ((if row.1.2.2 = col.1.2.2 then 1 else 0) * T row.2.2.2 col.2.2.2) =
    (if ((row.1.1, row.1.2.1), row.1.2.2) =
      ((col.1.1, col.1.2.1), col.1.2.2) then 1 else 0) *
      ((if (row.2.1, row.2.2.1) = (col.2.1, col.2.2.1) then 1 else 0) *
        T row.2.2.2 col.2.2.2)
  simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, one_mul, zero_mul, mul_zero]
  split_ifs <;> rfl



end ProjectiveSetting





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
# Normalized state extraction from a supplied global witness

The Pauli disagreement estimate is transported to auxiliary/EPR coordinates.
Averaging and the EPR projection identity then select a normalized auxiliary
state, including the case where the unnormalized projection vanishes.

## References

Blueprint `lem:qld-unitary`, Item 1; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1715-1783`;
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/



open scoped BigOperators Matrix Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum LIDT.MIPStarRE.LDT MIPStarRE.QPBT.DistanceCalculus



open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)

theorem solution
    (theta : EuclideanSpace ℂ (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB))
    (W : _root_.MIPStarRE.QPBT.PauliKind) (j : Fin P.model.basisDim) :
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
      (fun u => _root_.MIPStarRE.QPBT.heteroKron
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauObservable W u) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))))
      (fun u => _root_.MIPStarRE.QPBT.heteroKron
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
        (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) (_root_.MIPStarRE.QPBT.tauObservable W u)))
      (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm theta) =
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
      (fun u => S.placeSide .alice (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice))
        (_root_.MIPStarRE.QPBT.tauObservable W (P.model.basis j • u))))
      (fun u => S.placeSide .bob (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob))
        (_root_.MIPStarRE.QPBT.tauObservable W (P.model.basis j • u)))) theta := by
  classical
  unfold _root_.MIPStarRE.QPBT.opDistSq _root_.MIPStarRE.QPBT.opFamilyDistSq
  simp only [Fintype.sum_unique]
  simp_rw [_root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState,
    _root_.MIPStarRE.QPBT.WinImplications.reindexOp_sub, S.reindex_extracted_left, S.reindex_extracted_right]
  let e : _root_.MIPStarRE.QPBT.PauliRegister P ≃ _root_.MIPStarRE.QPBT.PauliRegister P := Equiv.piCongrRight
    (fun _ => Equiv.mulLeft₀ (P.model.basis j) (P.model.basis.ne_zero j))
  have he (u : _root_.MIPStarRE.QPBT.PauliRegister P) : e u = P.model.basis j • u := rfl
  simpa only [Equiv.symm_symm, he] using _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv e.symm
    (fun u => ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (S.placeSide .alice (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) (_root_.MIPStarRE.QPBT.tauObservable W u)) -
        S.placeSide .bob (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) (_root_.MIPStarRE.QPBT.tauObservable W u)))
      theta‖ ^ 2)
