-- Prove2me | solution 1 for MIPStarRE.QPBT.tildeObs_opDistSq_le_four_consistencyDefect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:16:53.66474+00:00
-- url     : https://prove2.me/submissions/d83c5353-8f0a-4518-ae9c-4724ac54284d

-- Generated proof for MIPStarRE.QPBT.tildeObs_opDistSq_le_four_consistencyDefect.
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
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_stateQForm_reindexState
import Theorems.Thm_MIPStarRE_QPBT_basis_character_opDistSq_le_four_consistencyDefect
import Theorems.Thm_MIPStarRE_QPBT_sum_tildeM_eq_one
import Theorems.Thm_MIPStarRE_QPBT_tildeM_isProj

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
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

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
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rfl



































end MIPStarRE.QPBT.DistanceCalculus

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
# Finite-character estimates for extracted observables

Parseval identifies the uniform average over field characters with the sum of
squared outcome norms. A fixed binary basis character instead admits a bound
by four times the consistency defect, using binary postprocessing.

## References

These are finite-dimensional auxiliary results for blueprint
`lem:qld-construct-the-paulis`, Item 2, and paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1542-1551`.
They do not assert the preceding pulled-apart measurement comparison
`eq:qld-pulling-cons`, whose extraction obligation is recorded under
issue Dengnifer/MIPStarRE-QPBT-bak#123 in `docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open MIPStarRE.QPBT.WinImplications

theorem solution
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (j : Fin P.model.basisDim) :
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
      (fun u => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeObs w .alice W u j))
      (fun u => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeObs w .bob W u j)) S.psiHat ≤
      4 * _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
        (fun u a => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeM w .alice W u a))
        (fun u a => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeM w .bob W u a)) S.psiHat := by
  classical
  let M (side : _root_.MIPStarRE.QPBT.PlayerSide) (u : _root_.MIPStarRE.QPBT.PauliRegister P) :
      _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P) (_root_.MIPStarRE.QPBT.ExtractionBlock P (S.LocalSpace side)) :=
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne (_root_.MIPStarRE.QPBT.tildeM w side W u)
      (fun a => (_root_.MIPStarRE.QPBT.tildeM_isProj w side W u a).nonneg) (_root_.MIPStarRE.QPBT.sum_tildeM_eq_one w side W u)
  let e := _root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  have h := _root_.MIPStarRE.QPBT.basis_character_opDistSq_le_four_consistencyDefect
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P)) (M .alice) (M .bob)
    (_root_.MIPStarRE.QPBT.reindexState e S.psiHat) j
  have hd : _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
      (fun u => _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tildeObs w .alice W u j) 1)
      (fun u => _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.tildeObs w .bob W u j)) (_root_.MIPStarRE.QPBT.reindexState e S.psiHat) =
      _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
        (fun u => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeObs w .alice W u j))
        (fun u => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeObs w .bob W u j)) S.psiHat := by
    unfold _root_.MIPStarRE.QPBT.opDistSq _root_.MIPStarRE.QPBT.opFamilyDistSq
    simp only [Fintype.sum_unique]
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro u
    rw [_root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState, _root_.MIPStarRE.QPBT.WinImplications.reindexOp_sub]
    rfl
  have hc : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tildeM w .alice W u a) 1)
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.tildeM w .bob W u a)) (_root_.MIPStarRE.QPBT.reindexState e S.psiHat) =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
        (fun u a => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeM w .alice W u a))
        (fun u a => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeM w .bob W u a)) S.psiHat := by
    unfold _root_.MIPStarRE.QPBT.consistencyDefect
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro u
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b
    · simp only [hab, if_true]
    · simp only [if_neg hab, _root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm]
      rw [_root_.MIPStarRE.QPBT.WinImplications.stateQForm_reindexState, _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul]
      rfl
  change _root_.MIPStarRE.QPBT.opDistSq _ (fun u => _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tildeObs w .alice W u j) 1)
    (fun u => _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.tildeObs w .bob W u j)) _ ≤
      4 * _root_.MIPStarRE.QPBT.consistencyDefect _ (fun u a => _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tildeM w .alice W u a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.tildeM w .bob W u a)) _ at h
  rwa [hd, hc] at h
