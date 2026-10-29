-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.stateQForm_pairState_eq_AA_prime_BA_prime_prime
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:16:02.753002+00:00
-- url     : https://prove2.me/submissions/4cd6974f-1e7b-4afb-8c43-4f2e607b8cee

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.stateQForm_pairState_eq_AA'_BA''.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_StateTransport
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_stateQForm_reindexState
import Theorems.Thm_MIPStarRE_QPBT_applyOperatorToState_heteroKron_vecTensor
import Theorems.Thm_MIPStarRE_QPBT_inner_vecTensor

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Combining/ExtendedLineGame/StateTransport.lean. -/
/-!
# Correlations on the two-player expanded state

The six-register state of `eq:def-psihat` factors as the two-player state
`ExtendedLineGame.pairState` and an unused normalized EPR pair, for each of
the opposite register placements `AA'`--`BA''` and `AB''`--`BB'`. Therefore
arbitrary Hermitian operators on the expanded local spaces have the same
correlation in the two descriptions. An individual operator need not factor
between its strategy register and its Pauli register.

These are formalization-only auxiliary identities for the strategy construction
in the proof of `lem:qld-4-7`. They do not establish its passing value or the
existence of its input measurements. Parent issue Dengnifer/MIPStarRE-QPBT-bak#119 remains open.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-372`,
  equation `eq:def-psihat`.
- The same source, `lem:qld-4-7`, proof at lines 1279-1288.
- Blueprint `def:expanded-state`, `def:symmetric-equivalents`, and `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#302.
-/

@[expose] public section

-- The six-register products require the same instance-search size as ExpandedPlacement.
set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open ProjectiveSetting

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : Real}





/-- In the `AA'`--`BA''` grouping, the expanded state is `pairState` tensored
with the unused EPR pair. This is a coordinate consequence of `eq:def-psihat`,
not an assumption on the strategy or its measurement effects. -/
theorem reindexState_aaBaRegrouping_psiHat (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) :
    _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.ExtendedLineGame.aaBaRegrouping setting) setting.psiHat =
      _root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) := by
  ext p
  rfl







end ExtendedLineGame

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

/-- The identity operator acts trivially on a state. Formalization-only support
for blueprint `def:strategy-observables`. -/
theorem applyOperatorToState_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ψ = ψ := by
  ext i
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]















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





/-- A Hermitian Kronecker product evaluated on a coordinate tensor factors as
the product of the two real quadratic forms. Formalization-only support for
the EPR product calculation in `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem stateQForm_vecTensor_heteroKron {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : _root_.LIDT.MIPStarRE.Quantum.Op ι) (B : _root_.LIDT.MIPStarRE.Quantum.Op κ) (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.vecTensor u v) (_root_.MIPStarRE.QPBT.heteroKron A B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm u A * _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm v B := by
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
  rw [_root_.MIPStarRE.QPBT.applyOperatorToState_heteroKron_vecTensor, _root_.MIPStarRE.QPBT.inner_vecTensor]
  have himA : (inner ℂ u (_root_.MIPStarRE.QPBT.applyOperatorToState A u)).im = 0 := by
    exact ((Matrix.isSymmetric_toEuclideanLin_iff (A := A)).mpr hA).im_inner_self_apply u
  have himB : (inner ℂ v (_root_.MIPStarRE.QPBT.applyOperatorToState B v)).im = 0 := by
    exact ((Matrix.isSymmetric_toEuclideanLin_iff (A := B)).mpr hB).im_inner_self_apply v
  rw [Complex.mul_re, himA, himB]
  ring

/-- Kronecker products preserve Hermiticity. -/
theorem heteroKron_isHermitian {ι κ : Type*} (A : _root_.LIDT.MIPStarRE.Quantum.Op ι) (B : _root_.LIDT.MIPStarRE.Quantum.Op κ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (_root_.MIPStarRE.QPBT.heteroKron A B).IsHermitian := by
  rw [Matrix.IsHermitian]
  unfold _root_.MIPStarRE.QPBT.heteroKron
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, hA.eq, hB.eq]

/-- The real quadratic form of the identity is the squared vector norm. -/
theorem stateQForm_one_eq_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm u (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) = ‖u‖ ^ 2 := by
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
  rw [_root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_one]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) u)



end

end MIPStarRE.QPBT

/-!
# Correlations on the two-player expanded state

The six-register state of `eq:def-psihat` factors as the two-player state
`ExtendedLineGame.pairState` and an unused normalized EPR pair, for each of
the opposite register placements `AA'`--`BA''` and `AB''`--`BB'`. Therefore
arbitrary Hermitian operators on the expanded local spaces have the same
correlation in the two descriptions. An individual operator need not factor
between its strategy register and its Pauli register.

These are formalization-only auxiliary identities for the strategy construction
in the proof of `lem:qld-4-7`. They do not establish its passing value or the
existence of its input measurements. Parent issue Dengnifer/MIPStarRE-QPBT-bak#119 remains open.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-372`,
  equation `eq:def-psihat`.
- The same source, `lem:qld-4-7`, proof at lines 1279-1288.
- Blueprint `def:expanded-state`, `def:symmetric-equivalents`, and `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#302.
-/



-- The six-register products require the same instance-search size as ExpandedPlacement.
set_option synthInstance.maxSize 400

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.ProjectiveSetting



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : Real}

theorem solution (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
    (A : _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace .alice))
    (B : _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace .bob))
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) (_root_.MIPStarRE.QPBT.heteroKron A B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
        (setting.place .AA' A * setting.place .BA'' B) := by
  let I : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P) := 1
  have hop : _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.ExtendedLineGame.aaBaRegrouping setting) (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron A B) I) =
      setting.place .AA' A * setting.place .BA'' B := by
    change _root_.LIDT.MIPStarRE.Quantum.Op (setting.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P) at A
    change _root_.LIDT.MIPStarRE.Quantum.Op (setting.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) at B
    change _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.ProjectiveSetting.aaBaBipartition P setting.toStrategy.ιA setting.toStrategy.ιB)
      (_root_.MIPStarRE.QPBT.reindexOp (Equiv.prodAssoc _ _ _).symm (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron A B) I)) = _
    rw [show _root_.MIPStarRE.QPBT.reindexOp (Equiv.prodAssoc _ _ _).symm
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron A B) I) = _root_.MIPStarRE.QPBT.heteroKron A (_root_.MIPStarRE.QPBT.heteroKron B I) from
      Matrix.kronecker_assoc A B I]
    rw [show _root_.MIPStarRE.QPBT.heteroKron A (_root_.MIPStarRE.QPBT.heteroKron B I) =
        _root_.MIPStarRE.QPBT.heteroKron A 1 * _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.heteroKron B I) by
      rw [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one, Matrix.one_mul]]
    exact (_root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul _ _ _).trans
      (congrArg₂ (fun X Y => X * Y)
        (_root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_left setting A)
        (_root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_right setting B))
  calc
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) (_root_.MIPStarRE.QPBT.heteroKron A B) =
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
          (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
          (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron A B) I) := by
      rw [_root_.MIPStarRE.QPBT.stateQForm_vecTensor_heteroKron _ _ _ _
        (_root_.MIPStarRE.QPBT.heteroKron_isHermitian A B hA hB) Matrix.isHermitian_one]
      simp [_root_.MIPStarRE.QPBT.stateQForm_one_eq_norm_sq, _root_.MIPStarRE.QPBT.eprState_norm]
    _ = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
        (setting.place .AA' A * setting.place .BA'' B) := by
      rw [← _root_.MIPStarRE.QPBT.ExtendedLineGame.reindexState_aaBaRegrouping_psiHat setting,
        _root_.MIPStarRE.QPBT.WinImplications.stateQForm_reindexState, hop]
