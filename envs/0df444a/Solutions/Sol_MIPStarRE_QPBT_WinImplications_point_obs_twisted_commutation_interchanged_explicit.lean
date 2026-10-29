-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.point_obs_twisted_commutation_interchanged_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:57:53.928191+00:00
-- url     : https://prove2.me/submissions/7ef3321a-d661-4060-8db4-e7b28fe64ac1

-- Generated proof for MIPStarRE.QPBT.WinImplications.point_obs_twisted_commutation_interchanged_explicit.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_InterchangedCommutation
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_point_obs_anticommutator_anticomm_le_bob_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_point_obs_commutator_comm_le_bob_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_twisted_commutation_of_halves

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/Defs.lean. -/
/-!
# Typed strategy measurements and point observables

This file fixes a projective, possibly heterogeneous strategy for the Pauli
basis test and extracts the typed measurement families used in the analysis.
Malformed answers are folded into a fixed valid answer, so the extracted
families remain complete measurements. The winning hypothesis bounds their
original wrong-form mass by the rejection probability. `Option` is used only
for the completed line-evaluation classes.

## References

The ambient strategy convention and the observable `W^r(u)` are in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190`,
corresponding to blueprint `def:strategy-observables`. The typed question
and answer forms come from blueprint `def:pauli-question-distribution` and
`def:pauli-win-predicate`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1225`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section







namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





























-- The support rewrites below elaborate the `Fintype` instance of
-- `PauliEdge × PauliSpace P`, whose nested sigma/sum instance chain exceeds the
-- default recursion depth.
































































/-- The zero-label point observable is the identity by measurement completeness. -/
theorem pointObs_zero (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    S.pointObs side W 0 u = 1 := by
  classical
  simpa [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs, _root_.MIPStarRE.QPBT.fixedBinTrace, _root_.MIPStarRE.QPBT.phaseSign] using (S.pointMeas side W u).sum_eq_one

/-- The point observable squares to the identity. This is the assertion that
the operator in `def:strategy-observables` has eigenvalues in `{+1,-1}`;
paper `14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
theorem pointObs_sq_eq_one (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (r : _root_.MIPStarRE.QPBT.PauliScalar P) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    S.pointObs side W r u * S.pointObs side W r u = 1 := by
  haveI : CharP (_root_.MIPStarRE.QPBT.PauliScalar P) 2 :=
    (Algebra.charP_iff (ZMod 2) (_root_.MIPStarRE.QPBT.PauliScalar P) 2).mp (ZMod.charP 2)
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs_mul, CharTwo.add_self_eq_zero, _root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs_zero]

/-- The point observable is Hermitian. This is the self-adjoint part of the
observable assertion following `eq:qld-strat-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
theorem pointObs_isHermitian (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (r : _root_.MIPStarRE.QPBT.PauliScalar P) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointObs side W r u).IsHermitian := by
  classical
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs, Matrix.IsHermitian]
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Matrix.conjTranspose_smul, _root_.MIPStarRE.QPBT.star_phaseSign]
  rw [(Matrix.nonneg_iff_posSemidef.mp
    ((S.pointMeas side W u).pos a)).isHermitian.eq]

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

/-- The identity operator acts trivially on a state. Formalization-only support
for blueprint `def:strategy-observables`. -/
theorem applyOperatorToState_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ψ = ψ := by
  ext i
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]

/-- Reindexing an operator is computed entrywise, hence commutes with
subtraction. Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_sub {ι ι' : Type*} (e : ι ≃ ι') (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι') :
    _root_.MIPStarRE.QPBT.reindexOp e (M - N) = _root_.MIPStarRE.QPBT.reindexOp e M - _root_.MIPStarRE.QPBT.reindexOp e N := rfl

/-- Interchanging the two tensor factors turns a Kronecker product into the
product of the exchanged factors. Formalization-only support for the
interchanged conclusions of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_prodComm_heteroKron {ιA ιB : Type*}
    (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.reindexOp (Equiv.prodComm ιA ιB) (_root_.MIPStarRE.QPBT.heteroKron B A) = _root_.MIPStarRE.QPBT.heteroKron A B := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.reindexOp, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.reindex_apply, mul_comm]

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

/- Source helpers from QPBT/Observables/WinImplications/AnticommutingObs.lean. -/
/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/





/-- The strategy point observable is a reflection. Paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:573-610`. -/
theorem pointObs_conjTranspose_mul_self {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (r : _root_.MIPStarRE.QPBT.PauliScalar P) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointObs side W r u)ᴴ * S.pointObs side W r u = 1 := by
  rw [(S.pointObs_isHermitian side W r u).eq]
  exact S.pointObs_sq_eq_one side W r u



/-! ## The anticommuting half of the twisted commutation -/





















end WinImplications

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

/-- Reindexing the identity operator gives the identity operator.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_one {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) : _root_.MIPStarRE.QPBT.reindexOp e (1 : _root_.LIDT.MIPStarRE.Quantum.Op κ) = (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.reindexOp, Matrix.one_apply, e.injective.eq_iff]

/-- The interchanged strategy state is again a unit vector.  This is needed to
chain consistency relations on the interchanged side of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`,
paper `14_analysis_of_the_pauli_basis_test.tex:227`. -/
theorem norm_swappedState {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : ‖S.swappedState‖ = 1 := by
  have h := _root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState
    (Equiv.prodComm S.toStrategy.ιA S.toStrategy.ιB)
    (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιB × S.toStrategy.ιA)) S.toStrategy.ψ
  rw [_root_.MIPStarRE.QPBT.WinImplications.reindexOp_one, _root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_one, _root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_one] at h
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.swappedState, h]
  exact S.toStrategy.ψ_norm

/-! ## Transport of the consistency defect -/









/-! ## Transport of the phase-signed operator distance -/

/-- Reindexing an operator commutes with scalar multiplication.
Formalization-only support for the second assertion of
`lem:qld-win-implications-obs`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem reindexOp_smul {ι κ : Type*} (e : ι ≃ κ) (c : ℂ) (M : _root_.LIDT.MIPStarRE.Quantum.Op κ) :
    _root_.MIPStarRE.QPBT.reindexOp e (c • M) = c • _root_.MIPStarRE.QPBT.reindexOp e M := rfl

/-- The phase-signed operator distance of two left-placed families is
unchanged by interchanging the tensor factors of the families and the state.
This is the transport used by the second assertion of
`lem:qld-win-implications-obs`, blueprint
`ch14_qpbt_observables.tex:761-794`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`. -/
theorem opDistSq_smul_swappedState {X ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (c : X → ℂ) (M N : X → _root_.LIDT.MIPStarRE.Quantum.Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.opDistSq μ (fun x => _root_.MIPStarRE.QPBT.heteroKron (M x) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA))
        (fun x => c x • _root_.MIPStarRE.QPBT.heteroKron (N x) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA))
        (_root_.MIPStarRE.QPBT.reindexState (Equiv.prodComm ιA ιB) ψ) =
      _root_.MIPStarRE.QPBT.opDistSq μ (fun x => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (M x))
        (fun x => c x • _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (N x)) ψ := by
  unfold _root_.MIPStarRE.QPBT.opDistSq _root_.MIPStarRE.QPBT.opFamilyDistSq
  refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
  intro x
  refine Finset.sum_congr rfl ?_
  intro _ _
  rw [_root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState]
  congr 2
  rw [_root_.MIPStarRE.QPBT.WinImplications.reindexOp_sub, _root_.MIPStarRE.QPBT.WinImplications.reindexOp_smul, _root_.MIPStarRE.QPBT.WinImplications.reindexOp_prodComm_heteroKron,
    _root_.MIPStarRE.QPBT.WinImplications.reindexOp_prodComm_heteroKron]

end WinImplications

end

end MIPStarRE.QPBT

/-!
# The factor-interchanged phase-signed commutation relation

Interchanging the tensor factors places Bob's point observables on the left.
The reversed consistency estimates of `lem:qld-win-implications` and Alice's
Magic Square anticommutation give the bound, which is then transported to the
original state. This proves the factor-interchanged relation in
`lem:qld-win-implications-obs`.

## References

The declarations formalize the trailing clause of
`lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-362`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications



/-! ## The interchanged consistency inputs on the interchanged state -/















/-! ## The two halves on Bob's factor -/











/-! ## The interchanged twisted commutation relation -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyInterchanged

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε),
      0 ≤ ε →
      _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P))
        (fun ω => _root_.MIPStarRE.QPBT.heteroKron 1
          (S.pointObs .bob .X ω.2.2.1 ω.1 *
            S.pointObs .bob .Z ω.2.2.2 ω.2.1))
        (fun ω => _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          _root_.MIPStarRE.QPBT.heteroKron 1
            (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1))
        S.toStrategy.ψ ≤
          (2 * (1024 * (2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
              1024 * Real.sqrt (4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) +
            (96 * (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
              3551040 * (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) + 4) *
            Real.sqrt ε := by
  classical
  intro P ε S hε
  have hswapped := _root_.MIPStarRE.QPBT.WinImplications.twisted_commutation_of_halves
    (fun ω => S.pointObs .bob .X ω.2.2.1 ω.1)
    (fun ω => S.pointObs .bob .Z ω.2.2.2 ω.2.1)
    S.swappedState (_root_.MIPStarRE.QPBT.WinImplications.norm_swappedState S)
    (fun ω => _root_.MIPStarRE.QPBT.WinImplications.pointObs_conjTranspose_mul_self S .bob .X ω.2.2.1 ω.1)
    (fun ω => _root_.MIPStarRE.QPBT.WinImplications.pointObs_conjTranspose_mul_self S .bob .Z ω.2.2.2 ω.2.1)
    hε (by positivity) (by positivity)
    (_root_.MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_bob_explicit P ε S hε)
    (_root_.MIPStarRE.QPBT.WinImplications.point_obs_anticommutator_anticomm_le_bob_explicit P ε S hε)
  have htransport := _root_.MIPStarRE.QPBT.WinImplications.opDistSq_smul_swappedState
    (ιA := S.toStrategy.ιA) (ιB := S.toStrategy.ιB)
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P))
    (fun ω => _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2))
    (fun ω => S.pointObs .bob .X ω.2.2.1 ω.1 *
      S.pointObs .bob .Z ω.2.2.2 ω.2.1)
    (fun ω => S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
      S.pointObs .bob .X ω.2.2.1 ω.1) S.toStrategy.ψ
  exact le_of_eq_of_le htransport.symm hswapped
