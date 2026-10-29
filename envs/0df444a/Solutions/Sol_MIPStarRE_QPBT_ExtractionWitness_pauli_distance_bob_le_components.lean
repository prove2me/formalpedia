-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtractionWitness.pauli_distance_bob_le_components
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:53:53.239244+00:00
-- url     : https://prove2.me/submissions/f8b39746-b7bb-420c-a039-bb8b78603d18

-- Generated proof for MIPStarRE.QPBT.ExtractionWitness.pauli_distance_bob_le_components.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_QPBT_QPBT_Extraction_PauliTransport
import Definitions.Def_QPBT_QPBT_Extraction_Unitary
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Definitions.Def_QPBT_QPBT_Test_Soundness_Ancilla
import Definitions.Def_QPBT_QPBT_Test_Soundness_StateTransfer
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtractionWitness_isometryTensor_eq
import Theorems.Thm_MIPStarRE_QPBT_sum_norm_rightTensor_conjIsometry_sub_sq_le

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
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
end MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Combining/Points/PlacementSupport.lean. -/
/-!
# Placement calculus on the expanded state

This module records the algebra of the four register placements used by the
combining argument: a placement is a unital `*`-homomorphism, placements on
opposite register pairs commute, and the crosswise exchange of the two EPR
pairs of the expanded state carries the placement `AA'` to `AB''` and `BA''`
to `BB'` while fixing the expanded state.  The last fact transfers every
state-dependent distance between the two bipartition schemes of
`def:symmetric-equivalents` without assuming a symmetric strategy.

## References

The placements are those of `def:symmetric-equivalents`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
placement module proves EPR-exchange invariance for the involution
`(A' B'')(A'' B')`, which fixes `A` and `B`, in
`ProjectiveSetting.reindexState_eprCrossSwap_psiHat`; its use for
`lem:qld-4-10` is analyzed in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## Placements as reindexed tensor factors -/









/-- Reindexing an operator commutes with the conjugate transpose. -/
theorem reindexOp_conjTranspose {ι κ : Type*} (e : ι ≃ κ) (M : _root_.LIDT.MIPStarRE.Quantum.Op κ) :
    _root_.MIPStarRE.QPBT.reindexOp e Mᴴ = (_root_.MIPStarRE.QPBT.reindexOp e M)ᴴ := by
  ext i j
  rfl



/-! ## The placement is a unital `*`-homomorphism -/























end ProjectiveSetting

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

/- Source helpers from QPBT/Extraction/PointConsistencyPrime.lean. -/
/-!
# Point consistency with Alice's pulled-apart measurement

This module proves the register-interchanged overlap calculation for Item 1 of
blueprint `lem:qld-construct-the-paulis`. Polynomial evaluation is replaced by
decoded evaluation only on encoding outcomes; the remaining loss is bounded
by the mass of the non-encoding outcomes.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
* `docs/paper-gaps/qpbt_decoding-identity.tex` records the necessary restriction
  on the decoder identity.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ}

/-- Placing a tensor with an identity on Alice's last register recovers `AA'`. -/
theorem placeSide_alice_tensor_one (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
    (B : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) :
    S.placeSide .alice (_root_.MIPStarRE.QPBT.heteroKron B (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) = S.place .AA' B := by
  ext row col
  simp [_root_.MIPStarRE.QPBT.ProjectiveSetting.placeSide, _root_.MIPStarRE.QPBT.sixRegExtractionEquiv, _root_.MIPStarRE.QPBT.reindexOp, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite]
  split_ifs <;> rfl





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

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Dilation.lean. -/
/-!
# A simultaneous projective dilation of a Magic Square strategy

The rigidity argument for the Magic Square game is stated for an arbitrary
tensor-product strategy, whose measurements are positive operator valued
measures.  The self-testing argument, however, manipulates projections.  This
file removes that discrepancy by dilating an arbitrary strategy to a projective
one without changing any observable quantity.

Each local Hilbert space `ℂ^ι` is enlarged by one auxiliary register whose
basis is indexed by `Option MsAnswer`, and the original space is identified with
the *ground slice* `ℂ^ι ⊗ |⊥⟩`.  The one-measurement Naimark lemma of the low
individual degree development supplies, for every question separately, a family
of projections on the enlarged space whose compression to the ground slice
returns the original effects; the ancilla is the same for all questions, so the
identification of `ℂ^ι` with the ground slice is a single isometry serving every
question at once.  Folding the deficiency `1 - ∑_a P_a` into one distinguished
answer turns the dilated family into a complete projective measurement without
disturbing the compression, because the original effects already sum to the
identity.

Since the dilated state is the image of the original state under the two ground
embeddings, every Born probability, and hence the game value and all the
rejection, malformed-answer, cell-consistency and parity masses of the
value-to-parity layer, is unchanged.  Conversely, the local isometries produced
by a rigidity argument applied to the dilated strategy compose with the ground
embeddings to give local isometries of the original strategy, and the
state-dependent norms occurring in the conclusion of `thm:ms-rigidity` transfer
along that composition.

## References

The rigidity statement supported here is blueprint
`thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, Theorem 6.9.  The dilation reuses the
one-measurement Naimark lemma of
`references/ldt-paper/orthonormalization.tex:121-159`, formalized as
`MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

/-! ## Orthogonality inside a subnormalized family of projections -/







/-! ## The ground slice of an enlarged local space -/



























/-! ## The dilated projective measurement -/

























/-! ## The dilated state -/













/-! ## The dilated Magic Square strategy -/













/-! ## Preservation of the value-to-parity layer -/



































/-! ## Composition of the dilation with later local isometries -/





/-- The matrix of an isometry acts on vectors as the isometry does. -/
theorem isometryMatrix_mulVec {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (x : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ *ᵥ WithLp.ofLp x = WithLp.ofLp (φ x) := by
  have h : Matrix.toEuclideanLin (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ) = φ.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply φ.toLinearMap
  have h' : Matrix.toEuclideanLin (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ) x = φ x := by rw [h]; rfl
  simpa using congrArg WithLp.ofLp h'

/-- The columns of the matrix of an isometry are the images of the basis
vectors. -/
theorem isometryMatrix_apply {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (k : ι') (i : ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ k i =
      φ ((EuclideanSpace.equiv ι ℂ).symm (Pi.single i 1)) k := by
  have h := congrFun (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_mulVec φ
    ((EuclideanSpace.equiv ι ℂ).symm (Pi.single i 1))) k
  rw [← h]
  simp [Matrix.mulVec, dotProduct, EuclideanSpace.equiv, eq_comm]











/-! ## Transfer of state-dependent bounds -/

















end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean. -/
/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ex:easy-but-long`).

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Contractions and their action on states -/











/-- Applying a product of rectangular matrices is successive application. -/
theorem toEuclideanLin_mul_apply {m n o : Type*} [Fintype n] [Fintype o]
    [DecidableEq n] [DecidableEq o]
    (A : Matrix m n ℂ) (B : Matrix n o ℂ) (v : EuclideanSpace ℂ o) :
    Matrix.toEuclideanLin (A * B) v =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]























/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/







/-- The average over the one-point uniform distribution is the sum over the
outcomes. -/
theorem opFamilyDistSq_uniform_unit {γ ι : Type*} [Fintype γ] [Fintype ι]
    [DecidableEq ι] (M N : Unit → γ → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit) M N ψ =
      ∑ c : γ, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M () c - N () c) ψ‖ ^ 2 := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  simp [_root_.LIDT.MIPStarRE.LDT.uniformDistribution, _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_weight]

/-! ## Matrices of isometries -/





















/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Reflections.lean. -/
/-!
# Reflections and the state-dependent metric on operators

The self-testing argument for the Magic Square game manipulates `±1`-valued
observables rather than positive operator valued measures.  This file records
the algebra of such observables and the estimates that convert Born masses into
operator bounds.

Postprocessing a projective measurement along a binary relabelling of its
answers produces a *reflection*, that is, a self-adjoint involution; two
reflections coming from one and the same measurement commute, and their product
is the reflection attached to the sum of the two relabellings.  The reflections
of the source are the binary observables of the rest of the development, so this
file uses `MIPStarRE.QPBT.IsBinaryObservable` and its algebra, defined in
`MIPStarRE/QPBT/Combining/Linearity/Defs.lean`, rather than a second predicate of
its own.  Two operators are compared through the norm of the difference of their
actions on a fixed state, the relation `NormCloseOn` below.  That relation is the
unsquared Euclidean distance between `M ψ` and `N ψ`; it is *not* the
state-dependent distance `≈_δ` of the source, which bounds the squared quantity
`⟨ψ|(M - N)ᴴ (M - N)|ψ⟩` and is formalized in this development by `opDistSq`.
The comparison is symmetric, satisfies the triangle inequality, and is unchanged
by multiplication on the left by an isometric operator; `NormCloseOn.opDistSq_le`
converts it into the source's relation.  Finally, a real spectral combination of
the joint effects of the two players has state-dependent norm controlled by the
Born mass of the answer pairs carrying a nonzero coefficient; this is the step
that turns each rejection mass of the value-to-parity layer into an operator
estimate.

## References

The statements supported here are the operator relations in `thm:ms-rigidity`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Rectangular tensor placement -/

section Kron

/-- Formalization-only: the tensor placement commutes with adjoints. -/
theorem heteroKron_conjTranspose {ιA ιB : Type} (M : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (N : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    (_root_.MIPStarRE.QPBT.heteroKron M N)ᴴ = _root_.MIPStarRE.QPBT.heteroKron Mᴴ Nᴴ := by
  unfold _root_.MIPStarRE.QPBT.heteroKron
  exact Matrix.conjTranspose_kronecker M N







end Kron

/-! ## The state-dependent norm -/



/-! ## Reflections

The *reflections* of `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:228-250`, are the self-adjoint involutions attached to
two-outcome projective measurements, which are exactly the binary observables
`MIPStarRE.QPBT.IsBinaryObservable` of
`MIPStarRE/QPBT/Combining/Linearity/Defs.lean`.  The Magic Square rigidity
argument therefore uses that predicate and its algebra directly:
`IsBinaryObservable.one`, `IsBinaryObservable.mul`,
`IsBinaryObservable.isometry`, `isBinaryObservable_heteroKron_one` and
`isBinaryObservable_one_heteroKron`. -/



/-! ## Closeness in the state-dependent norm -/





/-! ## Sign observables of a projective measurement -/



/-! ## Deviation of joint spectral combinations on the strategy state -/



end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/Soundness/StateTransfer.lean. -/
/-!
# State transfer from supplied extraction data

The extraction witness uses six registers, while the test conclusion groups
each player's first two registers into the auxiliary space. Adjoining the local
EPR states and applying the supplied swap unitaries gives the test isometries.
The squared state error is unchanged by this identification.

## References

Formalization support for blueprint `thm:pauli` and
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
This module transports supplied data without invoking either existence theorem.
The companion `OperatorTransfer` module completes both operator comparisons.
The source-facing obligations are tracked by issues #529 and #586 and
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} {w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG}







open Classical in
/-- The auxiliary-state/EPR vector is unchanged by grouping each player's
first two registers into that player's auxiliary space.
This identity is part of blueprint `thm:pauli-extraction-isometry-construction-support`. -/
theorem ExtractionWitness.idealState_eq (v : _root_.MIPStarRE.QPBT.ExtractionWitness S w delta) :
    _root_.MIPStarRE.QPBT.idealState P v.toPauliSoundnessWitness.aux =
      _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (S.idealExpState v.aux) := by
  ext p
  rfl

open Classical in
/-- The supplied extraction state's squared error is exactly the squared state
error of its test witness. Only the register order changes.
This identity is part of blueprint `thm:pauli-extraction-isometry-construction-support`. -/
theorem ExtractionWitness.state_error_eq (v : _root_.MIPStarRE.QPBT.ExtractionWitness S w delta) :
    ‖_root_.MIPStarRE.QPBT.isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
        S.toStrategy.ψ - _root_.MIPStarRE.QPBT.idealState P v.toPauliSoundnessWitness.aux‖ ^ 2 =
      ‖S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat -
        S.idealExpState v.aux‖ ^ 2 := by
  rw [v.isometryTensor_eq, v.idealState_eq]
  dsimp +instances only [_root_.MIPStarRE.QPBT.ExtractionWitness.toPauliSoundnessWitness, _root_.MIPStarRE.QPBT.ProjectiveSetting.LocalSpace,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.localSpaceFintype, _root_.MIPStarRE.QPBT.ProjectiveSetting.localSpaceDecidableEq]
  have hsub : ∀ x y : EuclideanSpace ℂ (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB),
      _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) x -
        _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) y =
      _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) (x - y) := by
    intros x y
    rfl
  rw [hsub, _root_.MIPStarRE.QPBT.reindexState_norm_eq]





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/PauliTransport.lean. -/
/-!
# Total Pauli measurements under the extraction swaps

The evaluated overlap on the swapped state is the original evaluated-Pauli
consistency overlap. Both player orientations retain their six-register
placements. These identities instantiate the ideal-state Pauli comparison.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1785-1858`,
especially `eq:qld-unitary-6` and `eq:qld-unitary-9`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

noncomputable section



namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)





/-- Original-player placement agrees with extension to the whole local block. -/
theorem placeSide_onPlayer (side : _root_.MIPStarRE.QPBT.PlayerSide) (A : _root_.LIDT.MIPStarRE.Quantum.Op (S.LocalSpace side)) :
    S.placeSide side (S.onPlayer side A) = S.placePlayer side A := by
  cases side
  · exact S.placeSide_alice_tensor_one _
  · exact S.placeSide_bob_tensor_one _



/-- Block placement preserves conjugation. -/
theorem placeSide_conjBy (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (U A : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionBlock P (S.LocalSpace side))) :
    S.placeSide side (_root_.MIPStarRE.QPBT.conjBy U A) = _root_.MIPStarRE.QPBT.conjBy (S.placeSide side U) (S.placeSide side A) := by
  cases side <;>
    simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.placeSide, _root_.MIPStarRE.QPBT.conjBy, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_conjTranspose,
      ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul, _root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_conjTranspose,
      _root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.conjTranspose_one, Matrix.mul_one] <;> rfl

/-- Conjugated total-Pauli effects in block coordinates give exactly the
six-register operators required by the extraction witness. -/
theorem placeSide_swappedPauliMeas (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    S.placeSide side ((S.swappedPauliMeas w side W).effect h) =
      _root_.MIPStarRE.QPBT.conjBy (S.placeSide side (_root_.MIPStarRE.QPBT.swapUnitary w side))
        (S.placePlayer side ((S.pauliMeas side W).effect h)) := by
  exact (S.placeSide_conjBy side _ _).trans
    (congrArg (_root_.MIPStarRE.QPBT.conjBy (S.placeSide side (_root_.MIPStarRE.QPBT.swapUnitary w side))) (S.placeSide_onPlayer side _))











end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/Ancilla.lean. -/
/-!
# Ancilla isometries for Pauli soundness

Adjoining a unit vector and applying a unitary gives the local isometry in the
final soundness argument. The exact intertwining identity below supplies the
algebraic hypothesis of the range-projection estimates. These results are
recorded in blueprint `thm:pauli-ancilla-intertwining-support`.

## References

Formalization support for blueprint `thm:pauli`, specifically the isometry at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
The registers are ordered as `AA'A''`, with the first two factors grouped.
These constructions do not assume or construct a global polynomial measurement.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MagicSquareRigidity

noncomputable section

variable {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]



/-- The columns of the ancilla isometry are the original basis vectors
tensored with the fixed ancilla. -/
theorem ancillaBlockIsometry_matrix_apply
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (p : (ι × κ) × ν) (i : ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix (_root_.MIPStarRE.QPBT.ancillaBlockIsometry (ι := ι) eta heta) p i =
      if p.1.1 = i then eta (p.1.2, p.2) else 0 := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_apply]
  simp [_root_.MIPStarRE.QPBT.ancillaBlockIsometry, _root_.MIPStarRE.QPBT.reindexState, _root_.MIPStarRE.QPBT.vecTensor, eq_comm]

/-- Extending an operator by identities commutes with adjoining a fixed ancilla.
This exact identity is independent of any success or consistency estimate. -/
theorem ancillaBlockIsometry_intertwines
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron M (1 : _root_.LIDT.MIPStarRE.Quantum.Op κ)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ν) *
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix (_root_.MIPStarRE.QPBT.ancillaBlockIsometry (ι := ι) eta heta) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix (_root_.MIPStarRE.QPBT.ancillaBlockIsometry (ι := ι) eta heta) * M := by
  ext p i
  simp [Matrix.mul_apply, _root_.MIPStarRE.QPBT.ancillaBlockIsometry_matrix_apply, _root_.MIPStarRE.QPBT.heteroKron,
    Matrix.kronecker, Matrix.one_apply, Fintype.sum_prod_type, mul_comm]



/-- The matrix of the extraction isometry is the unitary times the ancilla
embedding, with no range projection omitted. -/
theorem unitaryAncillaIsometry_matrix
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (U : _root_.LIDT.MIPStarRE.Quantum.Op ((ι × κ) × ν)) (hU : Uᴴ * U = 1) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix (_root_.MIPStarRE.QPBT.unitaryAncillaIsometry eta heta U hU) =
      U * _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix (_root_.MIPStarRE.QPBT.ancillaBlockIsometry (ι := ι) eta heta) := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro psi
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.toEuclideanLin_mul_apply]
  simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix, Matrix.toEuclideanLin.apply_symm_apply]
  rfl

/-- The unitary conjugate of an extended operator intertwines with the
extraction isometry. This proves the exact hypothesis needed by
`sum_norm_leftTensor_conjIsometry_sub_sq_le` and its Bob-side counterpart
for the local isometries used in the final proof of `thm:pauli`. -/
theorem unitaryAncillaIsometry_intertwines
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (U : _root_.LIDT.MIPStarRE.Quantum.Op ((ι × κ) × ν)) (hU : Uᴴ * U = 1) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (U * _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron M (1 : _root_.LIDT.MIPStarRE.Quantum.Op κ)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ν) * Uᴴ) *
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix (_root_.MIPStarRE.QPBT.unitaryAncillaIsometry eta heta U hU) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix (_root_.MIPStarRE.QPBT.unitaryAncillaIsometry eta heta U hU) * M := by
  rw [_root_.MIPStarRE.QPBT.unitaryAncillaIsometry_matrix]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul,
    _root_.MIPStarRE.QPBT.ancillaBlockIsometry_intertwines]

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/OperatorTransfer.lean. -/
/-!
# Operator transfer from supplied extraction data

The complete swap-conjugated measurements intertwine with the local ancilla
isometries. The range-projection estimates then transfer both Pauli families
to the ideal state, with squared error at most four times the extraction error.

## References

Formalization support for the final argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
This conditional construction uses supplied extraction data in a projective
setting; it does not prove blueprint `thm:pauli`. The omitted range projection
is documented in `docs/paper-gaps/qpbt_extraction-transfer.tex` (issue
Dengnifer/MIPStarRE-QPBT-bak#529).
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

noncomputable section

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} {w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG}



private theorem extracted_bob_eq (W : _root_.MIPStarRE.QPBT.PauliKind) (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    S.placeExtractedRegister .bob (_root_.MIPStarRE.QPBT.pauliProj W h) =
      _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (_root_.MIPStarRE.QPBT.pauliProjOnB'' P (ιA' := S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P)
          (ιB' := S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) W h) := by
  ext i j
  change ((1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA) i.1.1 j.1.1 * _root_.MIPStarRE.QPBT.pauliProj W h i.2.2.2 j.2.2.2) *
    (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) i.1.2.1 j.1.2.1 *
    (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) i.1.2.2 j.1.2.2 *
    (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) i.2.1 j.2.1 *
    (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) i.2.2.1 j.2.2.1 = _
  simp [_root_.MIPStarRE.QPBT.reindexOp, _root_.MIPStarRE.QPBT.sixRegExtractionEquiv, _root_.MIPStarRE.QPBT.pauliProjOnB'',
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> simp_all



private theorem conjugated_bob_eq (_v : _root_.MIPStarRE.QPBT.ExtractionWitness S w delta)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.conjBy (S.placeSide .bob (_root_.MIPStarRE.QPBT.swapUnitary w .bob))
        (S.placePlayer .bob ((S.pauliMeas .bob W).effect h)) =
      _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (_root_.MIPStarRE.QPBT.heteroKron 1 ((S.swappedPauliMeas w .bob W).effect h)) := by
  exact (S.placeSide_swappedPauliMeas w .bob W h).symm





private theorem full_pauli_distance_bob_of_le (v : _root_.MIPStarRE.QPBT.ExtractionWitness S w delta)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (D : ℝ)
    (hclose : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun (_ : Unit) (h : _root_.MIPStarRE.QPBT.PauliRegister P) =>
        _root_.MIPStarRE.QPBT.conjBy (S.placeSide .bob (_root_.MIPStarRE.QPBT.swapUnitary w .bob))
          (S.placePlayer .bob ((S.pauliMeas .bob W).effect h)))
      (fun (_ : Unit) (h : _root_.MIPStarRE.QPBT.PauliRegister P) =>
        S.placeExtractedRegister .bob (_root_.MIPStarRE.QPBT.pauliProj W h))
      (S.idealExpState v.aux) ≤ D) :
    ∑ h : _root_.MIPStarRE.QPBT.PauliRegister P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron 1 ((S.swappedPauliMeas w .bob W).effect h) -
        _root_.MIPStarRE.QPBT.pauliProjOnB'' P W h) (_root_.MIPStarRE.QPBT.idealState P v.toPauliSoundnessWitness.aux)‖ ^ 2 ≤ D := by
  classical
  have hc := hclose
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.opFamilyDistSq_uniform_unit] at hc
  simp_rw [conjugated_bob_eq v, extracted_bob_eq,
    ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_sub,
    ← _root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState] at hc
  rw [v.idealState_eq]
  exact hc





















end

end MIPStarRE.QPBT

/-!
# Operator transfer from supplied extraction data

The complete swap-conjugated measurements intertwine with the local ancilla
isometries. The range-projection estimates then transfer both Pauli families
to the ideal state, with squared error at most four times the extraction error.

## References

Formalization support for the final argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
This conditional construction uses supplied extraction data in a projective
setting; it does not prove blueprint `thm:pauli`. The omitted range projection
is documented in `docs/paper-gaps/qpbt_extraction-transfer.tex` (issue
Dengnifer/MIPStarRE-QPBT-bak#529).
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.MagicSquareRigidity MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement



variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} {w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG}

theorem solution
    (v : _root_.MIPStarRE.QPBT.ExtractionWitness S w delta) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.pauliOperatorDistanceB P S.toStrategy v.toPauliSoundnessWitness W ≤
      2 * _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun (_ : Unit) (h : _root_.MIPStarRE.QPBT.PauliRegister P) =>
          _root_.MIPStarRE.QPBT.conjBy (S.placeSide .bob (_root_.MIPStarRE.QPBT.swapUnitary w .bob))
            (S.placePlayer .bob ((S.pauliMeas .bob W).effect h)))
        (fun (_ : Unit) (h : _root_.MIPStarRE.QPBT.PauliRegister P) =>
          S.placeExtractedRegister .bob (_root_.MIPStarRE.QPBT.pauliProj W h))
        (S.idealExpState v.aux) +
      2 * ‖S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat -
        S.idealExpState v.aux‖ ^ 2 := by
  have h := _root_.MIPStarRE.QPBT.sum_norm_rightTensor_conjIsometry_sub_sq_le
    v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
    (S.pauliMeas .bob W).effect (S.swappedPauliMeas w .bob W)
    (_root_.MIPStarRE.QPBT.pauliProjOnB'' P W)
    (fun h => _root_.MIPStarRE.QPBT.unitaryAncillaIsometry_intertwines (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
      (_root_.MIPStarRE.QPBT.eprState_norm _) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) (v.swap_left_unitary .bob)
      ((S.pauliMeas .bob W).effect h))
    S.toStrategy.ψ (_root_.MIPStarRE.QPBT.idealState P v.toPauliSoundnessWitness.aux)
  have hlift (M : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) :
      _root_.MIPStarRE.QPBT.liftedBEffect S.toStrategy (ιA' := v.toPauliSoundnessWitness.ιA')
          v.toPauliSoundnessWitness.φB M =
        _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (v.toPauliSoundnessWitness.ιA' × _root_.MIPStarRE.QPBT.PauliRegister P))
          (_root_.MIPStarRE.QPBT.conjIsometry v.toPauliSoundnessWitness.φB M) := by
    ext i j
    simp [_root_.MIPStarRE.QPBT.liftedBEffect, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.one_apply]
  have hfull := full_pauli_distance_bob_of_le v W _ (le_refl _)
  have hstate := v.state_error_eq
  rw [norm_sub_rev] at hstate
  have hbound := h.trans (add_le_add
    (mul_le_mul_of_nonneg_left hfull (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left (le_of_eq hstate) (by norm_num : (0 : ℝ) ≤ 2)))
  apply le_of_eq_of_le ?_ hbound
  unfold _root_.MIPStarRE.QPBT.pauliOperatorDistanceB
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun O => ‖_root_.MIPStarRE.QPBT.applyOperatorToState (O - _root_.MIPStarRE.QPBT.pauliProjOnB'' P W a)
    (_root_.MIPStarRE.QPBT.idealState P v.toPauliSoundnessWitness.aux)‖ ^ 2) (hlift _)
