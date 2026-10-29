-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.extraction_pauli_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:23:38.961126+00:00
-- url     : https://prove2.me/submissions/25737ace-85ab-42b8-9f3f-f58b45daf02f

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.extraction_pauli_dist_le.
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
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_ConcretePauliComparison
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_EncodingSupport
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Extraction_PauliTransport
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_placeSide_extracted
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_swapped_pauli_overlap_alice
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_swapped_pauli_overlap_bob
import Theorems.Thm_MIPStarRE_QPBT_pauli_distance_on_ideal_le
import Theorems.Thm_MIPStarRE_QPBT_pauli_distance_on_ideal_right_le

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
namespace MIPStarRE.QPBT.GlobalPairWitness
end MIPStarRE.QPBT.GlobalPairWitness
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
end MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
namespace MIPStarRE.QPBT.PauliKind
end MIPStarRE.QPBT.PauliKind
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

/- Source helpers from QPBT/Extraction/Observables.lean. -/
/-!
# Pulled-apart Pauli observables

This module constructs the measurements and observables used to pull the two
Pauli bases onto separate registers. The construction retains the distinct
local spaces of the two players and uses the binary basis fixed in the
canonical field model.

## References

The product form and observable relations formalize blueprint
`lem:tildew-product-form`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1415-1456`.
The swap identities formalize blueprint `lem:v-swap-conjugation`, from paper
lines 1687-1713.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.LDT.Preliminaries LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Pulled-apart measurements and observables -/

























/-! ## Swap conjugation -/















/-- The swap map is a left unitary. This is the reverse exact unitarity
calculation implicit in blueprint
`lem:v-swap-conjugation`, paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1699`.

For finite square matrices, the right inverse identity also gives the left
inverse identity. -/
theorem conjTranspose_mul_swapUnitary {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {epsilon delta : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S delta) (side : _root_.MIPStarRE.QPBT.PlayerSide) :
    (_root_.MIPStarRE.QPBT.swapUnitary w side)ᴴ * _root_.MIPStarRE.QPBT.swapUnitary w side = 1 := by
  exact mul_eq_one_comm.mp (_root_.MIPStarRE.QPBT.swapUnitary_mul_conjTranspose w side)







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

/- Source helpers from QPBT/Extraction/Bounds.lean. -/
/-!
# Uniform bounds for the extraction witness

The concrete swap preserves the norm of the expanded state. Completeness of
the two measurement families bounds their summed squared distance by four.
These bounds justify the large-error case of extraction.

## References

* Blueprint `lem:qld-unitary`, including its normalization case distinction.
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1860`.
* `docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
variable (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)

/-- The simultaneous swap is an isometry on the six-register space. This is
the two-player consequence of the unitarity calculation at paper lines 1693-1700. -/
theorem placeBoth_swap_left_unitary (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) :
    (S.placeBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob))ᴴ *
      S.placeBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) = 1 := by
  classical
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.placeBoth, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_conjTranspose, ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_conjTranspose, _root_.MIPStarRE.QPBT.heteroKron_mul]
  erw [_root_.MIPStarRE.QPBT.conjTranspose_mul_swapUnitary, _root_.MIPStarRE.QPBT.conjTranspose_mul_swapUnitary]
  erw [_root_.MIPStarRE.QPBT.heteroKron_one_one]
  ext x y
  simp [_root_.MIPStarRE.QPBT.reindexOp, Matrix.one_apply]

/-- Applying the two concrete swap unitaries preserves normalization. -/
theorem applyBoth_swap_norm (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) :
    ‖S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat‖ = 1 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.applyBoth, _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_of_isometry
    (S.placeBoth_swap_left_unitary w), S.psiHat_norm]













end ProjectiveSetting

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

/- Source helpers from QPBT/Extraction/ConcretePauliComparison.lean. -/
/-!
# Pauli comparison for the concrete extraction maps

The ideal-state distance estimate is transported back to the six-register
operators occurring in the extraction witness, for both players.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

noncomputable section

/-- Coordinate transport preserves the distance between two state vectors. -/
theorem norm_reindexState_sub_eq {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (psi phi : EuclideanSpace ℂ I) :
    ‖_root_.MIPStarRE.QPBT.reindexState e psi - _root_.MIPStarRE.QPBT.reindexState e phi‖ = ‖psi - phi‖ := by
  change ‖_root_.MIPStarRE.QPBT.reindexState e (psi - phi)‖ = _
  exact _root_.MIPStarRE.QPBT.reindexState_norm_eq e _



namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)



/-- The ideal state in local extraction-block order. -/
theorem reindexState_idealExpState_blocks
    (aux : EuclideanSpace ℂ (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)) :
    _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
      (S.idealExpState aux) = _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor aux
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))) := by
  rfl

/-- Subtraction of block operators agrees with subtraction after placement. -/
theorem placeSide_sub (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (A B : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionBlock P (S.LocalSpace side))) :
    S.placeSide side (A - B) = S.placeSide side A - S.placeSide side B := by
  cases side
  · ext row col
    exact sub_mul _ _ _
  · ext row col
    exact mul_sub _ _ _

/-- The entire answer-summed distance in block coordinates is the distance
appearing in `ExtractionWitness.pauli_close`, for either player. -/
theorem extraction_pauli_dist_eq_sum (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (aux : EuclideanSpace ℂ (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun (_ : Unit) (h : _root_.MIPStarRE.QPBT.PauliRegister P) =>
        _root_.MIPStarRE.QPBT.conjBy (S.placeSide side (_root_.MIPStarRE.QPBT.swapUnitary w side))
          (S.placePlayer side ((S.pauliMeas side W).effect h)))
      (fun (_ : Unit) (h : _root_.MIPStarRE.QPBT.PauliRegister P) =>
        S.placeExtractedRegister side (_root_.MIPStarRE.QPBT.pauliProj W h)) (S.idealExpState aux) =
      ∑ h : _root_.MIPStarRE.QPBT.PauliRegister P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (S.placeSide side (((S.swappedPauliMeas w side W).effect h) -
          _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace side)) (_root_.MIPStarRE.QPBT.pauliProj W h)))
        (S.idealExpState aux)‖ ^ 2 := by
  simp_rw [S.placeSide_sub, S.placeSide_swappedPauliMeas, S.placeSide_extracted]
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const _



end ProjectiveSetting

end

end MIPStarRE.QPBT

/-!
# Pauli comparison for the concrete extraction maps

The ideal-state distance estimate is transported back to the six-register
operators occurring in the extraction witness, for both players.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement







open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)

set_option maxHeartbeats 800000 in

theorem solution (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (aux : EuclideanSpace ℂ (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
    (haux : ‖aux‖ = 1) (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun (_ : Unit) (h : _root_.MIPStarRE.QPBT.PauliRegister P) =>
        _root_.MIPStarRE.QPBT.conjBy (S.placeSide side (_root_.MIPStarRE.QPBT.swapUnitary w side))
          (S.placePlayer side ((S.pauliMeas side W).effect h)))
      (fun (_ : Unit) (h : _root_.MIPStarRE.QPBT.PauliRegister P) =>
        S.placeExtractedRegister side (_root_.MIPStarRE.QPBT.pauliProj W h)) (S.idealExpState aux) ≤
      2 * S.evaluatedPauliDefect w side W + 2 * ((P.m * P.d : ℝ) / P.q) +
        4 * ‖S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat -
          S.idealExpState aux‖ := by
  let e := _root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  let theta := S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat
  have htheta : ‖_root_.MIPStarRE.QPBT.reindexState e theta‖ = 1 := by
    rw [_root_.MIPStarRE.QPBT.reindexState_norm_eq]
    exact S.applyBoth_swap_norm w
  rw [S.extraction_pauli_dist_eq_sum]
  cases side
  · have h := _root_.MIPStarRE.QPBT.pauli_distance_on_ideal_le (S.swappedPauliMeas w .alice W) W aux haux
      (_root_.MIPStarRE.QPBT.reindexState e theta) htheta
    dsimp only at h
    erw [S.swapped_pauli_overlap_alice w W, sub_sub_cancel,
      ← S.reindexState_idealExpState_blocks aux, _root_.MIPStarRE.QPBT.norm_reindexState_sub_eq] at h
    convert h using 1
    · apply Finset.sum_congr rfl
      intro label _
      congr 1
      exact (_root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState e _ _).symm
    · rfl
  · have h := _root_.MIPStarRE.QPBT.pauli_distance_on_ideal_right_le (S.swappedPauliMeas w .bob W) W aux haux
      (_root_.MIPStarRE.QPBT.reindexState e theta) htheta
    dsimp only at h
    erw [S.swapped_pauli_overlap_bob w W, sub_sub_cancel,
      ← S.reindexState_idealExpState_blocks aux, _root_.MIPStarRE.QPBT.norm_reindexState_sub_eq] at h
    convert h using 1
    · apply Finset.sum_congr rfl
      intro label _
      congr 1
      exact (_root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState e _ _).symm
    · rfl
