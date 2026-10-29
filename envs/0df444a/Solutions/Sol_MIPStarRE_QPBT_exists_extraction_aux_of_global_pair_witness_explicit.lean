-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_extraction_aux_of_global_pair_witness_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:37:32.100074+00:00
-- url     : https://prove2.me/submissions/b46fa314-732a-4e78-bb07-3eee1f8d5ee3

-- Generated proof for MIPStarRE.QPBT.exists_extraction_aux_of_global_pair_witness_explicit.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_ExplicitConstants
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_EPRState
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_Extraction_norm_sub_eprProjection_le_of_pauli_dist
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_exists_unit_aux_near_eprProjection
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_pauli_dist_reindex_extraction
import Theorems.Thm_MIPStarRE_QPBT_opDistSq_conjBy_apply_eq
import Theorems.Thm_MIPStarRE_QPBT_swapUnitary_conj_tildeObs
import Theorems.Thm_MIPStarRE_QPBT_tilde_obs_self_consistent_of_global_pair_witness_card

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

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Transfer.lean. -/
/-!
# Transfer of rigidity bounds along the projective dilation

The self-testing argument behind `thm:ms-rigidity` is carried out for the
projective dilation `msDilatedStrategy S` of an arbitrary Magic Square strategy
`S`.  Its conclusions are state-dependent bounds for the *dilated* projectors,
conjugated by local isometries `φ_A`, `φ_B` out of the enlarged local spaces.
The witness for the original strategy is obtained by composing these isometries
with the ground embeddings, and the operators appearing in its bounds are the
conjugates of the *original* effects, that is, of the compressions `Π P Π` of
the dilated projectors `P` to the ground slice (`Π` the ground projection).

Naimark dilation preserves Born probabilities but not state-dependent `≈_δ`
estimates in general (`references/ldt-paper/orthonormalization.tex:82-101`,
blueprint `ex:easy-but-long`), so `Π P Π` and `P` need not act
alike on the dilated state.  Their difference on the dilated state `ψ'` is the
*leakage* `(1 - Π) P ψ'` of `P` out of the ground slice, and the point of this
file is that in the Magic Square game this leakage is controlled by the
cell-consistency defect of the value-to-parity layer: the dilated effect
`P ⊗ 1` almost agrees with the partner effect `1 ⊗ Q` on the other side, and
`(1 - Π) ⊗ 1` annihilates `1 ⊗ Q ψ'`.  Combined with the closeness of
`(φ_A ⊗ φ_B) ψ'` to the ideal state and the fact that all operators involved
are contractions, this pulls every bound of `thm:ms-rigidity` back from the
dilated strategy to the original one with explicit constants.

## Main statements

* `ms_effect_transfer_A`, `ms_effect_transfer_B`: the bit-measurement distances
  of the original strategy are bounded by three times those of the dilated
  strategy plus `216 ε + 24 η²`, where `η` bounds the state closeness.
* `ms_anticommutator_transfer_A`, `ms_anticommutator_transfer_B`: the
  anticommutator defects transfer with the bound `3 · (dilated) + 15552 ε +
  48 η²`.
* `ms_state_transfer`: the state closeness is unchanged.

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

/-! ## Cell consistency of the postprocessed effects -/





/-! ## The dilated effects on the enlarged ground spaces -/









/-! ## Compressions of the dilated postprocessed effects -/

















/-! ## Transfer of the effect estimates -/















/-! ## Transfer of the anticommutator estimates -/



/-- The action on states respects differences of operators. -/
theorem applyOperatorToState_sub_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (M - N) v =
      _root_.MIPStarRE.QPBT.applyOperatorToState M v - _root_.MIPStarRE.QPBT.applyOperatorToState N v := by
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]





























end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/PauliBasisTest.lean. -/
/-!
# The Pauli basis test

This file supplies the finite question and answer alphabets, the typed
conditionally-linear question sampler, and the Boolean win predicate for the
Pauli basis test.  The quantitative soundness theorem is isolated in
`Soundness.lean`.

## References

The source-facing nodes are blueprint `def:admissible`,
`def:pauli-question-distribution`, and `def:pauli-win-predicate`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:908-1225`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section



















/- The nested sum is the fixed register order
`V_X ⊕ V_Z ⊕ V_I ⊕ V_V ⊕ V_{R_X} ⊕ V_{R_Z}` from the blueprint. -/


















































set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Deciding the cardinality unfolds the nested finite sum and product alphabets.
/-- The ordered carrier of the Pauli question graph has `86` edges: its
`26` loops occur once, while its `30` non-loop undirected edges occur in both
orientations. This finite computation supports the explicit quantitative
baseline for `thm:pauli`; the graph itself is unchanged. -/
theorem pauli_edge_card : Fintype.card _root_.MIPStarRE.QPBT.PauliEdge = 86 := by
  decide





































end

end MIPStarRE.QPBT

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

/- Source helpers from QPBT/Extraction/ObservableConsistency.lean. -/
/-!
# Self-consistency of the pulled-apart observables

The difference-polynomial measurements reduce observable self-consistency to
point self-consistency and polynomial collision. The global witness remains
an explicit premise.

## References

- Blueprint `lem:qld-construct-the-paulis-given-global-pair`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1476-1662`.
- `docs/paper-gaps/qpbt_extraction-transfer.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#123.
- The joint source obligation for `lem:qld-construct-the-paulis` is stated in
  `Extraction.Construction`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section



/-- The pulled-apart observable consistency bound at the closed extraction
coefficient `2800`. -/
theorem tilde_obs_self_consistent_of_global_pair_witness_explicit
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon deltaG : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon ≤ 1) (hdeltaG : 0 ≤ deltaG)
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (j : Fin P.model.basisDim) :
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
      (fun u => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeObs w .alice W u j))
      (fun u => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeObs w .bob W u j))
      S.psiHat ≤ _root_.MIPStarRE.QPBT.deltaConstructPaulis _root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant
        epsilon deltaG P.m P.d P.q := by
  have h := _root_.MIPStarRE.QPBT.tilde_obs_self_consistent_of_global_pair_witness_card
    P epsilon deltaG hepsilon hepsilon_one hdeltaG S w W j
  norm_num [_root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant, _root_.MIPStarRE.QPBT.pauli_edge_card] at h ⊢
  exact h



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/SwappedConsistency.lean. -/
/-!
# Observable consistency after the concrete swaps

Unitary conjugation transports the supplied-witness observable estimate to
the canonical Pauli operators on the extracted registers. This is the input
to the EPR correlation argument, before projection and normalization.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1701-1724`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum LIDT.MIPStarRE.LDT DistanceCalculus

noncomputable section

private theorem conjBy_reindexOp {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (U A : _root_.LIDT.MIPStarRE.Quantum.Op J) :
    _root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.reindexOp e U) (_root_.MIPStarRE.QPBT.reindexOp e A) = _root_.MIPStarRE.QPBT.reindexOp e (_root_.MIPStarRE.QPBT.conjBy U A) := by
  rw [_root_.MIPStarRE.QPBT.conjBy, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_conjTranspose,
    ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul, ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul, _root_.MIPStarRE.QPBT.conjBy]

private theorem conjBy_heteroKron {I J : Type} [Fintype I] [Fintype J]
    (U A : _root_.LIDT.MIPStarRE.Quantum.Op I) (V B : _root_.LIDT.MIPStarRE.Quantum.Op J) :
    _root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.heteroKron U V) (_root_.MIPStarRE.QPBT.heteroKron A B) =
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjBy U A) (_root_.MIPStarRE.QPBT.conjBy V B) := by
  simp only [_root_.MIPStarRE.QPBT.conjBy, _root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_conjTranspose, _root_.MIPStarRE.QPBT.heteroKron_mul]

/-- Simultaneous swaps conjugate each local operator by its own swap. This
retains the heterogeneous local spaces in the calculation at paper lines 1701-1713. -/
theorem ProjectiveSetting.conjBy_placeBoth_swap_placeSide
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (A : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionBlock P (S.LocalSpace side))) :
    _root_.MIPStarRE.QPBT.conjBy (S.placeBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob)) (S.placeSide side A) =
      S.placeSide side (_root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.swapUnitary w side) A) := by
  classical
  cases side <;> simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.placeBoth, _root_.MIPStarRE.QPBT.ProjectiveSetting.placeSide,
    conjBy_reindexOp, conjBy_heteroKron]
  · congr 2
    change _root_.MIPStarRE.QPBT.swapUnitary w .bob * 1 * (_root_.MIPStarRE.QPBT.swapUnitary w .bob)ᴴ = 1
    rw [Matrix.mul_one, _root_.MIPStarRE.QPBT.swapUnitary_mul_conjTranspose]
  · congr 2
    change _root_.MIPStarRE.QPBT.swapUnitary w .alice * 1 * (_root_.MIPStarRE.QPBT.swapUnitary w .alice)ᴴ = 1
    rw [Matrix.mul_one, _root_.MIPStarRE.QPBT.swapUnitary_mul_conjTranspose]



/-- After the swaps, the pulled-apart distance is exactly the distance of the
canonical Pauli observables on the two extracted blocks. -/
theorem opDistSq_extracted_eq_tildeObs
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind) (j : Fin P.model.basisDim) :
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
      (fun u => S.placeSide .alice (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice))
        (_root_.MIPStarRE.QPBT.tauObservable W (P.model.basis j • u))))
      (fun u => S.placeSide .bob (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob))
        (_root_.MIPStarRE.QPBT.tauObservable W (P.model.basis j • u))))
      (S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat) =
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
      (fun u => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeObs w .alice W u j))
      (fun u => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeObs w .bob W u j)) S.psiHat := by
  have h := _root_.MIPStarRE.QPBT.opDistSq_conjBy_apply_eq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
    _ (S.placeBoth_swap_left_unitary w)
    (fun u => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeObs w .alice W u j))
    (fun u => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeObs w .bob W u j)) S.psiHat
  simp_rw [S.conjBy_placeBoth_swap_placeSide w .alice,
    S.conjBy_placeBoth_swap_placeSide w .bob,
    _root_.MIPStarRE.QPBT.swapUnitary_conj_tildeObs w .alice W,
    _root_.MIPStarRE.QPBT.swapUnitary_conj_tildeObs w .bob W] at h
  simpa only [_root_.MIPStarRE.QPBT.ProjectiveSetting.applyBoth] using h

/-- The supplied global witness bounds the canonical Pauli disagreement on
the swapped state, with a universal constant independent of the parameters.
This is the distance form of paper `eq:qld-unitary-1`.

**Unfaithful:** This uses the supplied-witness theorem
`tildeObs_selfConsistent_ofGlobalPairWitness`, not the construction in
`lem:qld-4-7`. The missing source construction and its planned composition
with `exists_globalPairWitness` are recorded in
`docs/paper-gaps/qpbt_extraction-transfer.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#123. -/
theorem extracted_obs_self_consistent_of_global_pair_witness_explicit
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon deltaG : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon ≤ 1) (hdeltaG : 0 ≤ deltaG)
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (j : Fin P.model.basisDim) :
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliRegister P))
      (fun u => S.placeSide .alice (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice))
        (_root_.MIPStarRE.QPBT.tauObservable W (P.model.basis j • u))))
      (fun u => S.placeSide .bob (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob))
        (_root_.MIPStarRE.QPBT.tauObservable W (P.model.basis j • u))))
      (S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat) ≤
        _root_.MIPStarRE.QPBT.deltaConstructPaulis _root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant
          epsilon deltaG P.m P.d P.q := by
  rw [_root_.MIPStarRE.QPBT.opDistSq_extracted_eq_tildeObs]
  exact _root_.MIPStarRE.QPBT.tilde_obs_self_consistent_of_global_pair_witness_explicit
    P epsilon deltaG hepsilon hepsilon_one hdeltaG S w W j



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
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon deltaG : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon ≤ 1) (hdeltaG : 0 ≤ deltaG)
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) :
    ∃ aux : EuclideanSpace ℂ
        (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB),
      ‖aux‖ = 1 ∧
        ‖S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat -
          S.idealExpState aux‖ ^ 2 ≤
            16 * _root_.MIPStarRE.QPBT.deltaConstructPaulis _root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant
              epsilon deltaG P.m P.d P.q := by
  let theta := S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat
  let e := (_root_.MIPStarRE.QPBT.extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm
  let delta := _root_.MIPStarRE.QPBT.deltaConstructPaulis _root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant
    epsilon deltaG P.m P.d P.q
  have hdelta : 0 ≤ delta := by
    dsimp [delta, _root_.MIPStarRE.QPBT.deltaConstructPaulis, _root_.MIPStarRE.QPBT.pauliBaselineExtractionConstant]
    positivity
  let j : Fin P.model.basisDim := ⟨0, P.model.basisDimOdd.pos⟩
  have hdist := _root_.MIPStarRE.QPBT.Extraction.norm_sub_eprProjection_le_of_pauli_dist
    (_root_.MIPStarRE.QPBT.reindexState e theta) delta hdelta (fun W => by
      exact (S.pauli_dist_reindex_extraction theta W j).trans_le
        (_root_.MIPStarRE.QPBT.extracted_obs_self_consistent_of_global_pair_witness_explicit
          P epsilon deltaG hepsilon hepsilon_one hdeltaG S w W j))
  have htransport :
      ‖_root_.MIPStarRE.QPBT.reindexState e theta - _root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
          (Matrix.vecMulVec (fun x => _root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P) x)
            (fun y => star (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P) y)))) (_root_.MIPStarRE.QPBT.reindexState e theta)‖ =
        ‖theta - _root_.MIPStarRE.QPBT.applyOperatorToState S.extractionEprProjection theta‖ := by
    have h := _root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState e
      (1 - _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
        (Matrix.vecMulVec (fun x => _root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P) x)
          (fun y => star (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P) y)))) theta
    rw [_root_.MIPStarRE.QPBT.WinImplications.reindexOp_sub] at h
    have hone : _root_.MIPStarRE.QPBT.reindexOp e (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA
        S.toStrategy.ιB × (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))) = 1 := by
      ext x y
      simp [_root_.MIPStarRE.QPBT.reindexOp, Matrix.one_apply]
    rw [hone] at h
    simpa only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub_op,
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one,
      _root_.MIPStarRE.QPBT.ProjectiveSetting.extractionEprProjection] using h
  have hprojection := htransport.symm.trans_le hdist
  obtain ⟨aux, haux, hclose⟩ := S.exists_unit_aux_near_eprProjection theta (S.applyBoth_swap_norm w)
  refine ⟨aux, haux, ?_⟩
  have hnorm := norm_nonneg (theta - S.idealExpState aux)
  have hsqrt := Real.sqrt_nonneg delta
  have hsquare := Real.sq_sqrt hdelta
  change ‖theta - S.idealExpState aux‖ ^ 2 ≤ 16 * delta
  nlinarith
