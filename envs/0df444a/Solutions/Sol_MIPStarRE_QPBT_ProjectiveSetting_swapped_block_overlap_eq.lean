-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.swapped_block_overlap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:24:45.953871+00:00
-- url     : https://prove2.me/submissions/f20e3fba-6e72-4c64-939f-09dc689a0a44

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.swapped_block_overlap_eq.
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
import Definitions.Def_QPBT_QPBT_Extraction_BlockMeasurement
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_consistencyDefect_eq_one_sub_overlap
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_stateQForm_reindexState

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
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







































/-- The quadratic form of `Wᴴ M W` in `ψ` is the quadratic form of `M` in
`W ψ`.  This is the conjugation identity behind the placed-sandwich
rewritings: conjugating transfers the outer operator to the state vector.
It is formalization-only auxiliary content, shared by the overlap-gap estimate
and the sandwich self-consistency argument. -/
theorem stateQForm_conjTranspose_mul_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (W M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Wᴴ * M * W) = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState W ψ) M := by
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  congr 1
  change inner ℂ ψ (Matrix.toEuclideanLin Wᴴ _) =
    inner ℂ (Matrix.toEuclideanLin W ψ) _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]



















































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

/-- Simultaneous unitary conjugation preserves the quadratic form of a product. -/
theorem stateQForm_conjBy_mul_apply {I : Type*} [Fintype I] [DecidableEq I]
    (U A B : _root_.LIDT.MIPStarRE.Quantum.Op I) (hU : Uᴴ * U = 1) (psi : EuclideanSpace ℂ I) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState U psi) (_root_.MIPStarRE.QPBT.conjBy U A * _root_.MIPStarRE.QPBT.conjBy U B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi (A * B) := by
  rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_conjTranspose_mul_mul]
  congr 1
  simp only [_root_.MIPStarRE.QPBT.conjBy]
  calc
    _ = (Uᴴ * U) * A * (Uᴴ * U) * B * (Uᴴ * U) := by noncomm_ring
    _ = A * B := by rw [hU]; simp

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)















/-- Multiplying the two block placements is their tensor product in block coordinates. -/
theorem reindexOp_heteroKron_eq_placeSides
    (A : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionBlock P S.toStrategy.ιA))
    (B : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionBlock P S.toStrategy.ιB)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
      (_root_.MIPStarRE.QPBT.heteroKron A B) = S.placeSide .alice A * S.placeSide .bob B := by
  simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.placeSide, ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul, _root_.MIPStarRE.QPBT.heteroKron_mul,
    Matrix.mul_one, Matrix.one_mul]







end ProjectiveSetting

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









end

end MIPStarRE.QPBT

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



open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement





open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)

theorem solution (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    {X α : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (mu : _root_.LIDT.MIPStarRE.LDT.Distribution X) (hmu : mu.IsProbability)
    (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α (_root_.MIPStarRE.QPBT.ExtractionBlock P S.toStrategy.ιA))
    (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α (_root_.MIPStarRE.QPBT.ExtractionBlock P S.toStrategy.ιB)) :
    _root_.LIDT.MIPStarRE.LDT.avgOver mu (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
      (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat))
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.swapUnitary w .alice) ((A x).effect a))
        (_root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.swapUnitary w .bob) ((B x).effect a)))) =
      1 - _root_.MIPStarRE.QPBT.consistencyDefect mu
        (fun x a => S.placeSide .alice ((A x).effect a))
        (fun x a => S.placeSide .bob ((B x).effect a)) S.psiHat := by
  have h := _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap mu
    (fun x => S.blockMeasurement .alice (A x))
    (fun x => S.blockMeasurement .bob (B x)) S.psiHat hmu S.psiHat_norm
  simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.blockMeasurement_effect] at h
  rw [h, sub_sub_cancel]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  rw [_root_.MIPStarRE.QPBT.WinImplications.stateQForm_reindexState, S.reindexOp_heteroKron_eq_placeSides]
  erw [← S.conjBy_placeBoth_swap_placeSide w .alice,
    ← S.conjBy_placeBoth_swap_placeSide w .bob]
  exact _root_.MIPStarRE.QPBT.stateQForm_conjBy_mul_apply _ _ _ (S.placeBoth_swap_left_unitary w) S.psiHat
