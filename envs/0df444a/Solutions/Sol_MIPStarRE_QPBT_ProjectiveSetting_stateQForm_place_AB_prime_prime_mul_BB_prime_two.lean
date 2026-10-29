-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.stateQForm_place_AB_prime_prime_mul_BB_prime_two
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:24:45.810342+00:00
-- url     : https://prove2.me/submissions/dda394f6-33ef-4595-a749-6e64ecc715d1

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.stateQForm_place_AB''_mul_BB'_two.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_stateQForm_reindexState
import Theorems.Thm_MIPStarRE_QPBT_applyOperatorToState_heteroKron_vecTensor
import Theorems.Thm_MIPStarRE_QPBT_inner_vecTensor

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



/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/





/-- The `BB'` placement in the unshuffled tensor order of `psiHat`. -/
theorem reindexOp_sixRegShuffle_place_BB'_heteroKron
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (T : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB)
    (V : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .BB' (_root_.MIPStarRE.QPBT.heteroKron T V)) =
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA) T)
          (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))
            (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))))
        (_root_.MIPStarRE.QPBT.heteroKron V (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) := by
  ext i j
  obtain ⟨⟨⟨iA, iB⟩, iA', iA''⟩, iB', iB''⟩ := i
  obtain ⟨⟨⟨jA, jB⟩, jA', jA''⟩, jB', jB''⟩ := j
  simp only [_root_.MIPStarRE.QPBT.reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, _root_.MIPStarRE.QPBT.ProjectiveSetting.place, _root_.MIPStarRE.QPBT.sixRegShuffle, Equiv.coe_fn_mk, _root_.MIPStarRE.QPBT.heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply]
  ring

/-- The `AB''` placement in the unshuffled tensor order of `psiHat`. -/
theorem reindexOp_sixRegShuffle_place_AB''_heteroKron
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (T : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
    (V : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .AB'' (_root_.MIPStarRE.QPBT.heteroKron T V)) =
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron T (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB))
          (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))
            (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))))
        (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) V) := by
  ext i j
  obtain ⟨⟨⟨iA, iB⟩, iA', iA''⟩, iB', iB''⟩ := i
  obtain ⟨⟨⟨jA, jB⟩, jA', jA''⟩, jB', jB''⟩ := j
  simp only [_root_.MIPStarRE.QPBT.reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, _root_.MIPStarRE.QPBT.ProjectiveSetting.place, _root_.MIPStarRE.QPBT.sixRegShuffle, Equiv.coe_fn_mk, _root_.MIPStarRE.QPBT.heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply]
  ring



















end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/LinePointOverlap.lean. -/
/-!
# Overlap of expanded line and expanded point measurements

This module computes the diagonal overlap, on the expanded state, between an
expanded line measurement on one placement and the expanded point effects
selected by evaluation at the sampled point on the opposite placement. Each
product of convolution terms factorizes into a strategy overlap and an EPR
overlap; the EPR overlap of a Pauli line projector with a Pauli point projector
vanishes unless the line polynomial evaluates to the point value, and then
equals the EPR overlap of the line projector alone. Summing over the
convolution fibers identifies the expanded overlap with the overlap of the
strategy's evaluation classes and its completed point measurement. This is the
computation displayed in items 2 and 3 of the expanded-line consistency lemma.

The sections on the linearity of the state quadratic form, on register
placements, and on the completed point measurements collect formalization-only
auxiliaries: the source uses these facts without stating them.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Linearity of the state quadratic form -/



namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





















/-! ## Effects of the completed measurement families -/















/-! ## Factorization of opposite placements with distinct Pauli factors -/



set_option synthInstance.maxSize 400 in
/-- The product of opposite `AB''` and `BB'` placements with distinct Pauli
factors separates into the strategy product, the identity on the first EPR
pair, and the second EPR-pair product. -/
theorem reindexOp_sixRegShuffle_place_AB''_mul_BB'_two
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (A : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
    (B : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) (T T' : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .AB'' (_root_.MIPStarRE.QPBT.heteroKron A T) * S.place .BB' (_root_.MIPStarRE.QPBT.heteroKron B T')) =
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron A B)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)))
        (_root_.MIPStarRE.QPBT.heteroKron T' T) := by
  rw [_root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_sixRegShuffle_place_AB''_heteroKron,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_sixRegShuffle_place_BB'_heteroKron]
  simp only [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one, Matrix.one_mul,
    _root_.MIPStarRE.QPBT.heteroKron_one_one]









end ProjectiveSetting

/-! ## The overlap identity -/







end

end MIPStarRE.QPBT

/-!
# Overlap of expanded line and expanded point measurements

This module computes the diagonal overlap, on the expanded state, between an
expanded line measurement on one placement and the expanded point effects
selected by evaluation at the sampled point on the opposite placement. Each
product of convolution terms factorizes into a strategy overlap and an EPR
overlap; the EPR overlap of a Pauli line projector with a Pauli point projector
vanishes unless the line polynomial evaluates to the point value, and then
equals the EPR overlap of the line projector alone. Summing over the
convolution fibers identifies the expanded overlap with the overlap of the
strategy's evaluation classes and its completed point measurement. This is the
computation displayed in items 2 and 3 of the expanded-line consistency lemma.

The sections on the linearity of the state quadratic form, on register
placements, and on the completed point measurements collect formalization-only
auxiliaries: the source uses these facts without stating them.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



/-! ## Linearity of the state quadratic form -/

open MIPStarRE.QPBT.DistanceCalculus





open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





















/-! ## Effects of the completed measurement families -/















/-! ## Factorization of opposite placements with distinct Pauli factors -/

set_option synthInstance.maxSize 400 in

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (A : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB)
    (T T' : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hT : T.IsHermitian) (hT' : T'.IsHermitian) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place .AB'' (_root_.MIPStarRE.QPBT.heteroKron A T) * S.place .BB' (_root_.MIPStarRE.QPBT.heteroKron B T')) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ (_root_.MIPStarRE.QPBT.heteroKron A B) *
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
          (_root_.MIPStarRE.QPBT.heteroKron T' T) := by
  have hAB : (_root_.MIPStarRE.QPBT.heteroKron A B).IsHermitian :=
    _root_.MIPStarRE.QPBT.heteroKron_isHermitian A B hA hB
  have hpassive :
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron A B)
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))).IsHermitian :=
    _root_.MIPStarRE.QPBT.heteroKron_isHermitian _ _ hAB Matrix.isHermitian_one
  have hTT : (_root_.MIPStarRE.QPBT.heteroKron T' T).IsHermitian :=
    _root_.MIPStarRE.QPBT.heteroKron_isHermitian T' T hT' hT
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_eq_reindexState, _root_.MIPStarRE.QPBT.WinImplications.stateQForm_reindexState,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_sixRegShuffle_place_AB''_mul_BB'_two,
    _root_.MIPStarRE.QPBT.stateQForm_vecTensor_heteroKron _ _ _ _ hpassive hTT,
    _root_.MIPStarRE.QPBT.stateQForm_vecTensor_heteroKron _ _ _ _ hAB Matrix.isHermitian_one,
    _root_.MIPStarRE.QPBT.stateQForm_one_eq_norm_sq, _root_.MIPStarRE.QPBT.eprState_norm]
  ring
