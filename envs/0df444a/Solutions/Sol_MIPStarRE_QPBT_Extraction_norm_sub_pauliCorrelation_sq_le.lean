-- Prove2me | solution 1 for MIPStarRE.QPBT.Extraction.norm_sub_pauliCorrelation_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:36:27.800474+00:00
-- url     : https://prove2.me/submissions/6fa4e9da-2462-417b-988d-d3034fa8cd6c

-- Generated proof for MIPStarRE.QPBT.Extraction.norm_sub_pauliCorrelation_sq_le.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Algebra_PauliTheorems
import Definitions.Def_QPBT_QPBT_Extraction_EPRProjection
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_ExpandedCommutation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_LDT_averageOperatorOverDistribution_const_of_isProbability
import Theorems.Thm_MIPStarRE_QPBT_avg_closeness

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
namespace MIPStarRE.QPBT.Extraction
end MIPStarRE.QPBT.Extraction
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
end MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/Points/Commutation.lean. -/
/-!
# Approximate commutation of the field-valued expanded point measurements

The approximate commutation of `lem:qld-comm-cons` is stated for the binary
refinements `M^{(Point,W),u,r}_b` of the expanded point measurements.  The
combined point measurements of `lem:qld-4-10` are built here directly from the
`F_q`-valued measurements `M^{(Point,W),u}_a`, so the commutation estimate is
transferred to them.  The transfer is exact: since
`M^{(Point,X),x}_a = E_r (-1)^{tr(ar)} X^r(x)` and
`M^{(Point,Z),z}_b = E_s (-1)^{tr(bs)} Z^s(z)`, the commutator of the two
measurement effects is the Fourier transform, in the outcome pair `(a, b)`,
of the commutators of the expanded observables, and Parseval's identity for
the additive characters of `F_q` turns the sum over `(a, b)` of the squared
norms into the average over `(r, s)` of the squared norms of the observable
commutators.  No factor depending on `q` is lost.

## Main results

* `sum_norm_sum_smul_sq_of_orthogonal`: Parseval's identity for an orthogonal
  system of coefficients.
* `sum_fixedCharacter_mul`: Fourier cancellation for the fixed trace character.
* `expPoint_comm`: the field-valued expanded point measurements approximately
  commute on every register placement, with the error of
  `lem:qld-comm-cons`.

## References

The commutation estimate for the binary refinements is item 2 of
`lem:qld-comm-cons`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1210`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`; the
Fourier form of the point effects is `def:expanded-point-measurement`, paper
lines 384--418.  The role of the transfer in the proof of `lem:qld-4-10` is
explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section



/-! ## Parseval's identity for an orthogonal system of coefficients -/



/-! ## The fixed trace character -/



/-! ## Fourier form of the point effects and of their commutator -/

/-- A uniform operator average is the normalized sum. -/
theorem averageOperatorOverDistribution_uniform_eq_inv_card_smul_sum
    {α ι : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype ι] [DecidableEq ι] (f : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f =
      (Fintype.card α : ℂ)⁻¹ • ∑ a, f a := by
  ext i j
  simp only [_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution, _root_.LIDT.MIPStarRE.LDT.uniformDistribution,
    _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset, Finset.mem_univ, if_true, Matrix.sum_apply,
    Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
    Finset.card_univ, one_div, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [Finset.mul_sum]



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/ExpandedCommutation.lean. -/
/-!
# Approximate commutation of the expanded point projections

The trace-coarse-grained expanded point projections approximately commute on
each of the four register placements.  The commutator of the two projections is
a scalar multiple of a factorized operator whose strategy factor is the twisted
commutator of the two point observables and whose Pauli factor is a product of
generalized Pauli observables; the latter is an isometry, so the placement
bookkeeping of `ExpandedPlacement` reduces the estimate to the twisted
commutation relation of `lem:qld-win-implications-obs` on the corresponding
player side.  Both player sides are treated explicitly.

## References

The declarations prove item 2 of `lem:qld-comm-cons` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Algebraic preliminaries -/



/-- The generalized Pauli observables are reflections. Blueprint
`ch11_qpbt_algebra.tex:596-644`, paper
`references/qpbt-paper/04_preliminaries.tex:1088-1089`. -/
theorem tauObservable_conjTranspose_mul_self {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι]
    [DecidableEq ι] (W : _root_.MIPStarRE.QPBT.PauliKind) (v : ι → K) :
    (_root_.MIPStarRE.QPBT.tauObservable W v)ᴴ * _root_.MIPStarRE.QPBT.tauObservable W v = 1 := by
  rw [_root_.MIPStarRE.QPBT.tauObservable_conjTranspose, _root_.MIPStarRE.QPBT.tauObservable_sq]



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

/-!
# EPR projection from Pauli disagreement

Averaging the paired Pauli operators contracts the disagreement norm. The X
and Z averages multiply to the EPR projection, giving the corrected projection
estimate directly in the squared-distance formulation.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1715-1783`;
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT.Extraction

open LIDT.MIPStarRE.Quantum LIDT.MIPStarRE.LDT MIPStarRE.QPBT.DistanceCalculus



variable {K I R : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K] [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

theorem solution
    (W : _root_.MIPStarRE.QPBT.PauliKind) (psi : EuclideanSpace ℂ (R × ((I → K) × (I → K)))) :
    ‖psi - _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.Extraction.pauliCorrelation W)) psi‖ ^ 2 ≤
      _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (I → K))
        (fun u => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauObservable W u) 1))
        (fun u => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.tauObservable W u))) psi := by
  classical
  let L (u : I → K) :=
    _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauObservable W u) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (I → K)))
  let B (u : I → K) :=
    _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (I → K)) (_root_.MIPStarRE.QPBT.tauObservable W u))
  let C (u : I → K) :=
    _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauObservable W u) (_root_.MIPStarRE.QPBT.tauObservable W u))
  have hL (u : I → K) : (L u)ᴴ * L u = 1 := by
    simp only [L, _root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_conjTranspose, Matrix.conjTranspose_one,
      _root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.one_mul, _root_.MIPStarRE.QPBT.tauObservable_conjTranspose_mul_self,
      _root_.MIPStarRE.QPBT.heteroKron_one_one]
  have halg (u : I → K) : L u * (L u - B u) = 1 - C u := by
    simp only [L, B, C, Matrix.mul_sub, _root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.one_mul,
      Matrix.mul_one, _root_.MIPStarRE.QPBT.tauObservable_sq, _root_.MIPStarRE.QPBT.heteroKron_one_one]
  have hdist : _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (I → K)) (fun _ => 1) C psi =
      _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (I → K)) L B psi := by
    unfold _root_.MIPStarRE.QPBT.opDistSq _root_.MIPStarRE.QPBT.opFamilyDistSq
    simp only [Fintype.sum_unique]
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro u
    rw [← halg, _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_isometry_mul (hL u)]
  have havg : _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (I → K))
      (fun u => (1 : ℂ) • ((1 : _root_.LIDT.MIPStarRE.Quantum.Op (R × ((I → K) × (I → K)))) - C u)) =
      1 - _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.Extraction.pauliCorrelation W) := by
    simp only [one_smul]
    have hsub : _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (I → K))
        (fun u => (1 : _root_.LIDT.MIPStarRE.Quantum.Op (R × ((I → K) × (I → K)))) - C u) =
        _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (I → K)) (fun _ => 1) -
          _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (I → K)) C := by
      simp [_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution, smul_sub, Finset.sum_sub_distrib]
    rw [hsub, _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution_const_of_isProbability _
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _)]
    congr 1
    rw [_root_.MIPStarRE.QPBT.averageOperatorOverDistribution_uniform_eq_inv_card_smul_sum]
    change _ = (Matrix.kroneckerBilinear (R := ℂ) (α := ℂ) (1 : _root_.LIDT.MIPStarRE.Quantum.Op R)) _
    simp only [_root_.MIPStarRE.QPBT.Extraction.pauliCorrelation, map_smul, map_sum, C]
    rfl
  have h := _root_.MIPStarRE.QPBT.avg_closeness (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (I → K))
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) (fun _ => 1) C (fun _ => 1)
    (fun _ => by simp) psi
  rw [havg, hdist] at h
  simpa only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub_op,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one] using h
