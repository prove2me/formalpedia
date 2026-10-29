-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.overlap_BB_prime_AB_prime_prime_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:28:55.862688+00:00
-- url     : https://prove2.me/submissions/b44535fd-a21b-45dc-8e66-5e9a3411f3d8

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.overlap_BB'_AB''_eq.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_LinePointOverlap
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Projector
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_stateQForm_place_AB_prime_prime_mul_BB_prime_two
import Theorems.Thm_MIPStarRE_QPBT_overlap_identity_of_mem
import Theorems.Thm_MIPStarRE_QPBT_overlap_identity_of_not_mem
import Theorems.Thm_MIPStarRE_QPBT_stateQForm_eprState_tauLineProj_tauPointProj

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
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
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



























/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]































































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



































/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/



/-- Tensor placement distributes over a finite sum in the right factor. -/
theorem heteroKron_finset_sum_right {β ιA ιB : Type*} (s : Finset β)
    (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (C : β → _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron A (∑ b ∈ s, C b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.heteroKron A (C b) :=
  _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right s A C





/-! ## Matrices of isometries -/





















/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

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

namespace DistanceCalculus

/-- The state quadratic form of the zero operator vanishes. -/
theorem stateQForm_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι) = 0 := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]

end DistanceCalculus

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}



/-- A register placement of the zero operator is zero. -/
theorem place_zero (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement) :
    S.place p (0 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)) = 0 := by
  ext i j
  cases p <;> simp [_root_.MIPStarRE.QPBT.ProjectiveSetting.place]





/-- The `AB''` placement respects finite sums. -/
theorem place_AB''_finset_sum (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) {γ : Type*}
    (s : Finset γ) (O : γ → _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) :
    S.place .AB'' (∑ g ∈ s, O g : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) =
      ∑ g ∈ s, S.place .AB'' (O g) :=
  _root_.MIPStarRE.QPBT.ProjectiveSetting.place_finset_sum S .AB'' s O

/-- The `BB'` placement respects finite sums. -/
theorem place_BB'_finset_sum (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) {γ : Type*}
    (s : Finset γ) (O : γ → _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) :
    S.place .BB' (∑ g ∈ s, O g : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) =
      ∑ g ∈ s, S.place .BB' (O g) :=
  _root_.MIPStarRE.QPBT.ProjectiveSetting.place_finset_sum S .BB' s O





/-- The `AB''` placement of zero is zero. -/
theorem place_AB''_zero (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    S.place .AB'' (0 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) = 0 :=
  _root_.MIPStarRE.QPBT.ProjectiveSetting.place_zero S .AB''



/-! ## Effects of the completed measurement families -/











/-- The expanded point effect selected by a line answer, written through the
convolution form of the expanded point measurement. -/
theorem expPointEffectAtLineAnswer_eq_elim (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) :
    S.expPointEffectAtLineAnswer side W line u f =
      (_root_.MIPStarRE.QPBT.evalOpt line u f).elim 0 (fun a =>
        ∑ q ∈ Finset.univ.filter
          (fun q : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P => q.1 + q.2 = a),
          _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas side W u).effect q.1)
            (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u q.2)) := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointEffectAtLineAnswer
  cases _root_.MIPStarRE.QPBT.evalOpt line u f with
  | none => rfl
  | some a => exact S.expPointOp_eq_convolution side W u a



/-! ## Factorization of opposite placements with distinct Pauli factors -/











set_option synthInstance.maxSize 400 in
/-- Operators placed on `AB''` and on `BB'` commute. -/
theorem place_AB''_mul_place_BB'_comm (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (X : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice))
    (Y : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) :
    S.place .AB'' X * S.place .BB' Y = S.place .BB' Y * S.place .AB'' X := by
  have key : ∀ (X' : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
      (Y' : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P)),
      S.place .AB'' X' * S.place .BB' Y' = S.place .BB' Y' * S.place .AB'' X' := by
    intro X' Y'
    rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_abBbBipartition_left S X', ← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_abBbBipartition_right S Y',
      ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul, ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul]
    congr 1
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]
  exact key X Y

end ProjectiveSetting

/-! ## The overlap identity -/





namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The four placement pairs -/

/-- A strategy line effect is Hermitian, being positive semidefinite. -/
private theorem lineMeas_effect_isHermitian (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) :
    ((S.lineMeas side W line).effect f).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp ((S.lineMeas side W line).pos f)).isHermitian

/-- A strategy point effect is Hermitian, being positive semidefinite. -/
private theorem pointMeas_effect_isHermitian (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    ((S.pointMeas side W u).effect b).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp ((S.pointMeas side W u).pos b)).isHermitian

/-- A Pauli line projector is Hermitian, being positive semidefinite. -/
private theorem tauLineProj_isHermitian (W : _root_.MIPStarRE.QPBT.PauliKind)
    (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) :
    (_root_.MIPStarRE.QPBT.tauLineProj P W line f).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (_root_.MIPStarRE.QPBT.tauLineProj_nonneg P W line f)).isHermitian

/-- A Pauli point projector is Hermitian, being positive semidefinite. -/
private theorem tauPointProj_isHermitian (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp ((_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointMeas W u).pos b)).isHermitian









end ProjectiveSetting

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















/-! ## The overlap identity -/





open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The four placement pairs -/

set_option synthInstance.maxSize 400 in

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    ∑ f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          (S.place .BB' (S.expLineOp .bob W line f) *
            S.place .AB'' (S.expPointEffectAtLineAnswer .alice W line u f)) =
      ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ
          (_root_.MIPStarRE.QPBT.heteroKron ((S.pointMeasOption .alice W u).effect o)
            ((S.lineEvalMeas .bob W line u).effect o)) := by
  let Φ : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob) →
      _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice) → ℝ := fun X Y =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat (S.place .BB' X * S.place .AB'' Y)
  let Ψ : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB → _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA → ℝ := fun L Q =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ (_root_.MIPStarRE.QPBT.heteroKron Q L)
  have hΦ0 : ∀ X, Φ X 0 = 0 := by
    intro X
    simp only [Φ]
    rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_AB''_zero, mul_zero, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_zero]
  have hΦl : ∀ (s : Finset (_root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) ×
        _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)))
      (X : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) × _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) →
        _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob))
      (Y : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y := by
    intro s X Y
    simp only [Φ]
    rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_BB'_finset_sum, Finset.sum_mul,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  have hΦr : ∀ (X : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob))
      (t : Finset (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P))
      (Y : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P → _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j) := by
    intro X t Y
    simp only [Φ]
    rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_AB''_finset_sum, Finset.mul_sum,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  have hΨl : ∀ (s : Finset (_root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)))
      (A : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) → _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB)
      (B : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA), Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B := by
    intro s A B
    simp only [Ψ]
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_finset_sum_right,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  have hΨ0 : ∀ A, Ψ A 0 = 0 := by
    intro A
    simp only [Ψ]
    rw [_root_.MIPStarRE.QPBT.heteroKron_zero_left, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_zero]
  change ∑ f, Φ (S.expLineOp .bob W line f)
      (S.expPointEffectAtLineAnswer .alice W line u f) =
    ∑ o, Ψ (((S.lineMeas .bob W line).postprocess (_root_.MIPStarRE.QPBT.evalOpt line u)).effect o)
      (((S.pointMeas .alice W u).postprocess some).effect o)
  simp_rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.expPointEffectAtLineAnswer_eq_elim]
  by_cases hu : u ∈ line.pointSet
  · have hΦfact : ∀ (f' f'' : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d))
        (b' b'' : _root_.MIPStarRE.QPBT.PauliScalar P),
        Φ (_root_.MIPStarRE.QPBT.heteroKron ((S.lineMeas .bob W line).effect f')
            (_root_.MIPStarRE.QPBT.tauLineProj P W line f''))
          (_root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect b') (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b'')) =
        Ψ ((S.lineMeas .bob W line).effect f') ((S.pointMeas .alice W u).effect b') *
          (if _root_.MIPStarRE.QPBT.evalOpt line u f'' = some b'' then
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
              (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauLineProj P W line f'') (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)))
          else 0) := by
      intro f' f'' b' b''
      simp only [Φ, Ψ]
      have hfac := _root_.MIPStarRE.QPBT.ProjectiveSetting.stateQForm_place_AB_prime_prime_mul_BB_prime_two S
        ((S.pointMeas .alice W u).effect b') ((S.lineMeas .bob W line).effect f')
        (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b'') (_root_.MIPStarRE.QPBT.tauLineProj P W line f'')
        (pointMeas_effect_isHermitian S .alice W u b')
        (lineMeas_effect_isHermitian S .bob W line f')
        (tauPointProj_isHermitian W u b'') (tauLineProj_isHermitian W line f'')
      rw [_root_.MIPStarRE.QPBT.stateQForm_eprState_tauLineProj_tauPointProj P W line u hu f'' b''] at hfac
      have hcomm := _root_.MIPStarRE.QPBT.ProjectiveSetting.place_AB''_mul_place_BB'_comm S
        (_root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect b') (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b''))
        (_root_.MIPStarRE.QPBT.heteroKron ((S.lineMeas .bob W line).effect f') (_root_.MIPStarRE.QPBT.tauLineProj P W line f''))
      exact (congrArg (_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat) hcomm.symm).trans hfac
    exact _root_.MIPStarRE.QPBT.overlap_identity_of_mem P W (S.lineMeas .bob W line)
      (S.pointMeas .alice W u) Φ Ψ line u hu hΦ0 hΦl hΦr hΦfact hΨl hΨ0
  · exact _root_.MIPStarRE.QPBT.overlap_identity_of_not_mem P W (S.lineMeas .bob W line)
      (S.pointMeas .alice W u) Φ Ψ line u hu hΦ0 hΨl hΨ0
