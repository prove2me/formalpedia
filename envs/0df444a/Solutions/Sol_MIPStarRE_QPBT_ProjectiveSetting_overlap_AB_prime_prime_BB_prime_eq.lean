-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.overlap_AB_prime_prime_BB_prime_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:28:55.91342+00:00
-- url     : https://prove2.me/submissions/f9f4abf5-2b82-4a9e-b99b-3f372aeaef7a

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.overlap_AB''_BB'_eq.
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
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_LinePointOverlap
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Projector
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_stateQForm_place_AB_prime_prime_mul_BB_prime_two
import Theorems.Thm_MIPStarRE_QPBT_overlap_identity_of_mem
import Theorems.Thm_MIPStarRE_QPBT_overlap_identity_of_not_mem
import Theorems.Thm_MIPStarRE_QPBT_stateQForm_eprState_tauPointProj_tauLineProj

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







/-- The `BB'` placement of zero is zero. -/
theorem place_BB'_zero (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    S.place .BB' (0 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) = 0 :=
  _root_.MIPStarRE.QPBT.ProjectiveSetting.place_zero S .BB'

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

/-- Tensor placement distributes over a finite sum in the left factor. -/
theorem heteroKron_finset_sum_left {β ιA ιB : Type*} (s : Finset β)
    (A : β → _root_.LIDT.MIPStarRE.Quantum.Op ιA) (C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (∑ b ∈ s, A b) C = ∑ b ∈ s, _root_.MIPStarRE.QPBT.heteroKron (A b) C :=
  _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left s A C







/-! ## Matrices of isometries -/





















/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

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
          (S.place .AB'' (S.expLineOp .alice W line f) *
            S.place .BB' (S.expPointEffectAtLineAnswer .bob W line u f)) =
      ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ
          (_root_.MIPStarRE.QPBT.heteroKron ((S.lineEvalMeas .alice W line u).effect o)
            ((S.pointMeasOption .bob W u).effect o)) := by
  let Φ : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice) →
      _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob) → ℝ := fun X Y =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat (S.place .AB'' X * S.place .BB' Y)
  let Ψ : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA → _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB → ℝ := fun L Q =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ (_root_.MIPStarRE.QPBT.heteroKron L Q)
  have hΦ0 : ∀ X, Φ X 0 = 0 := by
    intro X
    simp only [Φ]
    rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_BB'_zero, mul_zero, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_zero]
  have hΦl : ∀ (s : Finset (_root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) ×
        _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)))
      (X : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) × _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) →
        _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice))
      (Y : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y := by
    intro s X Y
    simp only [Φ]
    rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_AB''_finset_sum, Finset.sum_mul,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  have hΦr : ∀ (X : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice))
      (t : Finset (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P))
      (Y : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P → _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j) := by
    intro X t Y
    simp only [Φ]
    rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_BB'_finset_sum, Finset.mul_sum,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  have hΨl : ∀ (s : Finset (_root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)))
      (A : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) → _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
      (B : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB), Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B := by
    intro s A B
    simp only [Ψ]
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_finset_sum_left,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  have hΨ0 : ∀ A, Ψ A 0 = 0 := by
    intro A
    simp only [Ψ]
    rw [_root_.MIPStarRE.QPBT.heteroKron_zero_right, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_zero]
  change ∑ f, Φ (S.expLineOp .alice W line f)
      (S.expPointEffectAtLineAnswer .bob W line u f) =
    ∑ o, Ψ (((S.lineMeas .alice W line).postprocess (_root_.MIPStarRE.QPBT.evalOpt line u)).effect o)
      (((S.pointMeas .bob W u).postprocess some).effect o)
  simp_rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.expPointEffectAtLineAnswer_eq_elim]
  by_cases hu : u ∈ line.pointSet
  · have hΦfact : ∀ (f' f'' : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d))
        (b' b'' : _root_.MIPStarRE.QPBT.PauliScalar P),
        Φ (_root_.MIPStarRE.QPBT.heteroKron ((S.lineMeas .alice W line).effect f')
            (_root_.MIPStarRE.QPBT.tauLineProj P W line f''))
          (_root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .bob W u).effect b') (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b'')) =
        Ψ ((S.lineMeas .alice W line).effect f') ((S.pointMeas .bob W u).effect b') *
          (if _root_.MIPStarRE.QPBT.evalOpt line u f'' = some b'' then
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
              (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauLineProj P W line f'') (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)))
          else 0) := by
      intro f' f'' b' b''
      simp only [Φ, Ψ]
      have hfac := _root_.MIPStarRE.QPBT.ProjectiveSetting.stateQForm_place_AB_prime_prime_mul_BB_prime_two S
        ((S.lineMeas .alice W line).effect f') ((S.pointMeas .bob W u).effect b')
        (_root_.MIPStarRE.QPBT.tauLineProj P W line f'') (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b'')
        (lineMeas_effect_isHermitian S .alice W line f')
        (pointMeas_effect_isHermitian S .bob W u b')
        (tauLineProj_isHermitian W line f'') (tauPointProj_isHermitian W u b'')
      rw [_root_.MIPStarRE.QPBT.stateQForm_eprState_tauPointProj_tauLineProj P W line u hu f'' b''] at hfac
      exact hfac
    exact _root_.MIPStarRE.QPBT.overlap_identity_of_mem P W (S.lineMeas .alice W line)
      (S.pointMeas .bob W u) Φ Ψ line u hu hΦ0 hΦl hΦr hΦfact hΨl hΨ0
  · exact _root_.MIPStarRE.QPBT.overlap_identity_of_not_mem P W (S.lineMeas .alice W line)
      (S.pointMeas .bob W u) Φ Ψ line u hu hΦ0 hΨl hΨ0
