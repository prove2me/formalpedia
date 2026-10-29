-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.sum_stateQForm_evalClass_BA_prime_prime_AA_prime_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:33:09.623462+00:00
-- url     : https://prove2.me/submissions/1592ff02-5b76-4e1c-b2af-b658aa9197bd

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.sum_stateQForm_evalClass_BA''_AA'_eq.
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
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_overlap_BA_prime_prime_AA_prime_eq

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







/-- The `BA''` placement respects finite sums. -/
theorem place_BA''_finset_sum (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) {γ : Type*}
    (s : Finset γ) (O : γ → _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) :
    S.place .BA'' (∑ g ∈ s, O g : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) =
      ∑ g ∈ s, S.place .BA'' (O g) :=
  _root_.MIPStarRE.QPBT.ProjectiveSetting.place_finset_sum S .BA'' s O













/-! ## Effects of the completed measurement families -/





/-- The completed expanded point measurement agrees with the expanded point
measurement on proper values. -/
theorem pointMeasExpOption_effect_some (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointMeasExpOption side W u).effect (some b) =
      (S.pointMeasExp side W u).effect b := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [Finset.filter_eq']

/-- The completed expanded point measurement assigns zero to `none`. -/
theorem pointMeasExpOption_effect_none (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointMeasExpOption side W u).effect none = 0 := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  apply Finset.sum_eq_zero
  intro a ha
  exact absurd (Finset.mem_filter.mp ha).2 (by simp)

/-- The expanded point effect selected by a line answer is the completed
expanded point effect at the partial evaluation of the answer. This
identifies the two presentations of item 2 and item 3 of
`lem:qld-comm-line-cons`, blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`. -/
theorem pointMeasExpOption_effect_evalOpt (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) :
    (S.pointMeasExpOption side W u).effect (_root_.MIPStarRE.QPBT.evalOpt line u f) =
      S.expPointEffectAtLineAnswer side W line u f := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointEffectAtLineAnswer
  cases _root_.MIPStarRE.QPBT.evalOpt line u f with
  | none => exact S.pointMeasExpOption_effect_none side W u
  | some a => exact S.pointMeasExpOption_effect_some side W u a



/-- Effects of the expanded evaluation classes are the fiber sums of expanded
line effects. -/
theorem lineEvalMeasExp_effect (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (o : Option (_root_.MIPStarRE.QPBT.PauliScalar P)) :
    (S.lineEvalMeasExp side W line u).effect o =
      ∑ f ∈ Finset.univ.filter
        (fun f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) => _root_.MIPStarRE.QPBT.evalOpt line u f = o),
        S.expLineOp side W line f := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.lineEvalMeasExp
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  rfl

/-! ## Factorization of opposite placements with distinct Pauli factors -/









set_option synthInstance.maxSize 400 in
/-- Operators placed on `AA'` and on `BA''` commute. -/
theorem place_AA'_mul_place_BA''_comm (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (X : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice))
    (Y : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) :
    S.place .AA' X * S.place .BA'' Y = S.place .BA'' Y * S.place .AA' X := by
  have key : ∀ (X' : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
      (Y' : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P)),
      S.place .AA' X' * S.place .BA'' Y' = S.place .BA'' Y' * S.place .AA' X' := by
    intro X' Y'
    rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_left S X', ← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_right S Y',
      ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul, ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul]
    congr 1
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]
  exact key X Y



end ProjectiveSetting

/-! ## The overlap identity -/







end

end MIPStarRE.QPBT

/-!
# Consistency of expanded evaluation classes with expanded points

This module proves item 3 of the expanded-line consistency lemma on the four
directed opposite-placement pairs. On each bipartition the distance between
the evaluation classes of the expanded line measurement and the completed
expanded point measurement is at most twice their inconsistency, which by the
overlap identity equals the inconsistency of the strategy's evaluation classes
with its completed point measurement. The trivial bound `4` on the same
distance supplies the large-`ε` case of the common square-root error.

## References

Item 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:540-545`,
blueprint `eq:qld-comm-line-pt-cons2`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## Overlaps of the evaluation classes -/

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' ((S.pointMeasExpOption .alice W u).effect o) *
            S.place .BA'' ((S.lineEvalMeasExp .bob W line u).effect o)) =
      ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ
          (_root_.MIPStarRE.QPBT.heteroKron ((S.pointMeasOption .alice W u).effect o)
            ((S.lineEvalMeas .bob W line u).effect o)) := by
  rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.overlap_BA_prime_prime_AA_prime_eq]
  calc
    _ = ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        ∑ f ∈ Finset.univ.filter
          (fun f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) => _root_.MIPStarRE.QPBT.evalOpt line u f = o),
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
            (S.place .BA'' (S.expLineOp .bob W line f) *
              S.place .AA' ((S.pointMeasExpOption .alice W u).effect
                (_root_.MIPStarRE.QPBT.evalOpt line u f))) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_AA'_mul_place_BA''_comm, _root_.MIPStarRE.QPBT.ProjectiveSetting.lineEvalMeasExp_effect,
        _root_.MIPStarRE.QPBT.ProjectiveSetting.place_BA''_finset_sum, Finset.sum_mul,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      rw [(Finset.mem_filter.mp hf).2]
    _ = ∑ f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          (S.place .BA'' (S.expLineOp .bob W line f) *
            S.place .AA' ((S.pointMeasExpOption .alice W u).effect
              (_root_.MIPStarRE.QPBT.evalOpt line u f))) :=
      Finset.sum_fiberwise Finset.univ (fun f => _root_.MIPStarRE.QPBT.evalOpt line u f) _
    _ = _ := by
      simp_rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption_effect_evalOpt]
