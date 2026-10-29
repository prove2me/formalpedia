-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.sum_stateQForm_evalClass_AB_prime_prime_BB_prime_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:33:09.916383+00:00
-- url     : https://prove2.me/submissions/ea68a828-5335-4204-af2e-62132a812c62

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.sum_stateQForm_evalClass_AB''_BB'_eq.
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
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_overlap_AB_prime_prime_BB_prime_eq

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



namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}









/-- The `AB''` placement respects finite sums. -/
theorem place_AB''_finset_sum (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) {γ : Type*}
    (s : Finset γ) (O : γ → _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) :
    S.place .AB'' (∑ g ∈ s, O g : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) =
      ∑ g ∈ s, S.place .AB'' (O g) :=
  _root_.MIPStarRE.QPBT.ProjectiveSetting.place_finset_sum S .AB'' s O











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
          (S.place .AB'' ((S.lineEvalMeasExp .alice W line u).effect o) *
            S.place .BB' ((S.pointMeasExpOption .bob W u).effect o)) =
      ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ
          (_root_.MIPStarRE.QPBT.heteroKron ((S.lineEvalMeas .alice W line u).effect o)
            ((S.pointMeasOption .bob W u).effect o)) := by
  rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.overlap_AB_prime_prime_BB_prime_eq]
  calc
    _ = ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        ∑ f ∈ Finset.univ.filter
          (fun f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) => _root_.MIPStarRE.QPBT.evalOpt line u f = o),
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
            (S.place .AB'' (S.expLineOp .alice W line f) *
              S.place .BB' ((S.pointMeasExpOption .bob W u).effect
                (_root_.MIPStarRE.QPBT.evalOpt line u f))) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.lineEvalMeasExp_effect, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_AB''_finset_sum, Finset.sum_mul,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      rw [(Finset.mem_filter.mp hf).2]
    _ = ∑ f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          (S.place .AB'' (S.expLineOp .alice W line f) *
            S.place .BB' ((S.pointMeasExpOption .bob W u).effect
              (_root_.MIPStarRE.QPBT.evalOpt line u f))) :=
      Finset.sum_fiberwise Finset.univ (fun f => _root_.MIPStarRE.QPBT.evalOpt line u f) _
    _ = _ := by
      simp_rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption_effect_evalOpt]
