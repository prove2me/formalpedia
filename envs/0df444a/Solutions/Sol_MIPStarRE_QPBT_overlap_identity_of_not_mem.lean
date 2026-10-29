-- Prove2me | solution 1 for MIPStarRE.QPBT.overlap_identity_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:59:25.658142+00:00
-- url     : https://prove2.me/submissions/03526b59-4ea4-465a-9e8c-3b823cc1263a

-- Generated proof for MIPStarRE.QPBT.overlap_identity_of_not_mem.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Projector
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

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

/- Source helpers from QPBT/Observables/LineMeasurement/Evaluation.lean. -/
/-!
# Evaluation of line polynomials at a sampled point

This module records the elementary calculus of the partial evaluation
`evalOpt` of a coefficient-list line polynomial at a point: the evaluation of
a sum is the sum of the evaluations whenever both summands evaluate, a summand
of an evaluating sum evaluates whenever the other summand does, the value is
unique, and nothing evaluates at a point off the line. These facts underlie
the manipulation of the evaluation classes in items 2 and 3 of the
expanded-line consistency lemma.

Every declaration below is a formalization-only auxiliary: the source uses
these facts about evaluation without stating them.

## References

The evaluation classes `[eval_u(·) = a]` are `def:ideg-deg-polynomials`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:51-58`. They are
manipulated in `eq:qld-comm-line-pt-cons` and `eq:qld-comm-line-pt-cons2`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT











/-- The partial evaluation returns `none` exactly when no value is
determined. This is the outcome that completes the evaluation classes to a
measurement, written `[eval_u(·) = ⊥]` in `def:ideg-deg-polynomials`. -/
theorem evalOpt_eq_none_iff {L : _root_.MIPStarRE.QPBT.LdParams} {c : ℕ} (line : _root_.MIPStarRE.QPBT.LineDesc L)
    (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) (f : _root_.MIPStarRE.QPBT.DegPoly L c) :
    _root_.MIPStarRE.QPBT.evalOpt line u f = none ↔ ¬ ∃ a : _root_.MIPStarRE.QPBT.ScalarQ L, _root_.MIPStarRE.QPBT.EvaluatesTo line f u a := by
  unfold _root_.MIPStarRE.QPBT.evalOpt
  split_ifs with hex <;> simp [hex]







/-- Off the line, no line polynomial evaluates, so every outcome falls in
the `none` class. -/
theorem evalOpt_eq_none_of_not_mem {L : _root_.MIPStarRE.QPBT.LdParams} {c : ℕ} {line : _root_.MIPStarRE.QPBT.LineDesc L}
    {u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L} (hu : u ∉ line.pointSet) (f : _root_.MIPStarRE.QPBT.DegPoly L c) :
    _root_.MIPStarRE.QPBT.evalOpt line u f = none := by
  rw [_root_.MIPStarRE.QPBT.evalOpt_eq_none_iff]
  rintro ⟨a, ha⟩
  exact hu ha.1

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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    {ιL ιP : Type*} [Fintype ιL] [DecidableEq ιL] [Fintype ιP] [DecidableEq ιP]
    (LM : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) ιL)
    (PM : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams) ιP)
    (Φ : _root_.LIDT.MIPStarRE.Quantum.Op (ιL × _root_.MIPStarRE.QPBT.PauliRegister P) → _root_.LIDT.MIPStarRE.Quantum.Op (ιP × _root_.MIPStarRE.QPBT.PauliRegister P) → ℝ)
    (Ψ : _root_.LIDT.MIPStarRE.Quantum.Op ιL → _root_.LIDT.MIPStarRE.Quantum.Op ιP → ℝ)
    (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) (u : Fin P.m → _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)
    (hu : u ∉ line.pointSet)
    (hΦ0 : ∀ X, Φ X 0 = 0)
    (hΨl : ∀ (s : Finset (_root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)))
      (A : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) → _root_.LIDT.MIPStarRE.Quantum.Op ιL) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιP),
      Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B)
    (hΨ0 : ∀ A, Ψ A 0 = 0) :
    (∑ f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d),
      Φ (∑ p ∈ Finset.univ.filter
          (fun p : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) ×
            _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2 = f),
          _root_.MIPStarRE.QPBT.heteroKron (LM.effect p.1) (_root_.MIPStarRE.QPBT.tauLineProj P W line p.2))
        ((_root_.MIPStarRE.QPBT.evalOpt line u f).elim 0 (fun a =>
          ∑ q ∈ Finset.univ.filter
            (fun q : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams × _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams => q.1 + q.2 = a),
            _root_.MIPStarRE.QPBT.heteroKron (PM.effect q.1) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u q.2)))) =
      ∑ o : Option (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams),
        Ψ ((LM.postprocess (_root_.MIPStarRE.QPBT.evalOpt line u)).effect o)
          ((PM.postprocess some).effect o) := by
  have hnone : ∀ f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d), _root_.MIPStarRE.QPBT.evalOpt line u f = none :=
    fun f => _root_.MIPStarRE.QPBT.evalOpt_eq_none_of_not_mem hu f
  rw [Finset.sum_eq_zero fun f _ => by rw [hnone f, Option.elim_none, hΦ0]]
  symm
  refine Finset.sum_eq_zero fun o _ => ?_
  rcases o with _ | b
  · have hPt : (PM.postprocess some).effect none = 0 := by
      rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
      apply Finset.sum_eq_zero
      intro a ha
      exact absurd (Finset.mem_filter.mp ha).2 (by simp)
    rw [hPt, hΨ0]
  · have hempty : Finset.univ.filter
        (fun f' : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) => _root_.MIPStarRE.QPBT.evalOpt line u f' = some b) =
          ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro f' _ h
      rw [hnone f'] at h
      exact absurd h (by simp)
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, hempty, Finset.sum_empty]
    simpa using hΨl ∅ (fun _ => 0) ((PM.postprocess some).effect (some b))
