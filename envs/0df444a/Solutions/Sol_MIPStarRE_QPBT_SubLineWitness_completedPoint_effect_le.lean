-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.completedPoint_effect_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:51:53.720986+00:00
-- url     : https://prove2.me/submissions/fb4a9608-e02f-4128-987d-f7d85ff10f16

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.completedPoint_effect_le.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Measurement
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_combinedPolynomial_evaluatesTo

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/WinImplications/LowDegree.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.instDecidableRel_qPBT
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.linePointFintypeCanonical
/-!
# Low-degree winning implications

This module proves the exact line-point and Pauli-basis consistency bounds.

## References

The line-point and Pauli-basis consistency theorems prove items 2 and 3
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications





































/-- A uniquely determined line evaluation is returned by `evalOpt`. -/
theorem evalOpt_eq_some_of_evaluatesTo {L : _root_.MIPStarRE.QPBT.LdParams} {c : ℕ}
    (line : _root_.MIPStarRE.QPBT.LineDesc L) (f : _root_.MIPStarRE.QPBT.DegPoly L c) (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)
    (a : _root_.MIPStarRE.QPBT.ScalarQ L) (h : _root_.MIPStarRE.QPBT.EvaluatesTo line f u a) :
    _root_.MIPStarRE.QPBT.evalOpt line u f = some a := by
  unfold _root_.MIPStarRE.QPBT.evalOpt
  rw [dif_pos ⟨a, h⟩]
  apply congrArg some
  obtain ⟨t, ht⟩ := h.1
  exact ((Classical.choose_spec ⟨a, h⟩).2 t ht).symm.trans (h.2 t ht)
























































end WinImplications

end

end MIPStarRE.QPBT

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









/-- The partial evaluation returns `some a` exactly when the polynomial
evaluates to `a`. This is the characterization that makes `evalOpt` the total
form of the evaluation classes of `def:ideg-deg-polynomials`. -/
theorem evalOpt_eq_some_iff {L : _root_.MIPStarRE.QPBT.LdParams} {c : ℕ} (line : _root_.MIPStarRE.QPBT.LineDesc L)
    (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) (f : _root_.MIPStarRE.QPBT.DegPoly L c) (a : _root_.MIPStarRE.QPBT.ScalarQ L) :
    _root_.MIPStarRE.QPBT.evalOpt line u f = some a ↔ _root_.MIPStarRE.QPBT.EvaluatesTo line f u a := by
  constructor
  · intro h
    unfold _root_.MIPStarRE.QPBT.evalOpt at h
    by_cases hex : ∃ a : _root_.MIPStarRE.QPBT.ScalarQ L, _root_.MIPStarRE.QPBT.EvaluatesTo line f u a
    · rw [dif_pos hex, Option.some_inj] at h
      rw [← h]
      exact Classical.choose_spec hex
    · rw [dif_neg hex] at h
      exact absurd h (by simp)
  · exact _root_.MIPStarRE.QPBT.WinImplications.evalOpt_eq_some_of_evaluatesTo line f u a











end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLines/Measurement.lean. -/
/-!
# Conditional extended-line measurements

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

























/-- A determined direct evaluation gives precisely its completed answer. -/
private theorem directEvalOpt_eq_some_of_evaluatesTo {params : _root_.MIPStarRE.QPBT.DirectLdParams} {bound : ℕ}
    (line : _root_.MIPStarRE.QPBT.DirectLineDesc params) (polynomial : _root_.MIPStarRE.QPBT.DirectDegPoly params bound)
    (point : Fin params.m → _root_.MIPStarRE.QPBT.DirectScalarQ params) (value : _root_.MIPStarRE.QPBT.DirectScalarQ params)
    (heval : _root_.MIPStarRE.QPBT.DirectEvaluatesTo line polynomial point value) :
    _root_.MIPStarRE.QPBT.directEvalOpt line point polynomial = some value := by
  classical
  have hexists : ∃ answer, _root_.MIPStarRE.QPBT.DirectEvaluatesTo line polynomial point answer := ⟨value, heval⟩
  rw [_root_.MIPStarRE.QPBT.directEvalOpt, dif_pos hexists]
  obtain ⟨parameter, hparameter⟩ := heval.1
  exact congrArg some (((Classical.choose_spec hexists).2 parameter hparameter).symm.trans
    (heval.2 parameter hparameter))





/-- Completed evaluation of the actual combination agrees with the source
linear combination whenever both source evaluations are defined. -/
theorem SubLineWitness.combinedPolynomial_evalOpt {params : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness params) (sample : _root_.MIPStarRE.QPBT.SubLineTriple params)
    (hsample : sample ∈ sublines.D.support)
    (polynomials : _root_.MIPStarRE.QPBT.DegPoly params.toLdParams (params.m * params.d) ×
      _root_.MIPStarRE.QPBT.DegPoly params.toLdParams (params.m * params.d))
    (point : Fin params.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd)
    (hpoint : point ∈ sample.1.pointSet) (valueX valueZ : _root_.MIPStarRE.QPBT.PauliScalar params)
    (hevalX : _root_.MIPStarRE.QPBT.evalOpt sample.2.1 (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli params point)) polynomials.1 =
      some valueX)
    (hevalZ : _root_.MIPStarRE.QPBT.evalOpt sample.2.2 (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli params point)) polynomials.2 =
      some valueZ) :
    (_root_.MIPStarRE.QPBT.directEvalOpt sample.1 point (sublines.combinedPolynomial sample hsample polynomials)).map
      (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params) =
        some ((_root_.MIPStarRE.QPBT.directPointToPauli params point) (_root_.MIPStarRE.QPBT.alphaVar params.m) * valueX +
          (_root_.MIPStarRE.QPBT.directPointToPauli params point) (_root_.MIPStarRE.QPBT.betaVar params.m) * valueZ) := by
  rw [directEvalOpt_eq_some_of_evaluatesTo _ _ _ _
    (sublines.combinedPolynomial_evaluatesTo sample hsample polynomials point hpoint valueX valueZ
      ((_root_.MIPStarRE.QPBT.evalOpt_eq_some_iff _ _ _ _).mp hevalX) ((_root_.MIPStarRE.QPBT.evalOpt_eq_some_iff _ _ _ _).mp hevalZ))]
  simp


















end

end MIPStarRE.QPBT

/-!
# Consistency of the extended-line measurements

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

theorem solution {params : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness params) (sample : _root_.MIPStarRE.QPBT.SubLineTriple params)
    (hsample : sample ∈ sublines.D.support)
    (polynomials : _root_.MIPStarRE.QPBT.DegPoly params.toLdParams (params.m * params.d) ×
      _root_.MIPStarRE.QPBT.DegPoly params.toLdParams (params.m * params.d))
    (point : Fin params.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd)
    (hpoint : point ∈ sample.1.pointSet)
    (measurement : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar params × _root_.MIPStarRE.QPBT.PauliScalar params) Carrier) :
    (measurement.postprocess (fun pair => (some pair.1, some pair.2))).effect
      (_root_.MIPStarRE.QPBT.evalOpt sample.2.1 (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli params point)) polynomials.1,
        _root_.MIPStarRE.QPBT.evalOpt sample.2.2 (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli params point)) polynomials.2) ≤
      (measurement.postprocess (fun pair => some
        ((_root_.MIPStarRE.QPBT.directPointToPauli params point) (_root_.MIPStarRE.QPBT.alphaVar params.m) * pair.1 +
          (_root_.MIPStarRE.QPBT.directPointToPauli params point) (_root_.MIPStarRE.QPBT.betaVar params.m) * pair.2))).effect
        ((_root_.MIPStarRE.QPBT.directEvalOpt sample.1 point
          (sublines.combinedPolynomial sample hsample polynomials)).map
            (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params)) := by
  classical
  have hnoneX (value : Option (_root_.MIPStarRE.QPBT.PauliScalar params)) :
      (measurement.postprocess (fun pair => (some pair.1, some pair.2))).effect (none, value) =
        0 := by
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
    apply Finset.sum_eq_zero
    intro pair hpair
    have himpossible := congrArg Prod.fst (Finset.mem_filter.mp hpair).2
    simp at himpossible
  have hnoneZ (value : Option (_root_.MIPStarRE.QPBT.PauliScalar params)) :
      (measurement.postprocess (fun pair => (some pair.1, some pair.2))).effect (value, none) =
        0 := by
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
    apply Finset.sum_eq_zero
    intro pair hpair
    have himpossible := congrArg Prod.snd (Finset.mem_filter.mp hpair).2
    simp at himpossible
  cases hevalX : _root_.MIPStarRE.QPBT.evalOpt sample.2.1 (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli params point)) polynomials.1 with
  | none =>
    erw [hnoneX]
    exact _root_.LIDT.MIPStarRE.Quantum.Submeasurement.pos _ _
  | some valueX =>
    cases hevalZ : _root_.MIPStarRE.QPBT.evalOpt sample.2.2 (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli params point)) polynomials.2 with
    | none =>
      erw [hnoneZ]
      exact _root_.LIDT.MIPStarRE.Quantum.Submeasurement.pos _ _
    | some valueZ =>
      rw [sublines.combinedPolynomial_evalOpt sample hsample polynomials point hpoint
        valueX valueZ hevalX hevalZ]
      have hinjective : Function.Injective
          (fun pair : _root_.MIPStarRE.QPBT.PauliScalar params × _root_.MIPStarRE.QPBT.PauliScalar params => (some pair.1, some pair.2)) := by
        intro left right hequal
        exact Prod.ext (Option.some.inj (congrArg Prod.fst hequal))
          (Option.some.inj (congrArg Prod.snd hequal))
      erw [_root_.MIPStarRE.QPBT.SandwichProduct.postprocess_effect_of_injective measurement _ hinjective
        (valueX, valueZ)]
      rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
      exact Finset.single_le_sum (fun pair _ => measurement.pos pair)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
