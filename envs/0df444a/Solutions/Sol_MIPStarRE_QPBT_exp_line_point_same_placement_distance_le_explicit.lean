-- Prove2me | solution 1 for MIPStarRE.QPBT.exp_line_point_same_placement_distance_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:05:34.585342+00:00
-- url     : https://prove2.me/submissions/b58dd31f-0990-439d-8e23-0a1a89a8b1bd

-- Generated proof for MIPStarRE.QPBT.exp_line_point_same_placement_distance_le_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_Strategy_value_le_one
import Theorems.Thm_MIPStarRE_QPBT_aLinePointDist_point_marginal_uniform
import Theorems.Thm_MIPStarRE_QPBT_dLinePointDist_point_marginal_uniform
import Theorems.Thm_MIPStarRE_QPBT_exp_line_point_cons_explicit_prime
import Theorems.Thm_MIPStarRE_QPBT_exp_point_self_cons_explicit
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_of_le_of_le

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



/-- A register placement of the zero operator is zero. -/
theorem place_zero (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement) :
    S.place p (0 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)) = 0 := by
  ext i j
  cases p <;> simp [_root_.MIPStarRE.QPBT.ProjectiveSetting.place]

















/-! ## Effects of the completed measurement families -/















/-! ## Factorization of opposite placements with distinct Pauli factors -/













end ProjectiveSetting

/-! ## The overlap identity -/







end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/AnticommutingObs.lean. -/
/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/



/-- Every strategy value is at most one. This is an alias of the Games-layer
`MIPStarRE.QPBT.Strategy.value_le_one`, which carries the single proof; the name
is kept here so the existing callers of this layer resolve unchanged.
Formalization-only support for `def:tensor-product-value`, blueprint
`ch12_qpbt_games.tex:71-82`. -/
theorem strategy_value_le_one {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) : S.value ≤ 1 :=
  _root_.MIPStarRE.QPBT.Strategy.value_le_one S

















end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/PointComparison.lean. -/
/-!
# Point and line marginal comparisons

Projection contraction and the original line-point law give the two marginal
comparisons used by the X-Z-X line construction.
The joint-point marginal estimates are imported through `Points` from
`Points.WitnessMarginals`, which retains the same statements and proofs.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

/-- The point marginal of the line-point law is uniform. This is the
formalization-only averaging step in `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`, using `lem:alnf` and `lem:dlnf`. -/
theorem avgOver_linePointDist_point (L : _root_.MIPStarRE.QPBT.LdParams)
    (value : (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist L) (fun sample => value sample.2) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)) value := by
  rw [_root_.MIPStarRE.QPBT.linePointDist, _root_.MIPStarRE.QPBT.avgOver_mix]
  rw [← _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map (_root_.MIPStarRE.QPBT.aLinePointDist L) Prod.snd value,
    ← _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map (_root_.MIPStarRE.QPBT.dLinePointDist L) Prod.snd value,
    (_root_.MIPStarRE.QPBT.aLinePointDist_point_marginal_uniform L).1,
    (_root_.MIPStarRE.QPBT.dLinePointDist_point_marginal_uniform L).1]
  ring











/-- Completing both answer alphabets with a zero outcome preserves placed
squared distance. This formalization-only identity reconciles `eq:pasting-q1`
with the completed evaluation convention of `lem:qld-comm-line-cons`. -/
theorem ProjectiveSetting.opFamilyDistSq_postprocess_some
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    {Sample Answer : Type*} [Fintype Answer] [DecidableEq Answer]
    (law : _root_.LIDT.MIPStarRE.LDT.Distribution Sample) (p1 p2 : _root_.MIPStarRE.QPBT.Placement)
    (first : Sample → _root_.LIDT.MIPStarRE.Quantum.Measurement Answer (S.ExpandedLocalSpace p1.side))
    (second : Sample → _root_.LIDT.MIPStarRE.Quantum.Measurement Answer (S.ExpandedLocalSpace p2.side)) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq law
      (fun sample answer => S.place p1 (((first sample).postprocess some).effect answer))
      (fun sample answer => S.place p2 (((second sample).postprocess some).effect answer))
      S.psiHat =
    _root_.MIPStarRE.QPBT.opFamilyDistSq law (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat := by
  classical
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  congr 1
  funext sample
  rw [Fintype.sum_option]
  simp [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess,
    _root_.LIDT.MIPStarRE.Quantum.Submeasurement.postprocess, Finset.sum_filter,
    S.place_zero, _root_.MIPStarRE.QPBT.applyOperatorToState]



























end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/SelfConsistency.lean. -/
/-!
# Self-consistency of the expanded line measurements

This module proves item 1 of the expanded-line consistency lemma on the two
opposite-placement bipartitions. The strategy line measurements are
self-consistent between the two players on average over the line-point
distribution, because a disagreement on a sampled line is rejected by the
corresponding self-loop of the Pauli basis test; the Pauli line projectors are
perfectly consistent on an EPR pair; and the data-processing inequality
transfers the product estimate to the addition postprocessing that defines the
expanded line measurement.

The module also records that the error parameter of a projective setting is
nonnegative, which is not assumed by the structure and is needed by the other
two items as well.

## References

The declarations formalize `enu:qld-comm-line-self-cons`, item 1 of
`lem:qld-comm-line-cons`, whose paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-532`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Self-consistency of the unexpanded line measurements -/











namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The error parameter -/

/-- The error parameter of a projective setting is nonnegative. Nothing in the
structure assumes this: it follows from the winning premise `1 - ε ≤ value`
together with the bound `value ≤ 1` satisfied by the value of every strategy.
Formalization-only auxiliary supplying the sign condition of the winning
implications used in items 2 and 3 of `lem:qld-comm-line-cons`. -/
theorem eps_nonneg (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : 0 ≤ ε := by
  have hv := _root_.MIPStarRE.QPBT.WinImplications.strategy_value_le_one S.toStrategy
  have hw := S.win
  linarith

/-! ## Placement of differences on the two bipartitions -/

-- The four-level product indices below exceed the default instance-search
-- size.







/-! ## Fine-product consistency on the two bipartitions -/





/-! ## Data processing and transport back to the six registers -/













end ProjectiveSetting

end

end MIPStarRE.QPBT

/-!
# Point and line marginal comparisons

Projection contraction and the original line-point law give the two marginal
comparisons used by the X-Z-X line construction.
The joint-point marginal estimates are imported through `Points` from
`Points.WitnessMarginals`, which retains the same statements and proofs.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
      (p1 p2 : _root_.MIPStarRE.QPBT.Placement), p1.IsOpposite p2 → ∀ W : _root_.MIPStarRE.QPBT.PauliKind,
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample answer => S.place p2
          ((S.lineEvalMeasExp p2.side W sample.1 sample.2).effect answer))
        (fun sample answer => S.place p2
          ((S.pointMeasExpOption p2.side W sample.2).effect answer))
        S.psiHat ≤ 1040 * (ε + _root_.MIPStarRE.QPBT.deltaLine ε) := by
  intro P ε S p1 p2 hopp W
  classical
  have hreverse : p2.IsOpposite p1 := by
    cases p1 <;> cases p2 <;> simp_all [_root_.MIPStarRE.QPBT.Placement.IsOpposite]
  have hpoint : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
      (fun sample answer => S.place p1
        ((S.pointMeasExpOption p1.side W sample.2).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side W sample.2).effect answer)) S.psiHat ≤ 172 * ε := by
    unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
    erw [S.opFamilyDistSq_postprocess_some]
    unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
    rw [_root_.MIPStarRE.QPBT.avgOver_linePointDist_point P.toLdParams (fun point =>
      ∑ answer, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (S.place p1 ((S.pointMeasExp p1.side W point).effect answer) -
          S.place p2 ((S.pointMeasExp p2.side W point).effect answer)) S.psiHat‖ ^ 2)]
    exact _root_.MIPStarRE.QPBT.exp_point_self_cons_explicit P ε S p1 p2 hopp W
  have htri := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
    (_root_.MIPStarRE.QPBT.exp_line_point_cons_explicit_prime P ε S p2 p1 hreverse W) hpoint
  refine htri.trans ?_
  have hε := S.eps_nonneg
  have hline : 0 ≤ _root_.MIPStarRE.QPBT.deltaLine ε := Real.sqrt_nonneg ε
  nlinarith
