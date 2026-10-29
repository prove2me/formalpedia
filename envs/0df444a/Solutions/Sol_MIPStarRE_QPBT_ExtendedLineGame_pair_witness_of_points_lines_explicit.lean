-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.pair_witness_of_points_lines_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:42:25.971999+00:00
-- url     : https://prove2.me/submissions/15767f45-91c5-4582-917f-6f05974d0992

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.pair_witness_of_points_lines_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_PairMeasurement
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_RetainedPointMass
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_RoundedPolynomialEstimates
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_WrongVariableMass
import Definitions.Def_QPBT_QPBT_Combining_PairCompletion
import Definitions.Def_QPBT_QPBT_Combining_PassingError
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_ExplicitConstants
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_directPairMeasurement_consistency_le
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_retainedPointMismatch_le_ordered_error
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_rounded_polynomial_separated_mass_explicit

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.PolynomialImageBounds
end MIPStarRE.QPBT.PolynomialImageBounds

/- Source helpers from QPBT/Combining/ExtendedLineGame/PairPointConsistency.lean. -/
/-!
# Point consistency of the completed polynomial-pair measurements

The polynomial-pair completion is applied to the actual rounded outcomes. Its missing
mass and retained point mismatch are kept separate until the final bound.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`,
`eq:qld-sgg-completeness` and `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.ExtendedLineGame

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section













/-- The completed pair measurement has point defect at most bad mass plus
`2E + 4/q`, for each basis and every opposite placement. -/
theorem directPairMeasurement_consistency_le_ordered_error
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopposite : p1.IsOpposite p2)
    (R : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : _root_.MIPStarRE.QPBT.Measurement.IsProjective R) (pair₀ : _root_.MIPStarRE.QPBT.PolyPair P) (reverse : Bool) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
      (fun x a => S.place p1 (((_root_.MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement R pair₀).postprocess
        (_root_.MIPStarRE.QPBT.evalAt (if reverse then .Z else .X) x)).effect a))
      (fun x a => S.place p2
        ((S.pointMeasExp p2.side (if reverse then .Z else .X) x).effect a)) S.psiHat ≤
      _root_.MIPStarRE.QPBT.ExtendedLineGame.separatedPolynomialMass S p1 R +
        2 * _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError S p1 p2 R reverse + 4 / P.q := by
  have h := _root_.MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement_consistency_le S p1 p2 hopposite R hR pair₀
    (if reverse then .Z else .X)
  have hm := _root_.MIPStarRE.QPBT.ExtendedLineGame.retainedPointMismatch_le_ordered_error S p1 p2 hopposite R hR reverse
  linarith










end

end MIPStarRE.QPBT.ExtendedLineGame

/- Source helpers from QPBT/Combining/PairCompletion.lean. -/
/-!
# Restricting and completing global polynomial-pair measurements

The combining map embeds pairs of bounded individual-degree polynomials into
extended polynomials. Restricting a measurement along this embedding produces a
submeasurement whose missing operator is the sum of the noncombined effects.
Relabeling those effects by one specified pair completes the measurement and
preserves projectivity.

These algebraic constructions do not establish the concentration estimate
`eq:qld-g-non-separable` or the point consistency required by
`exists_globalPairWitness`; those are separate quantitative obligations.

## References

- Blueprint `lem:qld-4-7`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`,
  `eq:qld-sgg-completeness` and the final completion paragraph.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open scoped BigOperators MatrixOrder

noncomputable section



























/-- The completed polynomial-pair measurement is projective whenever the
extended-polynomial measurement is projective. This proves the qualitative
completion step in `lem:qld-4-7`, paper lines 1402--1404, without assuming its
unproved consistency conclusion. -/
theorem completedPairMeasurement_projective (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : _root_.LIDT.MIPStarRE.Quantum.Measurement
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (_root_.MIPStarRE.QPBT.PauliScalar P) P.d) carrier)
    (hprojective : _root_.MIPStarRE.QPBT.Measurement.IsProjective measurement) (completionPair : _root_.MIPStarRE.QPBT.PolyPair P) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.completedPairMeasurement P measurement completionPair) := by
  exact _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective measurement hprojective _

open LIDT.MIPStarRE.Quantum DistanceCalculus





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLineGame/PairMeasurement.lean. -/
/-!
# Transport of the polynomial-pair completion

The actual singleton outcomes are transported by the canonical field
equivalence before applying the algebraic completion.
Every original outcome is retained, including those outside the combining image.

## References

Paper `eq:qld-sgg-completeness` and the completion paragraph of `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.ExtendedLineGame

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section













/-- Projectivity follows from completion and injective field transport. -/
theorem directPairMeasurement_projective {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (R : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd ι)
    (hR : _root_.MIPStarRE.QPBT.Measurement.IsProjective R) (pair₀ : _root_.MIPStarRE.QPBT.PolyPair P) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement R pair₀) :=
  _root_.MIPStarRE.QPBT.completedPairMeasurement_projective P _
    (_root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective R hR _) pair₀





end

end MIPStarRE.QPBT.ExtendedLineGame

/-!
# Point consistency of the completed polynomial-pair measurements

The polynomial-pair completion is applied to the actual rounded outcomes. Its missing
mass and retained point mismatch are kept separate until the final bound.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`,
`eq:qld-sgg-completeness` and `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/



open scoped BigOperators MatrixOrder

open MIPStarRE.QPBT.ExtendedLineGame

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus MIPStarRE.QPBT.PolynomialImageBounds

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε δQ δL : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
        (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ) (_lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness S points δL),
      let delta := _root_.MIPStarRE.QPBT.deltaLd _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower
        (_root_.MIPStarRE.QPBT.directPassingErrorEnvelope (δQ + δL) ((P.m * P.d : ℝ) / P.q))
        P.q (2 * P.m + 2) P.d 1
      let eta := delta + Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) +
        2 * Real.sqrt (2 * delta)
      Nonempty (_root_.MIPStarRE.QPBT.GlobalPairWitness S (8 * (4 * eta + 8 * δQ) +
        (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q))) := by
  let a := _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant
  let b := _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower
  have h := _root_.MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_separated_mass_explicit
  intro P ε δQ δL S points lines delta eta
  obtain ⟨RA, RB, hRA, hRB, horder, hmassA, hmassB⟩ := h P ε δQ δL S points lines
  let pair₀ : _root_.MIPStarRE.QPBT.PolyPair P := (0, 0)
  have hA (reverse : Bool) := _root_.MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement_consistency_le_ordered_error
    S .AA' .BA'' (by trivial) RA hRA pair₀ reverse
  have hB (reverse : Bool) := _root_.MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement_consistency_le_ordered_error
    S .BB' .AB'' (by trivial) RB hRB pair₀ reverse
  have hbound :
      6 * (4 * eta + 8 * δQ) + (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) +
        2 * (4 * eta + 8 * δQ) + 4 / P.q =
      8 * (4 * eta + 8 * δQ) + (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q) := by
    push_cast
    ring
  refine ⟨{
    Smeas := fun side => match side with
      | .alice => _root_.MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement RA pair₀
      | .bob => _root_.MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement RB pair₀
    projective := ?_
    point_consistent_alice := ?_
    point_consistent_bob := ?_ }⟩
  · intro side
    cases side
    · exact _root_.MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement_projective RA hRA pair₀
    · exact _root_.MIPStarRE.QPBT.ExtendedLineGame.directPairMeasurement_projective RB hRB pair₀
  · intro W
    cases W
    · exact (hA false).trans ((add_le_add
        (add_le_add hmassA (mul_le_mul_of_nonneg_left (horder false).1 (by norm_num)))
        le_rfl).trans_eq hbound)
    · exact (hA true).trans ((add_le_add
        (add_le_add hmassA (mul_le_mul_of_nonneg_left (horder true).1 (by norm_num)))
        le_rfl).trans_eq hbound)
  · intro W
    cases W
    · exact (hB false).trans ((add_le_add
        (add_le_add hmassB (mul_le_mul_of_nonneg_left (horder false).2 (by norm_num)))
        le_rfl).trans_eq hbound)
    · exact (hB true).trans ((add_le_add
        (add_le_add hmassB (mul_le_mul_of_nonneg_left (horder true).2 (by norm_num)))
        le_rfl).trans_eq hbound)
