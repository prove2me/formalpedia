-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_separated_mass_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:37:56.768769+00:00
-- url     : https://prove2.me/submissions/d7004793-e73a-4650-ba82-b2e55826f646

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_separated_mass_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_RoundedPolynomialEstimates
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_ScalarNonlinearMass
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_ScalarPolynomial
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_WrongVariableMass
import Definitions.Def_QPBT_QPBT_Combining_PassingError
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_ExplicitConstants
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_exists_polyPair_of_scalar_separated
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_rounded_polynomial_ordered_estimates_explicit
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_scalarNonlinearMass_le_ordered_error
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_scalarWrongVariableMass_le_ordered_error

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

/- Source helpers from QPBT/Combining/ExtendedLineGame/WrongVariableMass.lean. -/
/-!
# Wrong-variable mass of rounded polynomial outcomes

The two block orders use the actual projected state vectors and the full
ordered-error sum. A common exceptional coefficient controls all outcomes
of the fixed-block measurement before their weights are summed.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1328-1368`,
`eq:qld-g-separable`, `eq:qld-g-48`, `eq:qld-g-2`, and the two wrong-variable
mass bounds. This supports blueprint `lem:qld-4-7`; it does not establish
the subsequent retained overlaps or global polynomial-pair witness.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section

namespace ExtendedLineGame


















private theorem separatedPolynomialMass_le_three_masses {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement)
    (R : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p.side)) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.separatedPolynomialMass S p R ≤ _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarNonlinearMass S p R +
      _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarWrongVariableMass S p R false + _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarWrongVariableMass S p R true := by
  classical
  simp only [_root_.MIPStarRE.QPBT.ExtendedLineGame.separatedPolynomialMass, _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarNonlinearMass, _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarWrongVariableMass,
    Finset.sum_filter, Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  by_cases hlin : ∃ r t : MvPolynomial (Fin (2 * P.m)) (_root_.MIPStarRE.QPBT.PauliScalar P),
      _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial P g = MvPolynomial.C r * MvPolynomial.X 0 +
        MvPolynomial.C t * MvPolynomial.X 1
  · by_cases hX : ∃ r, _root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial P g (Finsupp.single 0 1) true =
        MvPolynomial.C r
    · by_cases hZ : ∃ r, _root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial P g (Finsupp.single 1 1) false =
          MvPolynomial.C r
      · have himage := _root_.MIPStarRE.QPBT.ExtendedLineGame.exists_polyPair_of_scalar_separated P g hlin hX hZ
        simp only [hlin, hX, hZ, not_true_eq_false, and_false, ↓reduceIte, zero_add]
        split_ifs with hout
        · exact le_rfl
        · exact False.elim (hout himage)
      · simp only [hlin, hX, hZ, not_false_eq_true, not_true_eq_false, and_true,
          and_false, ↓reduceIte, zero_add, add_zero]
        split_ifs <;> nlinarith [sq_nonneg ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p (R.effect g)) S.psiHat‖]
    · simp only [hlin, hX, not_false_eq_true, not_true_eq_false, true_and, ↓reduceIte,
        zero_add]
      split_ifs <;> nlinarith [sq_nonneg ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p (R.effect g)) S.psiHat‖]
  · simp only [hlin, not_false_eq_true, false_and, ↓reduceIte, add_zero]
    split_ifs <;> nlinarith [sq_nonneg ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p (R.effect g)) S.psiHat‖]

/-- The union of the three excluded classes is bounded in the actual two
ordered errors. The image is the existing faithful `combinePoly` encoding
with both components in `Poly P`. This proves concentration only, as in
`eq:qld-g-non-separable`, supporting blueprint `lem:qld-4-7`. -/
theorem separatedPolynomialMass_le_ordered_errors {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopposite : p1.IsOpposite p2)
    (R : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : _root_.MIPStarRE.QPBT.Measurement.IsProjective R) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.separatedPolynomialMass S p1 R ≤
      4 * _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError S p1 p2 R false +
      2 * _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError S p1 p2 R true +
      (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) := by
  have h := separatedPolynomialMass_le_three_masses S p1 R
  have hN := _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarNonlinearMass_le_ordered_error S p1 p2 hopposite R hR
  have hX := _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarWrongVariableMass_le_ordered_error S p1 p2 hopposite R hR true
  have hZ := _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarWrongVariableMass_le_ordered_error S p1 p2 hopposite R hR false
  refine h.trans ((add_le_add (add_le_add hN hZ) hX).trans_eq ?_)
  push_cast
  ring










end ExtendedLineGame

end

end MIPStarRE.QPBT

/-!
# Wrong-variable mass of rounded polynomial outcomes

The two block orders use the actual projected state vectors and the full
ordered-error sum. A common exceptional coefficient controls all outcomes
of the fixed-block measurement before their weights are summed.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1328-1368`,
`eq:qld-g-separable`, `eq:qld-g-48`, `eq:qld-g-2`, and the two wrong-variable
mass bounds. This supports blueprint `lem:qld-4-7`; it does not establish
the subsequent retained overlaps or global polynomial-pair witness.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus MIPStarRE.QPBT.PolynomialImageBounds



open MIPStarRE.QPBT.ExtendedLineGame

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε δQ δL : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
        (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ) (_lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness S points δL),
      let delta := _root_.MIPStarRE.QPBT.deltaLd _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower
        (_root_.MIPStarRE.QPBT.directPassingErrorEnvelope (δQ + δL) ((P.m * P.d : ℝ) / P.q))
        P.q (2 * P.m + 2) P.d 1
      let eta := delta + Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) +
        2 * Real.sqrt (2 * delta)
      ∃ RA : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace .alice),
      ∃ RB : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace .bob),
        _root_.MIPStarRE.QPBT.Measurement.IsProjective RA ∧ _root_.MIPStarRE.QPBT.Measurement.IsProjective RB ∧
        (∀ reverse : Bool,
          _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError S .AA' .BA'' RA reverse ≤ 4 * eta + 8 * δQ ∧
          _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError S .BB' .AB'' RB reverse ≤ 4 * eta + 8 * δQ) ∧
        _root_.MIPStarRE.QPBT.ExtendedLineGame.separatedPolynomialMass S .AA' RA ≤ 6 * (4 * eta + 8 * δQ) +
          (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) ∧
        _root_.MIPStarRE.QPBT.ExtendedLineGame.separatedPolynomialMass S .BB' RB ≤ 6 * (4 * eta + 8 * δQ) +
          (((12 * P.m * P.d + 4 * P.d + 10 : ℕ) : ℝ) / P.q) := by
  let a := _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant
  let b := _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower
  have h := _root_.MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_ordered_estimates_explicit
  intro P ε δQ δL S points lines delta eta
  obtain ⟨RA, RB, hRA, hRB, horder⟩ := h P ε δQ δL S points lines
  refine ⟨RA, RB, hRA, hRB, horder, ?_, ?_⟩
  · have hA := _root_.MIPStarRE.QPBT.ExtendedLineGame.separatedPolynomialMass_le_ordered_errors S .AA' .BA'' (by trivial) RA hRA
    have h0 := (horder false).1
    have h1 := (horder true).1
    linarith
  · have hB := _root_.MIPStarRE.QPBT.ExtendedLineGame.separatedPolynomialMass_le_ordered_errors S .BB' .AB'' (by trivial) RB hRB
    have h0 := (horder false).2
    have h1 := (horder true).2
    linarith
