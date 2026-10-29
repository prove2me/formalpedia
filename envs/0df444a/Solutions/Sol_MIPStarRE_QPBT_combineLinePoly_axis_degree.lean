-- Prove2me | solution 1 for MIPStarRE.QPBT.combineLinePoly_axis_degree
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:47:23.277976+00:00
-- url     : https://prove2.me/submissions/f12b704d-b450-4234-86fc-8f9f76571f46

-- Generated proof for MIPStarRE.QPBT.combineLinePoly_axis_degree.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

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

































/-- Coefficient support bounds the degree of the represented polynomial. -/
private theorem linePolynomial_natDegree_le_of_coefficients {Scalar : Type*}
    [Field Scalar] {bound degree : ℕ} (polynomial : Fin (bound + 1) → Scalar)
    (hdegree : ∀ index, degree < index.val → polynomial index = 0) :
    (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients polynomial).natDegree ≤ degree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro index _
  by_cases hindex : index.val ≤ degree
  · refine Polynomial.natDegree_mul_le.trans ?_
    have hpower := Polynomial.natDegree_pow_le
      (p := (Polynomial.X : Polynomial Scalar)) (n := index.val)
    simp only [Polynomial.natDegree_X, Nat.mul_one] at hpower
    simpa using hpower.trans hindex
  · simp [hdegree index (Nat.lt_of_not_ge hindex)]

/-- Affine substitution preserves a degree bound. -/
private theorem affine_comp_natDegree_le {Scalar : Type*} [Field Scalar]
    (polynomial : Polynomial Scalar) (offset slope : Scalar) {degree : ℕ}
    (hdegree : polynomial.natDegree ≤ degree) :
    (polynomial.comp (Polynomial.C offset + Polynomial.C slope * Polynomial.X)).natDegree ≤
      degree := by
  have haffine : (Polynomial.C offset + Polynomial.C slope * Polynomial.X).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  exact Polynomial.natDegree_comp_le.trans (by simpa using Nat.mul_le_mul hdegree haffine)














end

end MIPStarRE.QPBT

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



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

theorem solution {Scalar : Type*} [Field Scalar] {bound degree : ℕ}
    (hdegree : 1 ≤ degree) (data : Fin 8 → Scalar)
    (polynomialX polynomialZ : Fin (bound + 1) → Scalar)
    (hdegreeX : ∀ index, degree < index.val → polynomialX index = 0)
    (hdegreeZ : ∀ index, degree < index.val → polynomialZ index = 0)
    (haxis : (data 5 = 0 ∧ data 7 = 0) ∨ (data 1 = 0 ∧ data 3 = 0)) :
    ∀ index : Fin (bound + 1 + 1), degree < index.val →
      _root_.MIPStarRE.QPBT.combineLinePoly (data 0) (data 1) (data 2) (data 3)
        (data 4) (data 5) (data 6) (data 7) polynomialX polynomialZ index = 0 := by
  have hpolyX := linePolynomial_natDegree_le_of_coefficients polynomialX hdegreeX
  have hpolyZ := linePolynomial_natDegree_le_of_coefficients polynomialZ hdegreeZ
  have htotal : (_root_.MIPStarRE.QPBT.combineLinePolynomial (data 0) (data 1) (data 2) (data 3)
      (data 4) (data 5) (data 6) (data 7) polynomialX polynomialZ).natDegree ≤ degree := by
    unfold _root_.MIPStarRE.QPBT.combineLinePolynomial
    rcases haxis with ⟨halpha, hbeta⟩ | ⟨hparamX, hparamZ⟩
    · simp only [halpha, hbeta, Polynomial.C_0, zero_mul, add_zero]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine Polynomial.natDegree_mul_le.trans ?_
        simpa only [Polynomial.natDegree_C, Nat.zero_add] using
          (affine_comp_natDegree_le _ (data 0) (data 1) hpolyX)
      · refine Polynomial.natDegree_mul_le.trans ?_
        simpa only [Polynomial.natDegree_C, Nat.zero_add] using
          (affine_comp_natDegree_le _ (data 2) (data 3) hpolyZ)
    · simp only [hparamX, hparamZ, Polynomial.C_0, zero_mul, add_zero, Polynomial.comp_C]
      have hterm (constant slope value : Scalar) :
          ((Polynomial.C constant + Polynomial.C slope * Polynomial.X) *
            Polynomial.C value).natDegree ≤ degree := by
        refine Polynomial.natDegree_mul_le.trans ?_
        simp only [Polynomial.natDegree_C, Nat.add_zero]
        exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
          (Polynomial.natDegree_mul_le.trans (by simpa using hdegree)))
      exact (Polynomial.natDegree_add_le _ _).trans (max_le (hterm _ _ _) (hterm _ _ _))
  intro index hindex
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (htotal.trans_lt hindex)
