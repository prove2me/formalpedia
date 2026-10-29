-- Prove2me | solution 1 for MIPStarRE.QPBT.sqrt_deficit_bound_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:28:23.034725+00:00
-- url     : https://prove2.me/submissions/3fddddbb-9261-4adb-ab66-3a2b5b329317

-- Generated proof for MIPStarRE.QPBT.sqrt_deficit_bound_le.
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
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # Scalar error bounds for combining polynomial measurements

This module proves the formalization-only scalar estimates used by the combining
argument: nonnegativity of the real fourth root, the quarter-power form of a
square root of two deficit terms, polynomial bounds after conditioning,
composition with the dimension factor retained, and absorption into the global
polynomial-pair error scale. The estimates quantify over error functions and
numerical parameters; they do not construct measurements, and none of them is
specific to Claims 17-1 through 17-3.

## References

The auxiliary blueprint statements are `thm:qld-conditioned-polynomial-bound`,
`thm:qld-combining-polynomial-bound`, and `thm:qld-global-pair-error-bound` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`. They support the calculations
in `lem:qld-xz-lines`, `lem:qld-4-13`, and `lem:qld-4-7` of
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963,1134-1246`
and `:1278-1288,1402`. The corrected error notation and the retained dimension
factor are documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/



open MIPStarRE.QPBT

theorem solution (m δP δQ : ℝ) (hm : 1 ≤ m) (hP : 0 ≤ δP)
    (hQ : 0 ≤ δQ) :
    Real.sqrt (2 * Real.sqrt (4 * m ^ 2 * δP) + 2 * Real.sqrt (4 * δQ)) ≤
      2 * Real.sqrt m * (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ)) := by
  have hm0 : 0 ≤ m := by linarith
  have hsqrtm : 1 ≤ Real.sqrt m := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hm
  have h1 : Real.sqrt (4 * m ^ 2 * δP) = 2 * m * Real.sqrt δP := by
    rw [Real.sqrt_mul (by positivity), show (4 * m ^ 2 : ℝ) = (2 * m) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
  have h2 : Real.sqrt (4 * δQ) = 2 * Real.sqrt δQ := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hquarter : ∀ x : ℝ, 0 ≤ x →
      Real.sqrt (Real.sqrt x) = Real.rpow x (1 / 4 : ℝ) := by
    intro x hx
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    norm_num
  have hsplit : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a,
      Real.sqrt_nonneg b]
  have hPa : 0 ≤ 2 * (2 * m * Real.sqrt δP) :=
    mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (by norm_num) hm0) (Real.sqrt_nonneg _))
  have hQa : 0 ≤ 2 * (2 * Real.sqrt δQ) :=
    mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hPb : Real.sqrt (2 * (2 * m * Real.sqrt δP)) =
      2 * Real.sqrt m * Real.rpow δP (1 / 4 : ℝ) := by
    rw [show 2 * (2 * m * Real.sqrt δP) = 2 ^ 2 * m * Real.sqrt δP by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), hquarter δP hP]
  have hQb : Real.sqrt (2 * (2 * Real.sqrt δQ)) = 2 * Real.rpow δQ (1 / 4 : ℝ) := by
    rw [show 2 * (2 * Real.sqrt δQ) = 2 ^ 2 * Real.sqrt δQ by ring,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), hquarter δQ hQ]
  rw [h1, h2]
  calc
    Real.sqrt (2 * (2 * m * Real.sqrt δP) + 2 * (2 * Real.sqrt δQ))
        ≤ Real.sqrt (2 * (2 * m * Real.sqrt δP)) +
          Real.sqrt (2 * (2 * Real.sqrt δQ)) := hsplit _ _ hPa hQa
    _ = 2 * Real.sqrt m * Real.rpow δP (1 / 4 : ℝ) +
          2 * Real.rpow δQ (1 / 4 : ℝ) := by rw [hPb, hQb]
    _ ≤ 2 * Real.sqrt m *
          (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ)) := by
      have hQ4 : 0 ≤ Real.rpow δQ (1 / 4 : ℝ) := Real.rpow_nonneg hQ _
      nlinarith [hsqrtm, hQ4]
