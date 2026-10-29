-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_combining_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:32:45.542138+00:00
-- url     : https://prove2.me/submissions/83138813-459a-41b0-906d-6344271168b3

-- Generated proof for MIPStarRE.QPBT.exists_combining_polynomial_bound.
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
import Definitions.Def_QPBT_QPBT_Games_ErrorFunctions
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

theorem solution (pointError : ℝ → ℝ)
    (hpoint : _root_.MIPStarRE.QPBT.IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : _root_.MIPStarRE.QPBT.IsPolyErr₂ lineError) (constant : ℝ) (hconstant : 0 ≤ constant) :
    ∃ combinedError : ℝ → ℝ → ℝ, _root_.MIPStarRE.QPBT.IsPolyErr₂ combinedError ∧
      ∀ error ratio dimension : ℝ, 0 ≤ error → 0 ≤ ratio → 1 ≤ dimension →
        min 1 (constant * ((pointError error) ^ (1 / 2 : ℝ) + Real.sqrt dimension *
          ((lineError error ratio) ^ (1 / 4 : ℝ) + (pointError error) ^ (1 / 4 : ℝ) +
            error ^ (1 / 4 : ℝ)))) ≤ dimension * combinedError error ratio := by
  obtain ⟨pointConstant, pointPower, hpointConstant, hpointPower, hpointBound⟩ := hpoint
  obtain ⟨lineConstant, errorPower, ratioPower, hlineConstant,
    herrorPower, hratioPower, hlineBound⟩ := hline
  let finalPower := min (pointPower / 4) (min (errorPower / 4) (1 / 4 : ℝ))
  let coefficient := pointConstant ^ (1 / 2 : ℝ) + lineConstant ^ (1 / 4 : ℝ) +
    pointConstant ^ (1 / 4 : ℝ) + 1
  let finalConstant := 1 + constant * coefficient
  have hfinalPower : 0 < finalPower := by dsimp [finalPower]; positivity
  have hcoefficient : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have hfinalConstant : 1 ≤ finalConstant := by
    dsimp [finalConstant]
    linarith [mul_nonneg hconstant hcoefficient]
  refine ⟨fun error ratio => finalConstant *
    (error ^ finalPower + ratio ^ (ratioPower / 4)),
    ⟨finalConstant, finalPower, ratioPower / 4, hfinalConstant, hfinalPower,
      by positivity, ?_⟩, ?_⟩
  · intro error ratio herror hratio
    exact ⟨mul_nonneg (by linarith) (add_nonneg (Real.rpow_nonneg herror _)
      (Real.rpow_nonneg hratio _)), le_rfl⟩
  intro error ratio dimension herror hratio hdimension
  have hdimensionNonneg : 0 ≤ dimension := by linarith
  have herrorTerm : 0 ≤ error ^ finalPower := Real.rpow_nonneg herror _
  have hratioTerm : 0 ≤ ratio ^ (ratioPower / 4) := Real.rpow_nonneg hratio _
  by_cases herrorOne : error ≤ 1
  · have hpointValue := hpointBound error herror
    have hlineValue := hlineBound error ratio herror hratio
    have hpointRoot (power : ℝ) (hpower : 0 ≤ power)
        (hsmall : finalPower ≤ pointPower * power) :
        (pointError error) ^ power ≤ pointConstant ^ power * error ^ finalPower := by
      calc
        _ ≤ (pointConstant * error ^ pointPower) ^ power :=
          Real.rpow_le_rpow hpointValue.1 hpointValue.2 hpower
        _ = pointConstant ^ power * error ^ (pointPower * power) := by
          rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg herror _),
            ← Real.rpow_mul herror]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le hsmall)
          (Real.rpow_nonneg (by linarith) _)
    have hpointQuarter := hpointRoot (1 / 4) (by norm_num)
      (by
        have := min_le_left (pointPower / 4) (min (errorPower / 4) (1 / 4 : ℝ))
        dsimp [finalPower]
        linarith)
    have hpointHalf := hpointRoot (1 / 2) (by norm_num)
      (by
        have := min_le_left (pointPower / 4) (min (errorPower / 4) (1 / 4 : ℝ))
        dsimp [finalPower]
        linarith)
    have hlineQuarter : (lineError error ratio) ^ (1 / 4 : ℝ) ≤
        lineConstant ^ (1 / 4 : ℝ) * (error ^ finalPower + ratio ^ (ratioPower / 4)) := by
      calc
        _ ≤ (lineConstant * (error ^ errorPower + ratio ^ ratioPower)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hlineValue.1 hlineValue.2 (by norm_num)
        _ = lineConstant ^ (1 / 4 : ℝ) *
            (error ^ errorPower + ratio ^ ratioPower) ^ (1 / 4 : ℝ) := by
          rw [Real.mul_rpow (by linarith) (by positivity)]
        _ ≤ lineConstant ^ (1 / 4 : ℝ) *
            ((error ^ errorPower) ^ (1 / 4 : ℝ) +
              (ratio ^ ratioPower) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_add_le_add_rpow (Real.rpow_nonneg herror _)
              (Real.rpow_nonneg hratio _) (by norm_num) (by norm_num))
            (Real.rpow_nonneg (by linarith) _)
        _ ≤ _ := by
          rw [← Real.rpow_mul herror, ← Real.rpow_mul hratio]
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
          apply add_le_add _ (by simp [div_eq_mul_inv])
          apply Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le
          have hsmall : finalPower ≤ errorPower / 4 :=
            (min_le_right _ _).trans (min_le_left _ _)
          linarith
    have herrorQuarter : error ^ (1 / 4 : ℝ) ≤ error ^ finalPower :=
      Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le
        ((min_le_right _ _).trans (min_le_right _ _))
    have hsqrt : Real.sqrt dimension ≤ dimension := by
      nlinarith [Real.sq_sqrt hdimensionNonneg, Real.sqrt_nonneg dimension]
    have hsum : (pointError error) ^ (1 / 2 : ℝ) + Real.sqrt dimension *
        ((lineError error ratio) ^ (1 / 4 : ℝ) + (pointError error) ^ (1 / 4 : ℝ) +
          error ^ (1 / 4 : ℝ)) ≤
        dimension * (coefficient * (error ^ finalPower + ratio ^ (ratioPower / 4))) := by
      have hrootNonneg : 0 ≤ (lineError error ratio) ^ (1 / 4 : ℝ) +
          (pointError error) ^ (1 / 4 : ℝ) + error ^ (1 / 4 : ℝ) :=
        add_nonneg (add_nonneg (Real.rpow_nonneg hlineValue.1 _)
          (Real.rpow_nonneg hpointValue.1 _)) (Real.rpow_nonneg herror _)
      have hrootSum := add_le_add (add_le_add hlineQuarter hpointQuarter) herrorQuarter
      have hscaled := mul_le_mul hsqrt hrootSum hrootNonneg hdimensionNonneg
      have hpointScaled := mul_le_mul_of_nonneg_right hdimension
        (Real.rpow_nonneg hpointValue.1 (1 / 2 : ℝ))
      dsimp [coefficient]
      nlinarith [mul_nonneg hdimensionNonneg
        (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ pointConstant) (1 / 2 : ℝ))
          hratioTerm),
        mul_nonneg hdimensionNonneg
          (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ pointConstant) (1 / 4 : ℝ))
            hratioTerm),
        mul_le_mul_of_nonneg_left hpointHalf hdimensionNonneg,
        mul_nonneg hdimensionNonneg hratioTerm]
    refine (min_le_right _ _).trans ((mul_le_mul_of_nonneg_left hsum hconstant).trans ?_)
    dsimp [finalConstant]
    nlinarith [mul_nonneg hdimensionNonneg (add_nonneg herrorTerm hratioTerm)]
  · refine (min_le_left _ _).trans ?_
    have hone := Real.one_le_rpow (le_of_not_ge herrorOne) hfinalPower.le
    have hsumOne : 1 ≤ finalConstant * (error ^ finalPower + ratio ^ (ratioPower / 4)) := by
      nlinarith [mul_nonneg (show 0 ≤ finalConstant - 1 by linarith)
        (add_nonneg herrorTerm hratioTerm)]
    nlinarith [mul_nonneg (show 0 ≤ dimension - 1 by linarith)
      (show 0 ≤ finalConstant * (error ^ finalPower + ratio ^ (ratioPower / 4)) by linarith)]
