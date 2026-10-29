-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_conditioned_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:32:45.167956+00:00
-- url     : https://prove2.me/submissions/1e823c0e-eb2a-4ce9-8524-1d8c8960a58e

-- Generated proof for MIPStarRE.QPBT.exists_conditioned_polynomial_bound.
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
    (hpoint : _root_.MIPStarRE.QPBT.IsPolyErr pointError) (constant : ℝ) (hconstant : 1 ≤ constant)
    (pastingError : ℝ → ℝ → ℝ) (hpasting : _root_.MIPStarRE.QPBT.IsPolyErr₂ pastingError) :
    ∃ lineError : ℝ → ℝ → ℝ, _root_.MIPStarRE.QPBT.IsPolyErr₂ lineError ∧
      ∀ error ratio mass : ℝ, 0 ≤ error → 0 ≤ ratio →
        1 / 2 ≤ mass → mass ≤ 1 →
        min 1 (mass * pastingError ratio
          ((8 * pointError error + constant * (error + Real.sqrt error)) / mass) + ratio) ≤
          lineError error ratio := by
  obtain ⟨pointConstant, pointPower, hpointConstant, hpointPower, hpointBound⟩ := hpoint
  obtain ⟨pastingConstant, ratioPower, marginalPower, hpastingConstant,
    hratioPower, hmarginalPower, hpastingBound⟩ := hpasting
  let smallPower := min pointPower (1 / 2 : ℝ)
  let finalRatioPower := min ratioPower 1
  let marginalConstant := 8 * pointConstant + 2 * constant
  let powerConstant := (2 * marginalConstant) ^ marginalPower
  let finalConstant := pastingConstant * (1 + powerConstant) + 1
  have hsmall : 0 < smallPower := lt_min hpointPower (by norm_num)
  have hfinalRatio : 0 < finalRatioPower := lt_min hratioPower zero_lt_one
  have hmarginalConstant : 0 ≤ marginalConstant := by dsimp [marginalConstant]; linarith
  have hpowerConstant : 0 ≤ powerConstant := Real.rpow_nonneg (by positivity) _
  have hfinalConstant : 1 ≤ finalConstant := by
    dsimp [finalConstant]
    nlinarith
  refine ⟨fun error ratio => finalConstant *
    (error ^ (smallPower * marginalPower) + ratio ^ finalRatioPower),
    ⟨finalConstant, smallPower * marginalPower, finalRatioPower, hfinalConstant,
      mul_pos hsmall hmarginalPower, hfinalRatio, ?_⟩, ?_⟩
  · intro error ratio herror hratio
    exact ⟨mul_nonneg (by linarith) (add_nonneg (Real.rpow_nonneg herror _)
      (Real.rpow_nonneg hratio _)), le_rfl⟩
  intro error ratio mass herror hratio hmass hmassOne
  have hmassPos : 0 < mass := by linarith
  have herrorPower : 0 ≤ error ^ (smallPower * marginalPower) :=
    Real.rpow_nonneg herror _
  have hratioPowerNonneg : 0 ≤ ratio ^ finalRatioPower := Real.rpow_nonneg hratio _
  have hlarge (hlarge : 1 ≤ error ^ (smallPower * marginalPower) +
      ratio ^ finalRatioPower) :
      min 1 (mass * pastingError ratio
        ((8 * pointError error + constant * (error + Real.sqrt error)) / mass) + ratio) ≤
        finalConstant * (error ^ (smallPower * marginalPower) +
          ratio ^ finalRatioPower) := by
    refine (min_le_left _ _).trans ?_
    nlinarith [mul_nonneg (show 0 ≤ finalConstant - 1 by linarith)
      (add_nonneg herrorPower hratioPowerNonneg)]
  by_cases herrorOne : error ≤ 1
  · by_cases hratioOne : ratio ≤ 1
    · have hpointValue := hpointBound error herror
      have hpointSmall : pointError error ≤ pointConstant * error ^ smallPower :=
        hpointValue.2.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hsmall.le
            (min_le_left _ _)) (by linarith))
      have herrorSmall : error ≤ error ^ smallPower := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hsmall.le
          (show smallPower ≤ 1 by exact (min_le_right _ _).trans (by norm_num))
      have hsqrtSmall : Real.sqrt error ≤ error ^ smallPower := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hsmall.le
          (min_le_right _ _)
      have hmarginalNonneg : 0 ≤ 8 * pointError error +
          constant * (error + Real.sqrt error) :=
        add_nonneg (mul_nonneg (by norm_num) hpointValue.1)
          (mul_nonneg (by linarith) (add_nonneg herror (Real.sqrt_nonneg _)))
      have hmarginalSmall : 8 * pointError error +
          constant * (error + Real.sqrt error) ≤ marginalConstant * error ^ smallPower := by
        dsimp [marginalConstant]
        nlinarith [mul_le_mul_of_nonneg_left (add_le_add herrorSmall hsqrtSmall)
          (show 0 ≤ constant by linarith)]
      have hdivSmall : (8 * pointError error + constant * (error + Real.sqrt error)) /
          mass ≤ (2 * marginalConstant) * error ^ smallPower := by
        apply (div_le_iff₀ hmassPos).mpr
        exact hmarginalSmall.trans (by
          nlinarith [mul_nonneg hmarginalConstant (Real.rpow_nonneg herror smallPower),
            mul_nonneg (show 0 ≤ mass - 1 / 2 by linarith)
              (mul_nonneg hmarginalConstant (Real.rpow_nonneg herror smallPower))])
      have hdivPower : ((8 * pointError error + constant *
          (error + Real.sqrt error)) / mass) ^ marginalPower ≤
          powerConstant * error ^ (smallPower * marginalPower) := by
        calc
          _ ≤ ((2 * marginalConstant) * error ^ smallPower) ^ marginalPower :=
            Real.rpow_le_rpow (div_nonneg hmarginalNonneg hmassPos.le)
              hdivSmall hmarginalPower.le
          _ = _ := by rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg herror _),
            ← Real.rpow_mul herror]
      have hratioSmall : ratio ^ ratioPower ≤ ratio ^ finalRatioPower :=
        Real.rpow_le_rpow_of_exponent_ge' hratio hratioOne hfinalRatio.le
          (min_le_left _ _)
      have hratioLinear : ratio ≤ ratio ^ finalRatioPower := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' hratio hratioOne hfinalRatio.le
          (min_le_right _ _)
      have hpastingValue := hpastingBound ratio _ hratio
        (div_nonneg hmarginalNonneg hmassPos.le)
      refine (min_le_right _ _).trans ?_
      calc
        _ ≤ pastingError ratio
            ((8 * pointError error + constant * (error + Real.sqrt error)) / mass) +
            ratio := add_le_add (mul_le_of_le_one_left hpastingValue.1 hmassOne) le_rfl
        _ ≤ pastingConstant * (ratio ^ finalRatioPower +
            powerConstant * error ^ (smallPower * marginalPower)) +
            ratio ^ finalRatioPower :=
          add_le_add (hpastingValue.2.trans (mul_le_mul_of_nonneg_left
            (add_le_add hratioSmall hdivPower) (by linarith))) hratioLinear
        _ ≤ _ := by
          dsimp [finalConstant]
          nlinarith [mul_nonneg
            (mul_nonneg (show 0 ≤ pastingConstant by linarith) hpowerConstant)
            hratioPowerNonneg,
            mul_nonneg (show 0 ≤ pastingConstant by linarith) herrorPower]
    · apply hlarge
      linarith [Real.one_le_rpow (le_of_not_ge hratioOne) hfinalRatio.le]
  · apply hlarge
    linarith [Real.one_le_rpow (le_of_not_ge herrorOne)
      (mul_pos hsmall hmarginalPower).le]
