-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_direct_passing_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:28:22.886918+00:00
-- url     : https://prove2.me/submissions/7a6ba2f5-83c6-4a44-ace5-f8d4f3c0939f

-- Generated proof for MIPStarRE.QPBT.exists_direct_passing_polynomial_bound.
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
import Definitions.Def_QPBT_QPBT_Combining_PassingError
import Definitions.Def_QPBT_QPBT_Games_ErrorFunctions
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Absorbing both errors of the directly indexed game

The conversion from combined measurements to a low-degree strategy has passing
error `3 * (sqrt (deltaQ + deltaL) + m * d / q)`. This module bounds its cap by
one while retaining the point error and the dimension factor in the line error.
It then absorbs low-degree soundness at that capped error into `deltaQld`.
These scalar estimates do not construct either measurement witness.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288,1402`
* Blueprint `lem:qld-4-7`
-/



open MIPStarRE.QPBT

theorem solution (pointError : ℝ → ℝ)
    (hpoint : _root_.MIPStarRE.QPBT.IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : _root_.MIPStarRE.QPBT.IsPolyErr₂ lineError) (C : ℝ) (hC : 0 ≤ C) :
    ∃ passingError : ℝ → ℝ → ℝ, _root_.MIPStarRE.QPBT.IsPolyErr₂ passingError ∧
      ∀ error ratio dimension : ℝ, 0 ≤ error → 0 ≤ ratio → 1 ≤ dimension →
        min 1 (_root_.MIPStarRE.QPBT.directPassingErrorEnvelope
          (pointError error + C * dimension * lineError error ratio) ratio) ≤
            dimension * passingError error ratio := by
  obtain ⟨A, p, hA, hp, hpoint⟩ := hpoint
  obtain ⟨B, r, s, hB, hr, hs, hline⟩ := hline
  let t := min p r
  let u := min s 2
  let K := A + C * B
  let D := 3 * (Real.sqrt K + 1) + 1
  have ht : 0 < t := lt_min hp hr
  have hu : 0 < u := lt_min hs (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [Real.sqrt_nonneg K]
  refine ⟨fun error ratio => D * (error ^ (t / 2) + ratio ^ (u / 2)),
    ⟨D, t / 2, u / 2, hD, by positivity, by positivity, ?_⟩, ?_⟩
  · intro error ratio herror hratio
    exact ⟨by positivity, le_rfl⟩
  intro error ratio dimension herror hratio hdimension
  have hdim : 0 ≤ dimension := by linarith
  have he : 0 ≤ error ^ (t / 2) := Real.rpow_nonneg herror _
  have hy : 0 ≤ ratio ^ (u / 2) := Real.rpow_nonneg hratio _
  have hlarge (h : 1 ≤ error ^ (t / 2) + ratio ^ (u / 2)) :
      min 1 (_root_.MIPStarRE.QPBT.directPassingErrorEnvelope
        (pointError error + C * dimension * lineError error ratio) ratio) ≤
          dimension * (D * (error ^ (t / 2) + ratio ^ (u / 2))) := by
    refine (min_le_left _ _).trans ?_
    exact one_le_mul_of_one_le_of_one_le hdimension
      (one_le_mul_of_one_le_of_one_le hD h)
  by_cases herrorOne : error ≤ 1
  · by_cases hratioOne : ratio ≤ 1
    · have hpointBound : pointError error ≤ A * error ^ t :=
        (hpoint error herror).2.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne ht.le
            (min_le_left _ _)) (by linarith))
      have hlineBound : lineError error ratio ≤ B * (error ^ t + ratio ^ u) :=
        (hline error ratio herror hratio).2.trans (mul_le_mul_of_nonneg_left
          (add_le_add
            (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne ht.le
              (min_le_right _ _))
            (Real.rpow_le_rpow_of_exponent_ge' hratio hratioOne hu.le
              (min_le_left _ _))) (by linarith))
      have heFull : 0 ≤ error ^ t := Real.rpow_nonneg herror _
      have hyFull : 0 ≤ ratio ^ u := Real.rpow_nonneg hratio _
      have hsum : pointError error + C * dimension * lineError error ratio ≤
          dimension * K * (error ^ t + ratio ^ u) := by
        have hpDim : A * error ^ t ≤ dimension * (A * error ^ t) :=
          le_mul_of_one_le_left (by positivity) hdimension
        have hlDim := mul_le_mul_of_nonneg_left hlineBound
          (mul_nonneg hC hdim)
        dsimp [K]
        nlinarith [mul_nonneg (mul_nonneg hdim (by linarith : 0 ≤ A)) hyFull]
      have heSq : (error ^ (t / 2)) ^ (2 : ℕ) = error ^ t := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul herror]
        congr 1
        ring
      have hySq : (ratio ^ (u / 2)) ^ (2 : ℕ) = ratio ^ u := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hratio]
        congr 1
        ring
      have hrootSum : Real.sqrt (error ^ t + ratio ^ u) ≤
          error ^ (t / 2) + ratio ^ (u / 2) := by
        apply (Real.sqrt_le_left (add_nonneg he hy)).mpr
        nlinarith [mul_nonneg he hy]
      have hrootDim : Real.sqrt dimension ≤ dimension := by
        apply (Real.sqrt_le_left hdim).mpr
        nlinarith
      have hroot : Real.sqrt
          (pointError error + C * dimension * lineError error ratio) ≤
          dimension * Real.sqrt K * (error ^ (t / 2) + ratio ^ (u / 2)) := by
        calc
          _ ≤ Real.sqrt (dimension * K * (error ^ t + ratio ^ u)) :=
            Real.sqrt_le_sqrt hsum
          _ = Real.sqrt dimension * Real.sqrt K *
              Real.sqrt (error ^ t + ratio ^ u) := by
            rw [Real.sqrt_mul (mul_nonneg hdim hK), Real.sqrt_mul hdim]
          _ ≤ _ := mul_le_mul
            (mul_le_mul_of_nonneg_right hrootDim (Real.sqrt_nonneg K)) hrootSum
            (Real.sqrt_nonneg _) (mul_nonneg hdim (Real.sqrt_nonneg K))
      have hratioSmall : ratio ≤ ratio ^ (u / 2) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' hratio hratioOne
          (by positivity : 0 ≤ u / 2) (by
            have : u ≤ 2 := min_le_right _ _
            linarith : u / 2 ≤ 1)
      have hratioDim : ratio ≤ dimension * ratio ^ (u / 2) :=
        hratioSmall.trans (le_mul_of_one_le_left hy hdimension)
      refine (min_le_right _ _).trans ?_
      dsimp [_root_.MIPStarRE.QPBT.directPassingErrorEnvelope, D]
      nlinarith [mul_nonneg hdim he, mul_nonneg hdim hy]
    · exact hlarge (by
        have := Real.one_le_rpow (le_of_not_ge hratioOne) (by positivity : 0 ≤ u / 2)
        linarith)
  · exact hlarge (by
      have := Real.one_le_rpow (le_of_not_ge herrorOne) (by positivity : 0 ≤ t / 2)
      linarith)
