-- Prove2me | solution 1 for MIPStarRE.QPBT.global_pair_error_bound_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:32:45.535455+00:00
-- url     : https://prove2.me/submissions/84f77304-07ce-4c83-b220-5946a80454db

-- Generated proof for MIPStarRE.QPBT.global_pair_error_bound_explicit.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_ErrorBounds
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
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

set_option maxHeartbeats 800000 in
-- Normalizing the nested real-power envelope leaves a large nonlinear scalar goal.

theorem solution (pointError : ℝ → ℝ)
    (pointConstant pointPower : ℝ) (hpointConstant : 1 ≤ pointConstant)
    (hpointPower : 0 < pointPower)
    (hpointBound : ∀ error : ℝ, 0 ≤ error →
      0 ≤ pointError error ∧ pointError error ≤ pointConstant * error ^ pointPower)
    (combinedError : ℝ → ℝ → ℝ) (lineConstant errorPower ratioPower : ℝ)
    (hlineConstant : 1 ≤ lineConstant) (herrorPower : 0 < errorPower)
    (hratioPower : 0 < ratioPower)
    (hlineBound : ∀ error ratio : ℝ, 0 ≤ error → 0 ≤ ratio →
      0 ≤ combinedError error ratio ∧ combinedError error ratio ≤
        lineConstant * (error ^ errorPower + ratio ^ ratioPower))
    (combineConstant soundnessConstant soundnessPower finalScale : ℝ)
    (hcombineConstant : 0 ≤ combineConstant) (hsoundnessConstant : 1 ≤ soundnessConstant)
    (hsoundnessPower : 0 < soundnessPower) (hsoundnessPowerOne : soundnessPower ≤ 1)
    (hfinalScale : 0 ≤ finalScale) :
    1 < _root_.MIPStarRE.QPBT.globalPairBoundConstant pointConstant lineConstant combineConstant
          soundnessConstant soundnessPower ratioPower finalScale ∧
      0 < _root_.MIPStarRE.QPBT.globalPairBoundPower pointPower errorPower ratioPower soundnessPower ∧
      _root_.MIPStarRE.QPBT.globalPairBoundPower pointPower errorPower ratioPower soundnessPower < 1 ∧
      ∀ (params : _root_.MIPStarRE.QPBT.AdmissibleParams) (error : ℝ), 0 ≤ error →
        min 1 (finalScale *
          (_root_.MIPStarRE.QPBT.deltaLd soundnessConstant soundnessPower
              (combineConstant * (params.m : ℝ) *
                combinedError error ((params.m * params.d : ℕ) / (params.q : ℝ)) + error)
              params.q (2 * params.m + 2) params.d 1 +
            Real.sqrt (pointError error) + ((params.m * params.d : ℕ) / (params.q : ℝ)))) ≤
          _root_.MIPStarRE.QPBT.deltaQld
            (_root_.MIPStarRE.QPBT.globalPairBoundConstant pointConstant lineConstant combineConstant
              soundnessConstant soundnessPower ratioPower finalScale)
            (_root_.MIPStarRE.QPBT.globalPairBoundPower pointPower errorPower ratioPower soundnessPower)
            error params.m params.d params.q := by
  let finalPower := _root_.MIPStarRE.QPBT.globalPairBoundPower pointPower errorPower ratioPower soundnessPower
  have hfinalPower : 0 < finalPower := by
    dsimp [finalPower, _root_.MIPStarRE.QPBT.globalPairBoundPower]
    positivity
  have hhalf : finalPower ≤ 1 / 2 := by
    dsimp [finalPower, _root_.MIPStarRE.QPBT.globalPairBoundPower]
    exact min_le_left _ _
  have hpower : finalPower ≤ soundnessPower := by
    dsimp [finalPower, _root_.MIPStarRE.QPBT.globalPairBoundPower]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have herrorExponent : finalPower ≤ errorPower * soundnessPower := by
    dsimp [finalPower, _root_.MIPStarRE.QPBT.globalPairBoundPower]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hratioExponent : finalPower ≤ ratioPower * soundnessPower := by
    dsimp [finalPower, _root_.MIPStarRE.QPBT.globalPairBoundPower]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hpointExponent : finalPower ≤ pointPower / 2 := by
    dsimp [finalPower, _root_.MIPStarRE.QPBT.globalPairBoundPower]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  let lineGrowth := soundnessPower + ratioPower * soundnessPower
  let growth := soundnessConstant + lineGrowth + 1
  let lineCoefficient := soundnessConstant * (4 : ℝ) ^ soundnessConstant *
    ((combineConstant * lineConstant) ^ soundnessPower + 2)
  let coefficient := finalScale * (lineCoefficient + Real.sqrt pointConstant + 1)
  let finalConstant := coefficient + growth + 2
  change 1 < finalConstant ∧ 0 < finalPower ∧ finalPower < 1 ∧
    ∀ (params : _root_.MIPStarRE.QPBT.AdmissibleParams) (error : ℝ), 0 ≤ error →
      min 1 (finalScale *
        (_root_.MIPStarRE.QPBT.deltaLd soundnessConstant soundnessPower
            (combineConstant * (params.m : ℝ) *
              combinedError error ((params.m * params.d : ℕ) / (params.q : ℝ)) + error)
            params.q (2 * params.m + 2) params.d 1 +
          Real.sqrt (pointError error) + ((params.m * params.d : ℕ) / (params.q : ℝ)))) ≤
        _root_.MIPStarRE.QPBT.deltaQld finalConstant finalPower error params.m params.d params.q
  have hlineGrowth : 0 ≤ lineGrowth := by dsimp [lineGrowth]; positivity
  have hgrowth : 1 ≤ growth := by dsimp [growth]; linarith
  have hlineCoefficient : 0 ≤ lineCoefficient := by dsimp [lineCoefficient]; positivity
  have hcoefficient : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have hfinalConstant : 1 < finalConstant := by dsimp [finalConstant]; linarith
  have hcoefficient_le : coefficient ≤ finalConstant := by dsimp [finalConstant]; linarith
  have hgrowth_le : growth ≤ finalConstant := by dsimp [finalConstant]; linarith
  refine ⟨hfinalConstant, hfinalPower, by linarith, ?_⟩
  intro params error herror
  let size : ℝ := ((params.m * params.d : ℕ) : ℝ)
  let extendedSize : ℝ := (((2 * params.m + 2) * params.d : ℕ) : ℝ)
  let ratio : ℝ := size / (params.q : ℝ)
  let envelope := error ^ finalPower + (params.q : ℝ) ^ (-finalPower) +
    (2 : ℝ) ^ (-(finalPower * size))
  have hm : (1 : ℝ) ≤ (params.m : ℝ) := by exact_mod_cast params.one_le_m
  have hd : (1 : ℝ) ≤ (params.d : ℝ) := by exact_mod_cast params.hd
  have hsize : 1 ≤ size := by
    dsimp [size]
    exact_mod_cast Nat.mul_pos params.one_le_m params.hd
  have hsize0 : 0 ≤ size := by linarith
  have hsizePos : 0 < size := by linarith
  have hmSize : (params.m : ℝ) ≤ size := by dsimp [size]; push_cast; nlinarith
  have hq : (1 : ℝ) ≤ (params.q : ℝ) := by
    obtain ⟨power, _, hq⟩ := params.hq
    rw [hq]
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have hq0 : 0 ≤ (params.q : ℝ) := by linarith
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
  have henv : 0 ≤ envelope := by dsimp [envelope]; positivity
  have henvError : error ^ finalPower ≤ envelope := by
    dsimp [envelope]
    linarith [Real.rpow_nonneg hq0 (-finalPower),
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(finalPower * size))]
  have henvField : (params.q : ℝ) ^ (-finalPower) ≤ envelope := by
    dsimp [envelope]
    linarith [Real.rpow_nonneg herror finalPower,
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(finalPower * size))]
  change min 1 (finalScale *
    (_root_.MIPStarRE.QPBT.deltaLd soundnessConstant soundnessPower
      (combineConstant * (params.m : ℝ) * combinedError error ratio + error)
      params.q (2 * params.m + 2) params.d 1 + Real.sqrt (pointError error) + ratio)) ≤
    finalConstant * size ^ finalConstant * envelope
  by_cases herrorOne : error ≤ 1
  · have herrorMono (power : ℝ) (hpower : finalPower ≤ power) :
        error ^ power ≤ error ^ finalPower :=
      Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le hpower
    have hfieldMono (power : ℝ) (hpower : finalPower ≤ power) :
        (params.q : ℝ) ^ (-power) ≤ (params.q : ℝ) ^ (-finalPower) :=
      Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg hpower)
    have hsizeRatio : 1 ≤ size ^ (ratioPower * soundnessPower) :=
      Real.one_le_rpow hsize (mul_nonneg hratioPower.le hsoundnessPower.le)
    have hsizeLine : 1 ≤ size ^ lineGrowth := Real.one_le_rpow hsize hlineGrowth
    have hpolySum : error ^ (errorPower * soundnessPower) +
        ratio ^ (ratioPower * soundnessPower) ≤
        size ^ (ratioPower * soundnessPower) * envelope := by
      have hratioEq : ratio ^ (ratioPower * soundnessPower) =
          size ^ (ratioPower * soundnessPower) *
            (params.q : ℝ) ^ (-(ratioPower * soundnessPower)) := by
        dsimp [ratio]
        rw [Real.div_rpow hsize0 hq0, div_eq_mul_inv, Real.rpow_neg hq0]
      rw [hratioEq]
      have hfirst := (herrorMono _ herrorExponent).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg herror _) hsizeRatio)
      have hsecond := mul_le_mul_of_nonneg_left (hfieldMono _ hratioExponent)
        (Real.rpow_nonneg hsize0 (ratioPower * soundnessPower))
      have hsum := add_le_add hfirst hsecond
      refine hsum.trans ?_
      dsimp [envelope]
      nlinarith [mul_nonneg (Real.rpow_nonneg hsize0 (ratioPower * soundnessPower))
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(finalPower * size)))]
    have hcombinedValue := hlineBound error ratio herror hratio
    have hbaseNonneg : 0 ≤
        combineConstant * (params.m : ℝ) * combinedError error ratio :=
      mul_nonneg (mul_nonneg hcombineConstant (by positivity)) hcombinedValue.1
    have hpoly : (combinedError error ratio) ^ soundnessPower ≤
        lineConstant ^ soundnessPower *
          (size ^ (ratioPower * soundnessPower) * envelope) := by
      calc
        _ ≤ (lineConstant * (error ^ errorPower + ratio ^ ratioPower)) ^ soundnessPower :=
          Real.rpow_le_rpow hcombinedValue.1 hcombinedValue.2 hsoundnessPower.le
        _ = lineConstant ^ soundnessPower *
            (error ^ errorPower + ratio ^ ratioPower) ^ soundnessPower := by
          rw [Real.mul_rpow (by linarith) (by positivity)]
        _ ≤ lineConstant ^ soundnessPower *
            (error ^ (errorPower * soundnessPower) + ratio ^ (ratioPower * soundnessPower)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) _)
          simpa only [← Real.rpow_mul herror, ← Real.rpow_mul hratio] using
            Real.rpow_add_le_add_rpow (Real.rpow_nonneg herror errorPower)
              (Real.rpow_nonneg hratio ratioPower) hsoundnessPower.le hsoundnessPowerOne
        _ ≤ _ := mul_le_mul_of_nonneg_left hpolySum (Real.rpow_nonneg (by linarith) _)
    have hproduct : (combineConstant * (params.m : ℝ) * combinedError error ratio) ^
        soundnessPower ≤ (combineConstant * lineConstant) ^ soundnessPower *
          size ^ lineGrowth * envelope := by
      rw [Real.mul_rpow (by positivity) hcombinedValue.1]
      calc
        _ ≤ (combineConstant * size) ^ soundnessPower *
            (lineConstant ^ soundnessPower *
              (size ^ (ratioPower * soundnessPower) * envelope)) :=
          mul_le_mul (Real.rpow_le_rpow (by positivity)
            (mul_le_mul_of_nonneg_left hmSize hcombineConstant) hsoundnessPower.le)
            hpoly (Real.rpow_nonneg hcombinedValue.1 _) (by positivity)
        _ = _ := by
          dsimp [lineGrowth]
          rw [Real.mul_rpow hcombineConstant hsize0,
            Real.mul_rpow hcombineConstant (by linarith), Real.rpow_add hsizePos]
          ring
    have hinput : (combineConstant * (params.m : ℝ) * combinedError error ratio + error) ^
        soundnessPower ≤ ((combineConstant * lineConstant) ^ soundnessPower + 1) *
          size ^ lineGrowth * envelope := by
      have hsplit := Real.rpow_add_le_add_rpow
        hbaseNonneg herror
        hsoundnessPower.le hsoundnessPowerOne
      have hsum := hsplit.trans (add_le_add hproduct
        ((herrorMono _ hpower).trans henvError))
      refine hsum.trans ?_
      nlinarith [mul_le_mul_of_nonneg_right hsizeLine henv]
    have hextended : size ≤ extendedSize ∧ extendedSize ≤ 4 * size := by
      dsimp [size, extendedSize]
      push_cast
      constructor <;> nlinarith
    have hextended0 : 0 ≤ extendedSize := hsize0.trans hextended.1
    have hexponential : (2 : ℝ) ^ (-(soundnessPower * extendedSize)) ≤
        (2 : ℝ) ^ (-(finalPower * size)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact neg_le_neg ((mul_le_mul_of_nonneg_right hpower hsize0).trans
        (mul_le_mul_of_nonneg_left hextended.1 hsoundnessPower.le))
    have hrest : (params.q : ℝ) ^ (-soundnessPower) +
        (2 : ℝ) ^ (-(soundnessPower * extendedSize)) ≤ envelope := by
      have hsum := add_le_add (hfieldMono _ hpower) hexponential
      dsimp [envelope]
      linarith [Real.rpow_nonneg herror finalPower]
    have hbracket :
        (combineConstant * (params.m : ℝ) * combinedError error ratio + error) ^ soundnessPower +
          (params.q : ℝ) ^ (-soundnessPower) +
          (2 : ℝ) ^ (-(soundnessPower * extendedSize)) ≤
        ((combineConstant * lineConstant) ^ soundnessPower + 2) *
          size ^ lineGrowth * envelope := by
      have hsum := add_le_add hinput hrest
      nlinarith [mul_le_mul_of_nonneg_right hsizeLine henv]
    have hprefactor : soundnessConstant * extendedSize ^ soundnessConstant ≤
        soundnessConstant * ((4 : ℝ) ^ soundnessConstant * size ^ soundnessConstant) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      calc
        _ ≤ (4 * size) ^ soundnessConstant :=
          Real.rpow_le_rpow hextended0 hextended.2 (by linarith)
        _ = _ := Real.mul_rpow (by norm_num) hsize0
    have hld : _root_.MIPStarRE.QPBT.deltaLd soundnessConstant soundnessPower
        (combineConstant * (params.m : ℝ) * combinedError error ratio + error)
        params.q (2 * params.m + 2) params.d 1 ≤
        lineCoefficient * size ^ (soundnessConstant + lineGrowth) * envelope := by
      have heq : _root_.MIPStarRE.QPBT.deltaLd soundnessConstant soundnessPower
          (combineConstant * (params.m : ℝ) * combinedError error ratio + error)
          params.q (2 * params.m + 2) params.d 1 =
          soundnessConstant * extendedSize ^ soundnessConstant *
            ((combineConstant * (params.m : ℝ) * combinedError error ratio + error) ^
              soundnessPower + (params.q : ℝ) ^ (-soundnessPower) +
              (2 : ℝ) ^ (-(soundnessPower * extendedSize))) := by
        simp only [_root_.MIPStarRE.QPBT.deltaLd, extendedSize, Nat.mul_one, Real.rpow_eq_pow,
          Nat.mul_comm params.d (2 * params.m + 2)]
      rw [heq]
      refine (mul_le_mul hprefactor hbracket (by positivity) (by positivity)).trans_eq ?_
      dsimp [lineCoefficient]
      rw [Real.rpow_add hsizePos soundnessConstant lineGrowth]
      ring
    have hroot : Real.sqrt (pointError error) ≤ Real.sqrt pointConstant * envelope := by
      calc
        _ ≤ Real.sqrt (pointConstant * error ^ pointPower) :=
          Real.sqrt_le_sqrt (hpointBound error herror).2
        _ = Real.sqrt pointConstant * error ^ (pointPower / 2) := by
          rw [Real.sqrt_mul (by linarith)]
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul herror]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((herrorMono _ hpointExponent).trans henvError) (Real.sqrt_nonneg _)
    have hratioBound : ratio ≤ size * envelope := by
      dsimp [ratio]
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_left
        ((hfieldMono 1 (by linarith)).trans henvField) hsize0
    have hsizePower : size ^ (soundnessConstant + lineGrowth) ≤ size ^ growth :=
      Real.rpow_le_rpow_of_exponent_le hsize (by dsimp [growth]; linarith)
    have hsizeGrowth : size ≤ size ^ growth := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hsize hgrowth
    have honeGrowth : 1 ≤ size ^ growth := Real.one_le_rpow hsize (by linarith)
    have hldBound := hld.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsizePower hlineCoefficient) henv)
    have hrootBound := hroot.trans (le_mul_of_one_le_left
      (mul_nonneg (Real.sqrt_nonneg _) henv) honeGrowth)
    have hratioGrowth := hratioBound.trans (mul_le_mul_of_nonneg_right hsizeGrowth henv)
    have hsum := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hldBound hrootBound) hratioGrowth) hfinalScale
    have hfinal : finalScale *
        (_root_.MIPStarRE.QPBT.deltaLd soundnessConstant soundnessPower
          (combineConstant * (params.m : ℝ) * combinedError error ratio + error)
          params.q (2 * params.m + 2) params.d 1 + Real.sqrt (pointError error) + ratio) ≤
        coefficient * size ^ growth * envelope := by
      exact hsum.trans_eq (by dsimp [coefficient]; ring)
    refine (min_le_right _ _).trans (hfinal.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hcoefficient_le
        (Real.rpow_le_rpow_of_exponent_le hsize hgrowth_le)
        (Real.rpow_nonneg hsize0 growth) (by linarith)) henv
  · have herrorLarge : 1 ≤ error := le_of_not_ge herrorOne
    have henvOne : 1 ≤ envelope :=
      (Real.one_le_rpow herrorLarge hfinalPower.le).trans henvError
    have hsizeOne : 1 ≤ size ^ finalConstant :=
      Real.one_le_rpow hsize (by linarith)
    have hprefactorOne : 1 ≤ finalConstant * size ^ finalConstant := by
      simpa only [one_mul] using mul_le_mul hfinalConstant.le hsizeOne
        (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ finalConstant)
    refine (min_le_left _ _).trans ?_
    simpa only [one_mul] using mul_le_mul hprefactorOne henvOne
      (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hprefactorOne)
