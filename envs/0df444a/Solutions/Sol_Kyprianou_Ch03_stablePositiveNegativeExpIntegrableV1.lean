-- Prove2me | solution 1 for Kyprianou.Ch03.stablePositiveNegativeExpIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:45.543626+00:00
-- url     : https://prove2.me/submissions/412061e6-4550-4d0b-8955-7b5122b53d01

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch03_exponentialMomentsIffLargeJumpIntegral
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
open Kyprianou.Ch03
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (T : LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha c : ℝ) (hAlpha : 0 < alpha ∧ alpha < 2)
    (hC : 0 < c) (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure = temperedStablePositiveMeasure c alpha 0)
    (hStable : ∀ (t : NNReal) (scale : ℝ), 0 < scale →
      P.map (X (t * Real.toNNReal scale)) =
        P.map (fun omega => scale ^ (1 / alpha) * X t omega))
    (theta : ℝ) (htheta : 0 ≤ theta) :
    ∀ t : NNReal, Integrable (fun w => Real.exp (-theta * X t w)) P := by
  apply (Kyprianou.Ch03.exponentialMomentsIffLargeJumpIntegral P X hX T hLK (-theta)).mpr
  let S : Set ℝ := {x | 1 ≤ |x|}
  letI : IsFiniteMeasure (T.levyMeasure.restrict S) := by
    apply isFiniteMeasure_restrict.mpr
    have hf : Measurable (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))) := by fun_prop
    have hsub : S ⊆ {x : ℝ | 1 ≤ ENNReal.ofReal (min 1 (x ^ 2))} := by
      intro x hx
      change 1 ≤ |x| at hx
      have hx2 : 1 ≤ x ^ 2 := by
        have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx 2
        simpa only [one_pow, sq_abs] using hh
      change 1 ≤ ENNReal.ofReal (min 1 (x ^ 2))
      simp [min_eq_left hx2]
    have h := mul_meas_ge_le_lintegral hf 1 (μ := T.levyMeasure)
    rw [one_mul] at h
    exact ne_top_of_le_ne_top T.levyMeasure_isLevyMeasure.2.ne
      ((measure_mono hsub).trans h)
  have hneg : T.levyMeasure (Iio 0) = 0 := by
    rw [hMeasure, temperedStablePositiveMeasure, withDensity_apply _ measurableSet_Iio]
    calc
      _ = ∫⁻ x in Iio (0 : ℝ), (0 : ENNReal) := by
        apply setLIntegral_congr_fun measurableSet_Iio
        intro x hx
        have hx' : ¬ 0 < x := not_lt_of_ge (le_of_lt hx)
        simp [hx']
      _ = 0 := by simp
  have hnon : ∀ᵐ x ∂T.levyMeasure.restrict S, 0 ≤ x := by
    rw [ae_iff]
    change (T.levyMeasure.restrict S) {x | ¬0 ≤ x} = 0
    simp only [not_le]
    have hle : T.levyMeasure.restrict S ≤ T.levyMeasure := Measure.restrict_le_self
    exact le_antisymm ((hle (Iio 0)).trans_eq hneg) bot_le
  change Integrable (fun x : ℝ => Real.exp (-theta * x)) (T.levyMeasure.restrict S)
  apply (integrable_const (1 : ℝ)).mono (by fun_prop)
  filter_upwards [hnon] with x hx
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_one]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta) hx)
