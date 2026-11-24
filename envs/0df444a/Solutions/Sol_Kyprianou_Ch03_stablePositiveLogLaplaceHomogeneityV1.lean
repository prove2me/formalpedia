-- Prove2me | solution 1 for Kyprianou.Ch03.stablePositiveLogLaplaceHomogeneityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:40.302445+00:00
-- url     : https://prove2.me/submissions/38495a99-9942-4dd1-b6fc-288384ca404d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_stablePositiveNegativeExpIntegrableV1
import Theorems.Thm_Kyprianou_Ch03_stableLevyLogMomentTimeScalingV1
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
    Real.log (∫ w, Real.exp (-theta * X 1 w) ∂P) =
      Real.log (∫ w, Real.exp (-X 1 w) ∂P) * theta ^ alpha := by
  rcases eq_or_lt_of_le htheta with hzero | hpos
  · rw [← hzero, Real.zero_rpow hAlpha.1.ne']
    simp
  let t : NNReal := Real.toNNReal (theta ^ alpha)
  have ht : (t : ℝ) = theta ^ alpha := Real.coe_toNNReal _ (Real.rpow_nonneg hpos.le _)
  have hp : (theta ^ alpha) ^ (1 / alpha) = theta := by
    have he : alpha * (1 / alpha) = 1 := by field_simp [hAlpha.1.ne']
    rw [← Real.rpow_mul hpos.le, he, Real.rpow_one]
  have hscale : P.map (X t) = P.map (fun w => theta * X 1 w) := by
    have hs := hStable 1 (theta ^ alpha) (Real.rpow_pos_of_pos hpos _)
    rw [one_mul, hp] at hs
    exact hs
  let f : ℝ → ℝ := fun x => Real.exp (-x)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hm (u : NNReal) : AEMeasurable (X u) P :=
    Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX u
  have he : (∫ w, Real.exp (-X t w) ∂P) = ∫ w, Real.exp (-theta * X 1 w) ∂P := by
    calc
      _ = ∫ x, f x ∂(P.map (X t)) :=
        (integral_map (hm t) hf.aestronglyMeasurable).symm
      _ = ∫ x, f x ∂(P.map (fun w => theta * X 1 w)) := by rw [hscale]
      _ = _ := by
        have hsm : AEMeasurable (fun w => theta * X 1 w) P := aemeasurable_const.mul (hm 1)
        rw [integral_map hsm hf.aestronglyMeasurable]
        simp [f, neg_mul]
  have hi := Kyprianou.Ch03.stablePositiveNegativeExpIntegrableV1 P X hX T hLK
    alpha c hAlpha hC hGaussian hMeasure hStable 1 (by norm_num)
  have h := Kyprianou.Ch03.stableLevyLogMomentTimeScalingV1 P X hX (-1) hi t
  simp only [neg_one_mul] at h
  rw [he, ht] at h
  rw [h, mul_comm]
