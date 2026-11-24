-- Prove2me | solution 1 for Kyprianou.Ch03.stableHighIndexNoIntegerMomentsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:45:22.292357+00:00
-- url     : https://prove2.me/submissions/57125fb3-d7b2-4e33-958d-adfc53b67586

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_stableFracMoment_forward
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03
theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha c : ℝ) (hAlpha : 0 < alpha ∧ alpha < 2)
    (hC : 0 < c) (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure =
      temperedStablePositiveMeasure c alpha 0)
    (hStable : ∀ (t : NNReal) (scale : ℝ), 0 < scale →
      P.map (X (t * Real.toNNReal scale)) =
        P.map (fun omega => scale ^ (1 / alpha) * X t omega)) :
    1 < alpha →
      ∀ n : ℕ, 2 ≤ n →
        ¬ Integrable (fun omega => |X 1 omega| ^ n) P := by
  intro ha n hn hi
  let f : ℝ → ℝ := fun x => |x| ^ n
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hm (t : NNReal) : AEMeasurable (X t) P :=
    Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t
  have hAll : ∀ t : NNReal, 0 < t → Integrable (fun w => |X t w| ^ (n : ℝ)) P := by
    intro t ht
    let s : ℝ := (t : ℝ) ^ (1 / alpha)
    have hscale : P.map (X t) = P.map (fun w => s * X 1 w) := by
      simpa [s] using hStable 1 (t : ℝ) (by exact_mod_cast ht)
    have hs : AEMeasurable (fun w => s * X 1 w) P := aemeasurable_const.mul (hm 1)
    have hI : Integrable (f ∘ fun w => s * X 1 w) P := by
      change Integrable (fun w => |s * X 1 w| ^ n) P
      simpa only [abs_mul, mul_pow] using hi.const_mul (|s|^n)
    have hmap := (integrable_map_measure hf.aestronglyMeasurable hs).mpr hI
    rw [← hscale] at hmap
    simp only [Real.rpow_natCast]
    exact (integrable_map_measure hf.aestronglyMeasurable (hm t)).mp hmap
  have hd : T.levyMeasure = (volume : Measure ℝ).withDensity
      (fun x : ℝ => ENNReal.ofReal
        (if 0 < x then c / (x ^ (1 + alpha))
          else if x < 0 then 0 / ((-x) ^ (1 + alpha)) else 0)) := by
    rw [hMeasure]
    unfold Kyprianou.Ch03.temperedStablePositiveMeasure
    congr 1
    funext x
    by_cases hx : 0 < x <;> simp [hx]
  have h := Kyprianou.Ch03.stableFracMoment_forward P X hX T hLK alpha c 0 (n : ℝ)
    hAlpha hC.le (by norm_num) (by simpa using hC) hd (by exact_mod_cast (show 0 < n by omega)) hAll
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith [hAlpha.2]
