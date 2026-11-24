-- Prove2me | solution 1 for Kyprianou.Ch03.stablePositiveUnitNonzeroV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:00:56.635913+00:00
-- url     : https://prove2.me/submissions/235cfa5d-e3a0-4f21-8ff0-ea6ac348a09b

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_exercise33StableFractionalMomentCriterion
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
        P.map (fun omega => scale ^ (1 / alpha) * X t omega)) :
    ¬ X 1 =ᵐ[P] 0 := by
  intro hzero
  have hm (t : NNReal) : AEMeasurable (X t) P :=
    Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t
  have hd : T.levyMeasure = (volume : Measure ℝ).withDensity
      (fun x : ℝ => ENNReal.ofReal
        (if 0 < x then c / (x ^ (1 + alpha))
          else if x < 0 then 0 / ((-x) ^ (1 + alpha)) else 0)) := by
    rw [hMeasure]
    unfold Kyprianou.Ch03.temperedStablePositiveMeasure
    congr 1
    funext x
    by_cases hx : 0 < x <;> simp [hx]
  have hi : ∀ t : NNReal, 0 < t → Integrable (fun w => |X t w| ^ (2 : ℝ)) P := by
    intro t ht
    let s : ℝ := (t : ℝ) ^ (1 / alpha)
    have hscale : P.map (X t) = P.map (fun w => s * X 1 w) := by
      simpa [s] using hStable 1 (t : ℝ) (by exact_mod_cast ht)
    let f : ℝ → ℝ := fun x => |x| ^ (2 : ℝ)
    have hf : Measurable f := by dsimp [f]; fun_prop
    have hs : AEMeasurable (fun w => s * X 1 w) P := aemeasurable_const.mul (hm 1)
    have hI : Integrable (f ∘ fun w => s * X 1 w) P := by
      apply (integrable_const (0 : ℝ)).congr
      filter_upwards [hzero] with w hw
      change X 1 w = 0 at hw
      simp [f, hw, Real.rpow_two]
    have hmap := (integrable_map_measure hf.aestronglyMeasurable hs).mpr hI
    rw [← hscale] at hmap
    exact (integrable_map_measure hf.aestronglyMeasurable (hm t)).mp hmap
  have hh := (Kyprianou.Ch03.exercise33StableFractionalMomentCriterion P X hX T hLK
    alpha c 0 2 hAlpha hC.le (by norm_num) (by simpa using hC) hd (by norm_num)).mp hi
  linarith [hAlpha.2]
