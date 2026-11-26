-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositivePoissonCrossingIntensityLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:24:15.825711+00:00
-- url     : https://prove2.me/submissions/0386b979-e562-4e5c-99db-1b0315bd3842

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_markedPositiveCrossingKernelIntegrateV1
import Theorems.Thm_Kyprianou_Ch05_positiveDiscountedKernelHorizonLimitV1
import Theorems.Thm_Kyprianou_Ch05_positiveTimeLeftLimitRealNNRealV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonNoFixedJumpV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCadlagMonotoneV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonStripMeasurableAmbientV1
import Theorems.Thm_Kyprianou_Ch05_jumpPotentialKernelMeasurableV1
import Theorems.Thm_AvramDividend_Classical_ripple_predictable_le_ambient_product
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (eta d : ℝ) (heta : 0 ≤ eta) (hdrift : 0 ≤ d)
    (hs : Pi (Iic (0 : ℝ)) = 0)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (x : ℝ) (hx : 0 < x) (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAp : A ⊆ Ioi (0 : ℝ)) (hBp : B ⊆ Icc (0 : ℝ) x)
    (H : (NNReal → ℝ) → ENNReal) (hHmeas : Measurable H)
    (hH : ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        (∀ t, ContinuousWithinAt f (Ici t) t) →
        (∀ t, 0 < t → ∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l)) →
        H f = ∑' t : NNReal, if 0 < t ∧ f t > x ∧
          Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
          f t - x ∈ A ∧ x - Function.leftLim f t ∈ B then
          ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0)     (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} Q Pi)
    (hN : ∀ w, N.N w = (poissonRandomMeasure K Z w).restrict (Ici (0 : ℝ) ×ˢ univ))
    (F : Filtration NNReal inferInstance)
    (hF : ∀ t : NNReal, F t = prmEvalSigma K Z ((volume : Measure ℝ).prod Pi)
      (Iic (t : ℝ) ×ˢ univ))
    (V : NNReal → Lambda → ℝ)
    (hV : Measurable[F.predictable] (Function.uncurry V))
    (hleft : ∀ᵐ w ∂Q, ∀ t : NNReal, 0 < t →
      V t w = Function.leftLim (fun s => d * (s : ℝ) +
        (∫⁻ z in Ioc (0 : ℝ) (s : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) t) :
    let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    let psi := fun (s z : ℝ) (w : Lambda) =>
      if 0 < s ∧ V s.toNNReal w ∈ Icc (0 : ℝ) x ∧
        x - V s.toNNReal w < z ∧ z-(x-V s.toNNReal w) ∈ A ∧
        x-V s.toNNReal w ∈ B then ENNReal.ofReal (Real.exp (-eta*s)) else 0
    Tendsto (fun n : ℕ => ∫⁻ w, ∫⁻ t in Icc (0 : ℝ) (n : ℝ),
        ∫⁻ z, psi t z w ∂Pi ∂volume ∂Q) atTop (nhds (
      ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-eta*t)) *
      (∫⁻ v, (fun v : ℝ => if v ∈ Icc (0 : ℝ) x then
          ∫⁻ z in Ioi (x-v), if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
        else 0) v ∂(Q.map (X (Real.toNNReal t)))) ∂volume)) := by
  classical
  dsimp only
  let X := fun (t : NNReal) (w : Lambda) =>
    d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
  let f := (fun v : ℝ => if v ∈ Icc (0 : ℝ) x then
      ∫⁻ z in Ioi (x-v), if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
      else 0)
  have hVm : Measurable (Function.uncurry V) :=
    hV.mono (AvramDividend.Classical.ripple_predictable_le_ambient_product F) le_rfl
  have hXm (t : NNReal) : Measurable (X t) :=
    (positivePoissonStripMeasurableAmbientV1 Q Pi K Z hd hint 0 t).const_add (d*(t : ℝ))
  have hm : ∀ᵐ w ∂Q, Monotone (fun t => X t w) := by
    filter_upwards [canonicalPositivePoissonCadlagMonotoneV1 Q Pi K Z hd hint d hdrift] with w hw
    exact hw.1
  have hl := positiveTimeLeftLimitRealNNRealV1 Q
    (fun s w => d*s+(∫⁻ z in Ioc (0 : ℝ) s ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) V hm hleft
  have he (t : NNReal) (ht : 0 < t) : V t =ᵐ[Q] X t := by
    filter_upwards [hl,canonicalPositivePoissonNoFixedJumpV1 Q Pi K Z hd hint d hdrift t ht] with w hw hj
    exact (hw t ht).trans hj
  have hf : Measurable f := (jumpPotentialKernelMeasurableV1 (0 : Measure ℝ) Pi x A B hA hB).1
  have hh := positiveDiscountedKernelHorizonLimitV1 Q V X hVm hXm he f hf eta
  convert hh using 1
  funext n
  apply lintegral_congr
  intro w
  apply lintegral_congr
  intro s
  exact markedPositiveCrossingKernelIntegrateV1 Pi eta x s (V s.toNNReal w) A B
