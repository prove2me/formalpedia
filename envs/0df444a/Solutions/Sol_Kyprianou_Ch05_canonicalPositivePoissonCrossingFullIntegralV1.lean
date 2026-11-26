-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositivePoissonCrossingFullIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:52:08.867928+00:00
-- url     : https://prove2.me/submissions/e05be535-5065-4022-a158-9423b10d8953

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_positivePoissonCrossingAtomicSumV1
import Theorems.Thm_Kyprianou_Ch05_pointFamilyPairLIntegralV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCadlagMonotoneV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonJumpFibreV1
import Theorems.Thm_Kyprianou_Ch05_positiveTimeLeftLimitRealNNRealV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonDistinctActiveTimesV1
import Theorems.Thm_Kyprianou_Ch05_markedPositiveCrossingAmbientMeasurableV1
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
    ∀ᵐ w ∂Q, (∫⁻ z in Ici (0 : ℝ) ×ˢ (univ : Set ℝ), psi z.1 z.2 w ∂(N.N w)) =
      H (fun t => X t w) := by
  classical
  dsimp only
  let X := fun (t : NNReal) (w : Lambda) =>
    d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
  let psi := fun (s z : ℝ) (w : Lambda) =>
    if 0 < s ∧ V s.toNNReal w ∈ Icc (0 : ℝ) x ∧
      x - V s.toNNReal w < z ∧ z-(x-V s.toNNReal w) ∈ A ∧
      x-V s.toNNReal w ∈ B then ENNReal.ofReal (Real.exp (-eta*s)) else 0
  let g (w : Lambda) (z : ℝ × ℝ) := psi z.1 z.2 w
  have hg : Measurable (Function.uncurry g) :=
    markedPositiveCrossingAmbientMeasurableV1 F V hV eta x A B hA hB
  have hm : ∀ᵐ w ∂Q, Monotone (fun t => X t w) := by
    filter_upwards [canonicalPositivePoissonCadlagMonotoneV1 Q Pi K Z hd hint d hdrift] with w hw
    exact hw.1
  have hl := positiveTimeLeftLimitRealNNRealV1 Q
    (fun s w => d*s+(∫⁻ z in Ioc (0 : ℝ) s ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) V hm hleft
  filter_upwards [hl,canonicalPositivePoissonCadlagMonotoneV1 Q Pi K Z hd hint d hdrift,
    canonicalPositivePoissonJumpFibreV1 Q Pi K Z hd hint d hdrift,
    positivePoissonDistinctActiveTimesV1 Q Pi K Z hd] with w hw hc hj hi
  symm
  rw [hH (fun t => X t w) hc.1 (by simp [X]) (fun t => (hc.2 t).1)
    (fun t _ => (hc.2 t).2)]
  rw [hN,Measure.restrict_restrict_of_subset le_rfl]
  have hwhole : (∫⁻ z in Ici (0 : ℝ) ×ˢ (univ : Set ℝ), g w z
      ∂(poissonRandomMeasure K Z w)) =
      ∫⁻ z, g w z ∂(poissonRandomMeasure K Z w) := by
    rw [← lintegral_indicator (measurableSet_Ici.prod MeasurableSet.univ)]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ Ici (0 : ℝ) ×ˢ (univ : Set ℝ)
    · exact Set.indicator_of_mem hz _
    · rw [Set.indicator_of_notMem hz]
      have hn : ¬ 0 < z.1 := fun hp => hz ⟨hp.le,mem_univ _⟩
      simp [g,psi,hn]
  have hgw : Measurable (g w) := hg.comp (measurable_prodMk_left (x := w))
  rw [hwhole,pointFamilyPairLIntegralV1 K Z w (g w) hgw]
  rw [← positivePoissonCrossingAtomicSumV1 K Z w (fun t => X t w) hi hj hc.1 eta x A B]
  apply tsum_congr
  intro i
  by_cases hk : i.2 < K i.1 w
  · by_cases hs : 0 < (Z i.1 i.2 w).1
    · simp only [hk,if_true,g,psi,hw _ (Real.toNNReal_pos.mpr hs),X]
    · simp [hk,g,psi,hs]
  · simp [hk]
