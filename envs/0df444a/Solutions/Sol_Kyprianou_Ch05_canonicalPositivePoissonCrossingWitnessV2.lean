-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositivePoissonCrossingWitnessV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:57:38.369484+00:00
-- url     : https://prove2.me/submissions/9edc68b7-4d49-46d9-b8bd-96e7738c8f61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonPathAdaptedV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCadlagMonotoneV1
import Theorems.Thm_Kyprianou_Ch05_rawPredictableLeftVersionPositiveV1
import Theorems.Thm_Kyprianou_Ch05_predictableMarkedPositiveCrossingKernelV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCrossingPathLimitV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCrossingIntensityLimitV1
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
      (Iic (t : ℝ) ×ˢ univ)) :
    let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    ∃ psi : ℝ → ℝ → Lambda → ENNReal,
      Measurable[F.predictable.prod inferInstance]
        (fun z : (NNReal × Lambda) × ℝ => psi (z.1.1 : ℝ) z.2 z.1.2) ∧
      Tendsto (fun n : ℕ => ∫⁻ w, ∫⁻ z in Icc (0 : ℝ) (n : ℝ) ×ˢ univ,
        psi z.1 z.2 w ∂(N.N w) ∂Q) atTop (nhds (∫⁻ f, H f ∂(Q.map (fun w t => X t w)))) ∧
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
  have hX : Adapted F X := canonicalPositivePoissonPathAdaptedV1 Pi K Z F hF d
  have hreg : ∀ᵐ w ∂Q, Monotone (fun t => X t w) ∧ X 0 w = 0 := by
    filter_upwards [canonicalPositivePoissonCadlagMonotoneV1 Q Pi K Z hd hint d hdrift] with w hw
    exact ⟨hw.1,by simp [X]⟩
  obtain ⟨V,hV,hl⟩ := rawPredictableLeftVersionPositiveV1 Q F X hX hreg
  have hl' : ∀ᵐ w ∂Q, ∀ t : NNReal, 0 < t → V t w =
      Function.leftLim (fun s : ℝ => d*s + (∫⁻ z in Ioc (0 : ℝ) s ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) (t : ℝ) := by
    filter_upwards [hl,hreg] with w hw hr
    intro t ht
    rw [hw t ht]
    let g := fun s : ℝ => d*s + (∫⁻ z in Ioc (0 : ℝ) s ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    change Function.leftLim (fun s => X s w) t = Function.leftLim g (t : ℝ)
    have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
    have htend : Tendsto Real.toNNReal (nhdsWithin (t : ℝ) (Iio (t : ℝ)))
        (nhdsWithin t (Iio t)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_,?_⟩
      · have hi : Tendsto (id : ℝ → ℝ) (nhdsWithin (t : ℝ) (Iio (t : ℝ))) (nhds (t : ℝ)) :=
          nhdsWithin_le_nhds
        simpa only [Real.toNNReal_coe,id_eq] using tendsto_real_toNNReal hi
      · filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Ioi_mem_nhds ht')] with s hs hp
        exact (Real.toNNReal_lt_iff_lt_coe hp.le).mpr hs
    have htend' := (hr.1.tendsto_leftLim t).comp htend
    have he : (fun s => X s.toNNReal w) =ᶠ[nhdsWithin (t : ℝ) (Iio (t : ℝ))] g := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht')] with s hs
      simp [X,g,Real.coe_toNNReal _ hs.le]
    have hlim : Tendsto g (nhdsWithin (t : ℝ) (Iio (t : ℝ)))
        (nhds (Function.leftLim (fun s => X s w) t)) := htend'.congr' he
    exact (leftLim_eq_of_tendsto hlim).symm
  let psi := fun (s z : ℝ) (w : Lambda) =>
    if 0 < s ∧ V s.toNNReal w ∈ Icc (0 : ℝ) x ∧
      x - V s.toNNReal w < z ∧ z-(x-V s.toNNReal w) ∈ A ∧
      x-V s.toNNReal w ∈ B then ENNReal.ofReal (Real.exp (-eta*s)) else 0
  refine ⟨psi,predictableMarkedPositiveCrossingKernelV1 F V hV eta x A B hA hB,?_,?_⟩
  · exact canonicalPositivePoissonCrossingPathLimitV1 Q Pi K Z hd eta d heta hdrift hs hint
      x hx A B hA hB hAp hBp H hHmeas hH N hN F hF V hV hl'
  · exact canonicalPositivePoissonCrossingIntensityLimitV1 Q Pi K Z hd eta d heta hdrift hs hint
      x hx A B hA hB hAp hBp H hHmeas hH N hN F hF V hV hl'
