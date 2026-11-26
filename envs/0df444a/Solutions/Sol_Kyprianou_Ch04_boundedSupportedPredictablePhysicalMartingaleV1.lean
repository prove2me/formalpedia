-- Prove2me | solution 1 for Kyprianou.Ch04.boundedSupportedPredictablePhysicalMartingaleV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:45:44.6268+00:00
-- url     : https://prove2.me/submissions/a4a66b20-e503-4abb-81d5-ea5059a94b38

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedPhysicalPastMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedWindowIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_predictablePhysicalKernelSectionV1
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedPredictablePhysicalCenteredV1
import Theorems.Thm_Kyprianou_Ch04_boundedPredictablePhysicalPastEventIncrementV1
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Bounded finite-band predictable physical compensation is a martingale in the completed past. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (X : NNReal → Ω → ℝ) (F : Filtration NNReal inferInstance)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (u : ℝ) ×ˢ univ → Measurable[F u] (fun w => N.N w D))
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ p, ‖g p‖ ≤ C)
    (hs : ∀ p, p.2 ∉ B → g p = 0) :
    let J := fun (t : NNReal) w =>
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν
    Martingale J F P := by
  let D (t : NNReal) := Icc (0 : ℝ) (t : ℝ) ×ˢ B
  let U (t : NNReal) := Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ)
  let k (w : Ω) (z : ℝ × ℝ) := g ((z.1.toNNReal,w),z.2)
  let J (t : NNReal) (w : Ω) := (∫ z in U t, k w z ∂(N.N w)) -
    ∫ z in U t, k w z ∂referenceIntensity ν
  have hI (t : NNReal) : referenceIntensity ν (D t) < ⊤ :=
    (Kyprianou.Ch04.closedTimeBandIntensityFinite ν t B hfin).lt_top
  have hN (t : NNReal) : ∀ᵐ w ∂P, N.N w (D t) < ⊤ := by
    filter_upwards [N.integer_valued (measurableSet_Icc.prod hB) (hI t).ne] with w hw
    obtain ⟨n,hn⟩ := hw
    rw [hn]
    exact ENNReal.natCast_lt_top n
  have had : StronglyAdapted F J := by
    intro t
    have r := Kyprianou.Ch04.boundedSupportedPhysicalPastMeasurableV1 P X F hF N.N t B hB
      (fun S hS hsub => hPast t S hS (hsub.trans (Set.prod_mono subset_rfl (subset_univ B))))
      (hN t) g hg C hC hs
    have c := Kyprianou.Ch04.boundedSupportedPhysicalPastMeasurableV1 P X F hF
      (fun _ => referenceIntensity ν) t B hB (fun _ _ _ => measurable_const)
      (Eventually.of_forall fun _ => hI t) g hg C hC hs
    exact (r.sub c).stronglyMeasurable
  have hi (t : NNReal) : Integrable (J t) P :=
    (Kyprianou.Ch04.boundedSupportedPredictablePhysicalCenteredV1 P ν F N
      hFuture t B hB hfin g hg C hC hs).1
  refine ⟨had,fun s t hst => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hi t)
    (fun A _ _ => (hi s).integrableOn) _ (had s).aestronglyMeasurable
  intro A hA _
  apply Kyprianou.Ch04.boundedPredictablePhysicalPastEventIncrementV1 P ν F N
    hFuture B hB hfin g hg C hC0 hC hs s t hst A hA
  filter_upwards [hN t] with w hw
  have hk := Kyprianou.Ch04.predictablePhysicalKernelSectionV1 F g hg w
  exact ⟨(Kyprianou.Ch04.boundedSupportedWindowIntegrableV1 (N.N w) t B hB hw
    (k w) hk C (fun p => hC _) (fun p hp => hs _ hp)).1,
    (Kyprianou.Ch04.boundedSupportedWindowIntegrableV1 (referenceIntensity ν) t B hB
      (hI t) (k w) hk C (fun p => hC _) (fun p hp => hs _ hp)).1⟩
