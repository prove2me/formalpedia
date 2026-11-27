-- Prove2me | solution 1 for Kyprianou.Ch04.physicalKernelReferenceSquareProductV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:56:15.49234+00:00
-- url     : https://prove2.me/submissions/0da7ae74-6cc1-4112-96ff-436770c984d2

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedWindowIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_predictablePhysicalKernelSectionV1
import Theorems.Thm_Kyprianou_Ch04_referenceIntensityClosedWindowProductV1
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The physical reference-intensity square integral equals its iterated positive-time and mark integral. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (ν : Measure ℝ) [SigmaFinite ν] (F : Filtration NNReal inferInstance)
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC : ∀ p, ‖g p‖ ≤ C) (hs : ∀ p, p.2 ∉ B → g p = 0)
    (T : NNReal) (w : Ω) :
    (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ),
      (g ((z.1.toNNReal,w),z.2))^2 ∂referenceIntensity ν) =
    ∫ s in Ioc (0 : ℝ) (T : ℝ), ∫ x, (g ((s.toNNReal,w),x))^2 ∂ν ∂volume := by
  have hLam := Kyprianou.Ch04.closedTimeBandIntensityFinite ν T B hfin
  have hi := (Kyprianou.Ch04.boundedSupportedWindowIntegrableV1
    (referenceIntensity ν) T B hB hLam.lt_top _
    (Kyprianou.Ch04.predictablePhysicalKernelSectionV1 F g hg w)
    C (fun z => hC _) (fun z hz => hs _ hz)).2
  have hp := Kyprianou.Ch04.referenceIntensityClosedWindowProductV1 ν T
    (univ : Set ℝ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at hp
  rw [IntegrableOn,hp] at hi
  rw [hp,integral_prod _ hi,integral_Icc_eq_integral_Ioc]
