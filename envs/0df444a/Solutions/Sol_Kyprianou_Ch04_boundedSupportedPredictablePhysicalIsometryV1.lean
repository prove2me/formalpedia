-- Prove2me | solution 1 for Kyprianou.Ch04.boundedSupportedPredictablePhysicalIsometryV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:25:55.582316+00:00
-- url     : https://prove2.me/submissions/6b40030d-fc6e-441f-b882-1575f89ca25d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_fullPredictablePhysicalL2Core
import Theorems.Thm_Kyprianou_Ch04_fullPredictableClockAgreement
import Theorems.Thm_Kyprianou_Ch04_fullPredictableClockFiniteBandMassV1
import Theorems.Thm_Kyprianou_Ch04_boundedFiniteSupportMemLpV1
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The physical isometry for a bounded predictable kernel supported on a finite mark band. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (u : ℝ) ×ˢ univ →
      Measurable[F u] (fun ω => N.N ω D))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : ((NNReal × Ω) × ℝ) → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC : ∀ p, ‖g p‖ ≤ C)
    (hsupp : ∀ p, p.2 ∉ B → g p = 0) :
    let U := Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ)
    let K := fun ω (z : ℝ × ℝ) => g ((z.1.toNNReal,ω),z.2)
    let J := fun ω => (∫ z in U, K ω z ∂(N.N ω)) -
      ∫ z in U, K ω z ∂referenceIntensity ν
    Integrable (fun ω => (J ω)^2) P ∧
      (∫ ω, (J ω)^2 ∂P) = ∫ ω, ∫ z in U, (K ω z)^2 ∂referenceIntensity ν ∂P := by
  obtain ⟨μ,hClock⟩ := Kyprianou.Ch04.fullPredictableClockAgreement P ν F N hFuture t
  letI : MeasurableSpace ((NNReal × Ω) × ℝ) := F.predictable.prod inferInstance
  have hmass := Kyprianou.Ch04.fullPredictableClockFiniteBandMassV1
    P ν F t B hB hfin rfl μ (fun f hf => (hClock f hf).2.2.2)
  have hp := Kyprianou.Ch04.boundedFiniteSupportMemLpV1 μ (univ ×ˢ B)
    (MeasurableSet.univ.prod hB) hmass g hg C hC
    (fun p hp => hsupp p (fun hb => hp ⟨mem_univ _,hb⟩))
  exact Kyprianou.Ch04.fullPredictablePhysicalL2Core P ν F N hFuture hPast t
    rfl μ hClock g hg hp.1 hp.2
