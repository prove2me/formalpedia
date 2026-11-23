-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteMarkedApproxL2BoundFromMarksV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:12:11.721894+00:00
-- url     : https://prove2.me/submissions/b903ebed-94fd-4bc3-9f99-1dc8ab95bcc0

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkFiniteCountRepresentationV1
import Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkRawIntegralUniformL2LiminfV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkRawIntegralL2V1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeRectIntensityFiniteV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteIntensityWindowSimpleMarkIntegralTendstoV1
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B))
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hfpoint : ∀ x : ℝ,
      Filter.Tendsto (fun n => (f n) x) Filter.atTop (nhds x))
    (hfL2 : Filter.Tendsto
      (fun n => eLpNorm (fun x : ℝ => (f n) x - x) 2 (ν.restrict B))
      Filter.atTop (nhds 0)) :
    ∀ t : ℝ≥0,
      ∃ (F : ℕ → Finset ℕ)
        (C : ℕ → ℕ → Set (ℝ × ℝ)) (a : ℕ → ℕ → ℝ),
        (∀ n i, i ∈ F n → MeasurableSet (C n i)) ∧
        (∀ n i, i ∈ F n →
          LevyStochCalc.Poisson.referenceIntensity ν (C n i) ≠ ⊤) ∧
        (∀ n i, i ∈ F n →
          C n i ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) ∧
        (∀ᵐ ω ∂P,
          Filter.Tendsto
            (fun n => ∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal)
            Filter.atTop
            (nhds (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
              z.2 ∂(N.N ω)))) ∧
        Filter.liminf
          (fun n => eLpNorm
            (fun ω => ∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal)
            2 P) Filter.atTop < ⊤ := by
  have hRmeas (t : ℝ≥0) :
      MeasurableSet (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hRfin (t : ℝ≥0) :
      LevyStochCalc.Poisson.referenceIntensity ν
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤ :=
    Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1
      ν B hB hfinite 0 t
  have hrawL2 (t : ℝ≥0) (n : ℕ) :
      MemLp (fun ω =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          (f n) z.2 ∂(N.N ω)) 2 P :=
    Kyprianou.Ch02.prmFiniteSimpleMarkRawIntegralL2V1
      P ν N _ (hRmeas t) (hRfin t) (f n)
  intro t
  obtain ⟨F, C, a, hm, hfinC, hs, hrepr⟩ :=
    Kyprianou.Ch02.prmSimpleMarkFiniteCountRepresentationV1
      P ν N B hB hfinite f t
  refine ⟨F, C, a, hm, hfinC, hs, ?_, ?_⟩
  · have hconv := Kyprianou.Ch02.prmFiniteIntensityWindowSimpleMarkIntegralTendstoV1
      P ν N (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) (hRmeas t) (hRfin t)
      f hfpoint
    filter_upwards [hrepr, hconv] with ω hre hlim
    have hseq :
        (fun n => ∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal) =
          (fun n => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
            (f n) z.2 ∂(N.N ω)) := by
      funext n
      exact hre n
    rw [hseq]
    exact hlim
  · have huniform := Kyprianou.Ch02.prmSimpleMarkRawIntegralUniformL2LiminfV1
      P ν N B hB hfinite hsecond f hfL2 hrawL2 t
    have hseq :
        (fun n => eLpNorm (fun ω =>
          ∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal) 2 P) =
          (fun n => eLpNorm (fun ω =>
            ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
              (f n) z.2 ∂(N.N ω)) 2 P) := by
      funext n
      apply eLpNorm_congr_ae
      filter_upwards [hrepr] with ω hre
      exact hre n
    rw [hseq]
    exact huniform
