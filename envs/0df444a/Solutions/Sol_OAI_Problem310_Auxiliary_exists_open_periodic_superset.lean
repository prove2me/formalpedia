-- Prove2me | solution 1 for OAI.Problem310.Auxiliary.exists_open_periodic_superset
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T05:25:09.287813+00:00
-- url     : https://prove2.me/submissions/748f6890-e78a-4b33-ad2a-47a12bf14cf9

-- OpenAI/math contributors' proof, ExceptionalCenters.lean lines 103–127,
-- commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
-- Adapted and verified by Codex under Alexander Richard Towell (queelius)'s direction.
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_Problem310_Auxiliary_thickening_periodic

open Set Filter Topology MeasureTheory Metric

theorem solution (R : Set ℝ) (hRc : IsClosed R)
    (hRp : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set ℝ, IsOpen V ∧
      (∀ x : ℝ, x + 1 ∈ V ↔ x ∈ V) ∧ R ⊆ V ∧
      volume (V ∩ Icc (0 : ℝ) 1) ≤
        volume (R ∩ Icc (0 : ℝ) 1) + ENNReal.ofReal ε := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hfinite : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  let := hfinite
  have hlim : Tendsto (fun r => μ (thickening r R)) (𝓝[>] 0) (𝓝 (μ R)) :=
    tendsto_measure_thickening_of_isClosed ⟨1, zero_lt_one, measure_ne_top μ _⟩ hRc
  have hlt : μ R < μ R + ENNReal.ofReal ε :=
    ENNReal.lt_add_right (measure_ne_top μ R) (by positivity)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (thickening r R) < μ R + ENNReal.ofReal ε :=
    hlim.eventually (eventually_lt_nhds hlt)
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hbound⟩ := (hpos.and hev).exists
  refine ⟨thickening r R, isOpen_thickening,
    OAI.Problem310.Auxiliary.thickening_periodic R hRp r,
    self_subset_thickening hr R, ?_⟩
  simpa [μ, Measure.restrict_apply, isOpen_thickening.measurableSet,
    hRc.measurableSet] using hbound.le
