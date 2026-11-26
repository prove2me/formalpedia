-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41CountableSlopeTransferV13
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:03:46.632457+00:00
-- url     : https://prove2.me/submissions/37f3b64f-5c48-406a-9b9f-dfd19bd17224

import Mathlib
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_full_future_source_law
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F)
    (τ : Ω → NNReal) (hτ : ∀ s : NNReal, MeasurableSet[F.rightCont s] {w | τ w ≤ s})
    (q : ℕ → NNReal) (c : ℝ)
    (h : ∀ᵐ w ∂P, ∃ n : ℕ, ∀ k : ℕ, 0 < q k → q k < 1 / ((n : NNReal) + 1) →
      c * (q k : ℝ) ≤ L.X (q k) w) :
    ∀ᵐ w ∂P, ∃ n : ℕ, ∀ k : ℕ, 0 < q k → q k < 1 / ((n : NNReal) + 1) →
      c * (q k : ℝ) ≤ L.X (τ w + q k) w - L.X (τ w) w := by
  let G : Set (NNReal → ℝ) := {f | ∃ n : ℕ, ∀ k : ℕ, 0 < q k →
    q k < 1 / ((n : NNReal) + 1) → c * (q k : ℝ) ≤ f (q k)}
  have hm : MeasurableSet G := by
    have he : G = (⋃ n : ℕ, ⋂ k : ℕ, ⋂ (_ : 0 < q k),
      ⋂ (_ : q k < 1 / ((n : NNReal) + 1)), {f : NNReal → ℝ | c * (q k : ℝ) ≤ f (q k)}) := by
      ext y
      simp [G]
    rw [he]
    exact MeasurableSet.iUnion (fun n => MeasurableSet.iInter (fun k =>
      MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
        measurableSet_le measurable_const (measurable_pi_apply (q k))))))
  let f : Ω → NNReal → ℝ := fun w t => L.X t w
  let g : Ω → NNReal → ℝ := fun w t => L.X (τ w + t) w - L.X (τ w) w
  have hf : Measurable f := measurable_pi_lambda _ (fun t => (L.adapted t).mono (F.le t) le_rfl)
  obtain ⟨Y,hY,-,-,-⟩ := avram_wave5_04_source_rightCont_levy_lift L
  have hg : Measurable g := by
    simpa only [g,hY] using levy_finiteStopping_stoppedFuturePath_measurable Y τ (isStoppingTime_withTop_of_le_events τ hτ)
  have he : Measure.map g P = Measure.map f P :=
    avram_wave6_03_original_rightCont_stopped_full_future_source_law L τ hτ
  have hF : ∀ᵐ y ∂Measure.map f P, y ∈ G := (ae_map_iff hf.aemeasurable hm).2 h
  rw [← he] at hF
  exact (ae_map_iff hg.aemeasurable hm).1 hF
