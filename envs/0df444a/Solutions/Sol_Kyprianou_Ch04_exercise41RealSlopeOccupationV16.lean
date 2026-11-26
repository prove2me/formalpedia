-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41RealSlopeOccupationV16
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:13:28.424877+00:00
-- url     : https://prove2.me/submissions/919af55c-f783-43e1-8fba-792d7202f960

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : ℝ → ℝ)
    (h : ∀ᵐ s ∂(volume : Measure ℝ), 0 ≤ s → ∃ e : ℝ, 0 < e ∧
      ∀ v ∈ Ioo s (s + e), x s < x v) :
    ∀ b : ℝ, volume {s : ℝ | 0 ≤ s ∧ x s = b} = 0 := by
  intro b
  let E : Set ℝ := {s | 0 ≤ s ∧ x s = b}
  let C : Set ℝ := {s ∈ E | nhdsWithin s (E ∩ Ioi s) = ⊥}
  have hc : C.Countable := countable_setOfPred_isolated_right_within
  have hn : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ C := by
    rw [ae_iff]
    simpa using hc.measure_zero (volume : Measure ℝ)
  have hnull : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ E := by
    filter_upwards [h,hn] with s hs hnot
    intro hE
    obtain ⟨e,he,hlocal⟩ := hs hE.1
    apply hnot
    refine ⟨hE,?_⟩
    apply empty_mem_iff_bot.mp
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Iio (s+e),Iio_mem_nhds (by linarith),?_⟩
    intro v hv
    have hv' := hlocal v ⟨hv.2.2,hv.1⟩
    rw [hE.2,hv.2.1.2] at hv'
    exact False.elim ((lt_irrefl b) hv')
  simpa [E,ae_iff] using hnull
