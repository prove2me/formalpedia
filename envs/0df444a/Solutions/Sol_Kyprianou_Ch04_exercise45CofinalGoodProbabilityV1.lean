-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45CofinalGoodProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:35:19.83442+00:00
-- url     : https://prove2.me/submissions/69dabb94-5986-4e0e-8652-b84ff2322ae3

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Cofinal finite clocks exhaust compact intervals outside any common null set. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℕ → Ω → NNReal)
    (hMeas : ∀ n T, MeasurableSet {w | τ n w ≤ T})
    (hMono : ∀ w, Monotone (fun n => τ n w))
    (hCof : ∀ᵐ w ∂P, Tendsto (fun n => (τ n w : WithTop NNReal)) atTop (nhds ⊤))
    (G : Ω → Prop) (hG : ∀ᵐ w ∂P, G w) (T : NNReal) :
    Tendsto (fun n => (P {w | ¬ G w ∨ τ n w ≤ T}).toReal) atTop (nhds 0) := by
  let A (n : ℕ) := {w | τ n w ≤ T}
  have hAnti : Antitone A := fun n m hnm w hw => (hMono w hnm).trans hw
  have hnot : ∀ᵐ w ∂P, w ∉ ⋂ n, A n := by
    filter_upwards [hCof] with w hw
    rw [WithTop.tendsto_nhds_top_iff] at hw
    obtain ⟨n,hn⟩ := (hw T).exists
    intro h
    exact (not_le_of_gt (WithTop.coe_lt_coe.mp hn)) (mem_iInter.mp h n)
  have hz : P (⋂ n, A n) = 0 := by simpa only [not_not,setOf_mem_eq] using ae_iff.mp hnot
  have h := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (hMeas n T).nullMeasurableSet) hAnti ⟨0,measure_ne_top P _⟩
  rw [hz] at h
  have hlim : Tendsto (fun n => (P (A n)).toReal) atTop (nhds 0) := by
    simpa only [ENNReal.toReal_zero,Function.comp_def] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  change (P (A n)).toReal = (P {w | ¬ G w ∨ τ n w ≤ T}).toReal
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hG] with w hw
  change (τ n w ≤ T) = (¬ G w ∨ τ n w ≤ T)
  simp [hw]
