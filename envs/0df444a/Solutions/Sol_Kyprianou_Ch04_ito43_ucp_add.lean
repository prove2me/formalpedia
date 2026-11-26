-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ucp_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:46:13.934824+00:00
-- url     : https://prove2.me/submissions/af38e90e-c161-4af8-ac32-fe1b7e924b45

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Uniform-in-probability errors combine by the triangle inequality and union bound. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E G : ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (hE : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => (P {w | ∃ t ≤ T, ε ≤ |E n t w|}).toReal) atTop (𝓝 0))
    (hG : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => (P {w | ∃ t ≤ T, ε ≤ |G n t w|}).toReal) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, ε ≤ |E n t w + G n t w|}).toReal)
      atTop (𝓝 0) := by
  have h := (hE (ε/2) (by positivity)).add (hG (ε/2) (by positivity))
  rw [add_zero] at h
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ h
  intro n
  let A : Set Ω := {w | ∃ t ≤ T, ε/2 ≤ |E n t w|}
  let B : Set Ω := {w | ∃ t ≤ T, ε/2 ≤ |G n t w|}
  let C : Set Ω := {w | ∃ t ≤ T, ε ≤ |E n t w + G n t w|}
  have hsub : C ⊆ A ∪ B := by
    rintro w ⟨t,ht,hw⟩
    by_cases he : ε/2 ≤ |E n t w|
    · exact Or.inl ⟨t,ht,he⟩
    · right
      refine ⟨t,ht,?_⟩
      have htri := abs_add_le (E n t w) (G n t w)
      linarith [lt_of_not_ge he]
  change (P C).toReal ≤ (P A).toReal + (P B).toReal
  rw [← ENNReal.toReal_add (measure_ne_top P A) (measure_ne_top P B)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top P A, measure_ne_top P B⟩)
    ((measure_mono hsub).trans (measure_union_le A B))
