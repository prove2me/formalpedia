-- Prove2me | solution 1 for Kyprianou.Ch04.localisationOuterEventLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:00:59.95287+00:00
-- url     : https://prove2.me/submissions/21905080-077f-48c1-93ac-392940f18218

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

/-- Local error estimates with vanishing exceptional outer probability imply convergence. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Set Ω) (A : ℕ → ℕ → Set Ω) (E : ℕ → Set Ω)
    (hB : Tendsto (fun n => (P (B n)).toReal) atTop (nhds 0))
    (hA : ∀ n, Tendsto (fun j => (P (A n j)).toReal) atTop (nhds 0))
    (hSub : ∀ n j, E j ⊆ B n ∪ A n j) :
    Tendsto (fun j => (P (E j)).toReal) atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun j => ha.trans_le ENNReal.toReal_nonneg)
  · intro a ha
    obtain ⟨n, hn⟩ := ((tendsto_order.mp hB).2 (a / 2) (by linarith)).exists
    filter_upwards [(tendsto_order.mp (hA n)).2 (a / 2) (by linarith)] with j hj
    have hle : P (E j) ≤ P (B n) + P (A n j) :=
      (measure_mono (hSub n j)).trans (measure_union_le _ _)
    have hr := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top P _, measure_ne_top P _⟩) hle
    rw [ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _)] at hr
    linarith
