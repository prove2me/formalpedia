-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ucp_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:08:37.901926+00:00
-- url     : https://prove2.me/submissions/29e3d714-3138-4436-b9d4-f346658ca46a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_add
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- An eventually exact decomposition of the error transfers uniform-in-probability convergence. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E G H : ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (hE : ∀ e : ℝ, 0 < e → Tendsto
      (fun n => (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal) atTop (nhds 0))
    (hG : ∀ e : ℝ, 0 < e → Tendsto
      (fun n => (P {w | ∃ t ≤ T, e ≤ |G n t w|}).toReal) atTop (nhds 0))
    (hH : ∀ n : ℕ, 0 < n → ∀ t ≤ T, ∀ w, H n t w = E n t w + G n t w)
    (e : ℝ) (he : 0 < e) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |H n t w|}).toReal) atTop (nhds 0) := by
  apply (Kyprianou.Ch04.ito43_ucp_add P E G T hE hG e he).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  congr 1
  apply congrArg P
  ext w
  constructor <;> rintro ⟨t,ht,h⟩ <;> exact ⟨t,ht,by simpa only [hH n hn t ht w] using h⟩
