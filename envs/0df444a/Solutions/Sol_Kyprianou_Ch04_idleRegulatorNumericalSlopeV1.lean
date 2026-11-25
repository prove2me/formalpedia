-- Prove2me | solution 1 for Kyprianou.Ch04.idleRegulatorNumericalSlopeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:16:27.426501+00:00
-- url     : https://prove2.me/submissions/ffb443cc-058c-46da-9131-2f9a723242bc

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (d gap k : Real) (hd : 0 < d) (hg : 0 ≤ gap)
    (step r q : Nat → Real) (hpos : ∀ n, 0 < step n)
    (hstep : Tendsto step atTop (𝓝 0))
    (hq : Tendsto q atTop (𝓝 0))
    (hr : Tendsto r atTop (𝓝 k))
    (hb : ∀ n, 0 ≤ r n ∧
      r n ≤ max 0 (-gap + d * step n) / step n)
    (hl : gap = 0 → ∀ n, d - q n ≤ r n) :
    k = if gap = 0 then d else 0 := by
  by_cases hc : gap = 0
  · rw [if_pos hc]
    have hu (n : Nat) : r n ≤ d := by
      have h := (hb n).2
      rw [hc, neg_zero, zero_add, max_eq_right (mul_nonneg hd.le (hpos n).le),
        mul_div_cancel_right₀ _ (hpos n).ne'] at h
      exact h
    have hdl : Tendsto (fun n => d - q n) atTop (𝓝 d) := by
      simpa using tendsto_const_nhds.sub hq
    exact le_antisymm (le_of_tendsto_of_tendsto' hr tendsto_const_nhds hu)
      (le_of_tendsto_of_tendsto' hdl hr (hl hc))
  · rw [if_neg hc]
    have hg' : 0 < gap := lt_of_le_of_ne hg (fun he => hc he.symm)
    have ht : Tendsto (fun n => d * step n) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hstep
    have hz : r =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [ht.eventually_lt_const hg'] with n hn
      have h := (hb n).2
      rw [max_eq_left (by linarith), zero_div] at h
      exact le_antisymm h (hb n).1
    exact tendsto_nhds_unique hr (tendsto_const_nhds.congr' hz.symm)
