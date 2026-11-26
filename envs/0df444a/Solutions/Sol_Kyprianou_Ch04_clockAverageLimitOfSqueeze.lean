-- Prove2me | solution 1 for Kyprianou.Ch04.clockAverageLimitOfSqueeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:27:24.923746+00:00
-- url     : https://prove2.me/submissions/a8c93888-d961-42dc-9bb0-39167bb269c9

import Mathlib
open Filter Set MeasureTheory
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (f : NNReal → ℝ) (A : ℕ → ℝ)
    (err : ℕ → NNReal → ℝ) (ell : ℝ)
    (hf : Tendsto f atTop (nhds ell))
    (hlower : ∀ n, ell ≤ A n)
    (hupper : ∀ n T, A n ≤ f T + err n T)
    (herr : ∀ T, Tendsto (fun n => err n T) atTop (nhds 0)) :
    Tendsto A atTop (nhds ell) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun n => hb.trans_le (hlower n))
  · intro b hb
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hf.eventually_lt_const hb)
    have hFT : f T < b := hT T le_rfl
    have hlim : Tendsto (fun n => f T + err n T) atTop (nhds (f T)) := by
      simpa using (tendsto_const_nhds.add (herr T))
    filter_upwards [hlim.eventually_lt_const hFT] with n hn
    exact (hupper n T).trans_lt hn
