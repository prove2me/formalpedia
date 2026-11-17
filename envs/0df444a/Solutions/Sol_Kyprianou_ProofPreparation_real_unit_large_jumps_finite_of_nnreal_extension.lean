-- Prove2me | solution 1 for Kyprianou.ProofPreparation.real_unit_large_jumps_finite_of_nnreal_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:46:56.134213+00:00
-- url     : https://prove2.me/submissions/8a53b9ba-a88c-47aa-8d59-df46d1eed9f3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_Kyprianou_ProofPreparation_nnreal_coe_tendsto_left
import Theorems.Thm_Kyprianou_ProofPreparation_finite_large_jumps_of_nnreal_cadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false
noncomputable section

theorem solution
    (f : ℝ → ℝ) (Y : ℝ≥0 → ℝ)
    (heq : ∀ u : ℝ≥0, u ≤ 1 → Y u = f (u : ℝ))
    (hR : ∀ u : ℝ≥0, ContinuousWithinAt Y (Set.Ici u) u)
    (hL : ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l))
    (c : ℝ) (hc : 0 < c) :
    Set.Finite {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) ∧ c < |f t - l|} := by
  have hfin := finite_large_jumps_of_nnreal_cadlag Y hR hL 1 c hc
  apply (hfin.image (fun u : ℝ≥0 => (u : ℝ))).subset
  intro t ht
  obtain ⟨⟨ht0, ht1⟩, l, hl, hj⟩ := ht
  let u : ℝ≥0 := ⟨t, le_of_lt ht0⟩
  have hu0 : (0 : ℝ≥0) < u := by exact_mod_cast ht0
  have hu1 : u ≤ (1 : ℝ≥0) := by exact_mod_cast ht1
  have huLeft : Tendsto Y (𝓝[<] u) (𝓝 l) := by
    have htransfer : Tendsto (fun v : ℝ≥0 => f (v : ℝ)) (𝓝[<] u) (𝓝 l) := by
      exact hl.comp (nnreal_coe_tendsto_left u)
    have hsame : Y =ᶠ[𝓝[<] u] (fun v : ℝ≥0 => f (v : ℝ)) := by
      filter_upwards [eventually_mem_nhdsWithin (a := u) (s := Set.Iio u)] with v hv
      exact heq v (le_trans (le_of_lt hv) hu1)
    exact htransfer.congr' hsame.symm
  refine ⟨u, ⟨hu0, hu1, l, huLeft, ?_⟩, rfl⟩
  have huCast : (u : ℝ) = t := rfl
  simpa [heq u hu1, huCast] using hj
