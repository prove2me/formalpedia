-- Prove2me | solution 1 for Kyprianou.ProofPreparation.nnreal_clipped_left_limit_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:47:04.831628+00:00
-- url     : https://prove2.me/submissions/09b31f38-d78a-4473-9f65-2ee877f5bdc7

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_nnreal_coe_tendsto_left
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false
noncomputable section

theorem solution
    (f : ℝ → ℝ)
    (hL : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) :
    ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => f (min (v : ℝ) 1))
        (𝓝[<] u) (𝓝 l) := by
  intro u hu
  by_cases hle : u ≤ (1 : ℝ≥0)
  · have ht : (u : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
      constructor
      · exact_mod_cast hu
      · exact_mod_cast hle
    obtain ⟨l, hl⟩ := hL (u : ℝ) ht
    refine ⟨l, ?_⟩
    have htrans : Tendsto (fun v : ℝ≥0 => f (v : ℝ)) (𝓝[<] u) (𝓝 l) :=
      hl.comp (nnreal_coe_tendsto_left u)
    have hsame :
        (fun v : ℝ≥0 => f (min (v : ℝ) 1)) =ᶠ[𝓝[<] u]
          (fun v : ℝ≥0 => f (v : ℝ)) := by
      filter_upwards [eventually_mem_nhdsWithin (a := u) (s := Set.Iio u)] with v hv
      have hv1 : v ≤ (1 : ℝ≥0) := le_trans (le_of_lt hv) hle
      have hvReal : (v : ℝ) ≤ 1 := by exact_mod_cast hv1
      simp only [min_eq_left hvReal]
    exact htrans.congr' hsame.symm
  · have hgt : (1 : ℝ≥0) < u := lt_of_not_ge hle
    refine ⟨f 1, ?_⟩
    have hnear : Set.Ioi (1 : ℝ≥0) ∈ 𝓝[<] u := by
      apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      exact ⟨Set.Ioi 1, Ioi_mem_nhds hgt, Set.inter_subset_left⟩
    have hsame :
        (fun v : ℝ≥0 => f (min (v : ℝ) 1)) =ᶠ[𝓝[<] u]
          (fun _ : ℝ≥0 => f 1) := by
      filter_upwards [hnear] with v hv
      have hvReal : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast (le_of_lt hv)
      simp only [min_eq_right hvReal]
    exact tendsto_const_nhds.congr' hsame.symm
