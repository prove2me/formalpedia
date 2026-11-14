-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_monotone_iterates_if_order_preserved
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:09:11.858374+00:00
-- url     : https://prove2.me/submissions/8f7d7e18-725b-461c-8bf2-0e07c562501d

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_order_mass_potential_gap
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_iterates_well_defined
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_mass_identity
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect Set
open scoped ENNReal

private theorem order_zero_le (ν : Measure ℝ) : softFieldLE 0 ν := by
  intro ψ hc hconc h0 h1
  have hn : ∀ q ∈ Icc (0:ℝ) 1, 0 ≤ ψ q := by
    intro q hq
    have hh := hconc.2 (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
      (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
      (show 0 ≤ 1-q by linarith [hq.2]) hq.1 (by ring : 1-q+q=1)
    simpa [h0, h1] using hh
  change pairing ψ 0 ≤ pairing ψ ν
  unfold pairing
  simp only [integral_zero_measure]
  apply integral_nonneg
  intro z
  obtain ⟨hq,hq1,_⟩ := soft_field_mass_identity z
  exact mul_nonneg (le_of_lt (Real.cosh_pos z)) (hn _ ⟨le_of_lt hq,le_of_lt hq1⟩)

theorem solution
    (hpres : ∀ (β : ℝ) (ν' ν : Measure ℝ), 0 ≤ β →
      Measure.map (fun z : ℝ => -z) ν' = ν' →
      Measure.map (fun z : ℝ => -z) ν = ν →
      (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν') ≠ ∞ →
      (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞ →
      softFieldLE ν' ν → softFieldLE (Rbeta β ν') (Rbeta β ν))
    (γ : ℝ) : ∀ r : ℕ,
      softFieldLE (nuIter γ r) (nuIter γ (r+1)) ∧
      hPot (nuIter γ r) ≤ hPot (nuIter γ (r+1)) ∧
      ((massM (nuIter γ r)).toReal - hPot (nuIter γ r)) ≤
        ((massM (nuIter γ (r+1))).toReal - hPot (nuIter γ (r+1))) := by
  have horder : ∀ r : ℕ, softFieldLE (nuIter γ r) (nuIter γ (r+1)) := by
    intro r
    induction r with
    | zero =>
      change softFieldLE 0 (nuIter γ 1)
      exact order_zero_le _
    | succ r ih =>
      have h1 := soft_field_iterates_well_defined γ r
      have h2 := soft_field_iterates_well_defined γ (r+1)
      change softFieldLE (Rbeta (Real.exp (-γ)) (nuIter γ r)) (Rbeta (Real.exp (-γ)) (nuIter γ (r+1)))
      exact hpres _ _ _ (le_of_lt (Real.exp_pos _)) h1.2.1 h2.2.1 h1.2.2.1 h2.2.2.1 ih
  intro r
  letI : IsFiniteMeasure (nuIter γ r) := (soft_field_iterates_well_defined γ r).1
  letI : IsFiniteMeasure (nuIter γ (r+1)) := (soft_field_iterates_well_defined γ (r+1)).1
  have hh := soft_field_order_mass_potential_gap _ _ (horder r)
  refine ⟨horder r,?_,?_⟩ <;> linarith
