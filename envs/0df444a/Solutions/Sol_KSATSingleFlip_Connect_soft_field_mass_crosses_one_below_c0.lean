-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_mass_crosses_one_below_c0
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:14:21.191224+00:00
-- url     : https://prove2.me/submissions/6a3275b0-7c68-4fd8-be2c-090d0e79ff7b

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_mass_potential_comparison
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_iterates_well_defined
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem solution (γ : ℝ) (hγ : γ < c0) :
    ∃ r : ℕ, 1 < (massM (nuIter γ r)).toReal := by
  by_contra hh
  push_neg at hh
  have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hc1 : c0 ≤ 1 := by unfold c0; nlinarith
  have hδ : 0 < c0-γ := by linarith
  have hlower : ∀ r : ℕ, (r:ℝ)*(c0-γ) ≤ (massM (nuIter γ r)).toReal := by
    intro r
    induction r with
    | zero => simp [nuIter,massM]
    | succ r ih =>
      letI : IsFiniteMeasure (nuIter γ r) := (soft_field_iterates_well_defined γ r).1
      have hp := (soft_field_mass_potential_comparison (nuIter γ r)).1
      have hm := hh r
      have hrec := (soft_field_iterates_well_defined γ r).2.2.2.1
      rw [hrec, ← Real.exp_add]
      have he := Real.add_one_le_exp (-γ + hPot (nuIter γ r))
      have hg : 0 ≤ (1-c0)*(1-(massM (nuIter γ r)).toReal) :=
        mul_nonneg (by linarith) (by linarith)
      push_cast
      nlinarith
  obtain ⟨r,hr⟩ := exists_nat_gt (1/(c0-γ))
  have hr' := (div_lt_iff₀ hδ).mp hr
  have hl := hlower r
  have hu := hh r
  nlinarith
