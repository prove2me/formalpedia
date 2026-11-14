-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_threshold_partial
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:02:59.881624+00:00
-- url     : https://prove2.me/submissions/2acf5e9e-496d-443c-8120-1b1cdae155ae

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_mass_potential_comparison
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_iterates_well_defined
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_nonpositive_gamma_step
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

private theorem bounded_mass (γ : ℝ) (hγ : 1 ≤ γ) :
    ∀ r : ℕ, (massM (nuIter γ r)).toReal ≤ 1 := by
  intro r
  induction r with
  | zero => simp [nuIter, massM]
  | succ r ih =>
    letI : IsFiniteMeasure (nuIter γ r) := (soft_field_iterates_well_defined γ r).1
    have hpot := (soft_field_mass_potential_comparison (nuIter γ r)).2
    have hrec := (soft_field_iterates_well_defined γ r).2.2.2.1
    rw [hrec, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    linarith

private theorem growing_mass (γ : ℝ) (hγ : γ ≤ 0) :
    ∀ r : ℕ, (r : ℝ)/2 ≤ (massM (nuIter γ r)).toReal := by
  intro r
  induction r with
  | zero => simp [nuIter, massM]
  | succ r ih =>
    letI : IsFiniteMeasure (nuIter γ r) := (soft_field_iterates_well_defined γ r).1
    have hpot := (soft_field_mass_potential_comparison (nuIter γ r)).1
    have hrec := (soft_field_iterates_well_defined γ r).2.2.2.1
    have hstep := soft_field_nonpositive_gamma_step (massM (nuIter γ r)).toReal (hPot (nuIter γ r)) γ ENNReal.toReal_nonneg hpot hγ
    rw [hrec]
    push_cast
    linarith

theorem solution :
    (∀ γ : ℝ, 1 ≤ γ → (⨆ r : ℕ, mIter γ r) < ∞) ∧
    (∀ γ : ℝ, γ ≤ 0 → (⨆ r : ℕ, mIter γ r) = ∞) ∧
    0 ≤ gammaStar ∧ gammaStar ≤ 1 := by
  have hb : ∀ γ : ℝ, 1 ≤ γ → (⨆ r : ℕ, mIter γ r) < ∞ := by
    intro γ hγ
    apply lt_of_le_of_lt _ ENNReal.one_lt_top
    apply iSup_le
    intro r
    letI : IsFiniteMeasure (nuIter γ r) := (soft_field_iterates_well_defined γ r).1
    have hfinite : massM (nuIter γ r) ≠ ∞ := measure_ne_top (nuIter γ r) Set.univ
    have hh := bounded_mass γ hγ r
    change massM (nuIter γ r) ≤ 1
    apply (ENNReal.toReal_le_toReal hfinite ENNReal.one_ne_top).mp
    simpa using hh
  have hg : ∀ γ : ℝ, γ ≤ 0 → (⨆ r : ℕ, mIter γ r) = ∞ := by
    intro γ hγ
    by_contra hh
    have hf : (⨆ r : ℕ, mIter γ r) ≠ ∞ := hh
    obtain ⟨r,hr⟩ := exists_nat_gt (2*((⨆ r : ℕ, mIter γ r).toReal))
    have hlo := growing_mass γ hγ r
    have hhi : (massM (nuIter γ r)).toReal ≤ ((⨆ r : ℕ, mIter γ r).toReal) :=
      ENNReal.toReal_mono hf (le_iSup (mIter γ) r)
    linarith
  refine ⟨hb,hg,?_,?_⟩
  · unfold gammaStar
    apply le_csInf
    · exact ⟨1,hb 1 le_rfl⟩
    · intro γ hγ
      by_contra hn
      have hneg : γ ≤ 0 := le_of_lt (lt_of_not_ge hn)
      have := hg γ hneg
      change (⨆ r : ℕ, mIter γ r) < ∞ at hγ
      rw [this] at hγ
      exact lt_irrefl _ hγ
  · unfold gammaStar
    apply csInf_le
    · refine ⟨0,?_⟩
      intro γ hγ
      by_contra hn
      have hneg : γ ≤ 0 := le_of_lt (lt_of_not_ge hn)
      have := hg γ hneg
      change (⨆ r : ℕ, mIter γ r) < ∞ at hγ
      rw [this] at hγ
      exact lt_irrefl _ hγ
    · exact hb 1 le_rfl
