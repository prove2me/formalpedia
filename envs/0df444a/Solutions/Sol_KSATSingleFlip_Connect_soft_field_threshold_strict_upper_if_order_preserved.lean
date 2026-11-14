-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_threshold_strict_upper_if_order_preserved
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:14:20.18955+00:00
-- url     : https://prove2.me/submissions/41475165-333c-4a31-b7e7-3b9d0d70a6cd

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_iterates_well_defined
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_threshold_partial
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_first_iterate
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_monotone_iterates_if_order_preserved
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem solution
    (hpres : ∀ (β : ℝ) (ν' ν : Measure ℝ), 0 ≤ β →
      Measure.map (fun z : ℝ => -z) ν' = ν' →
      Measure.map (fun z : ℝ => -z) ν = ν →
      (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν') ≠ ∞ →
      (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞ →
      softFieldLE ν' ν → softFieldLE (Rbeta β ν') (Rbeta β ν)) :
    gammaStar ≤ 1 - (1-c0)*Real.exp (-1)/2 ∧ gammaStar < 1 := by
  have hgap : ∀ (γ : ℝ) (r : ℕ), 1 ≤ r →
      (1-c0)*Real.exp (-γ) ≤ (massM (nuIter γ r)).toReal - hPot (nuIter γ r) := by
    intro γ r hr
    have hm : Monotone (fun j : ℕ => (massM (nuIter γ j)).toReal - hPot (nuIter γ j)) := by
      apply monotone_nat_of_le_succ
      intro j
      exact (soft_field_monotone_iterates_if_order_preserved hpres γ j).2.2
    have he := soft_field_first_iterate γ
    have hfirst : (massM (nuIter γ 1)).toReal - hPot (nuIter γ 1) = (1-c0)*Real.exp (-γ) := by
      rw [he.2.1, he.2.2]
      ring
    rw [← hfirst]
    exact hm hr
  have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 ≤ c0 := by unfold c0; nlinarith
  have hc1 : c0 < 1 := by unfold c0; nlinarith
  let d : ℝ := (1-c0)*Real.exp (-1)
  have hd : 0 < d := mul_pos (by linarith) (Real.exp_pos _)
  have hde : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hd1 : d ≤ 1 := by
    dsimp [d]
    nlinarith [mul_nonneg (show 0 ≤ c0 by exact hc0) (le_of_lt (Real.exp_pos (-1)))]
  let γ : ℝ := 1-d/2
  have hγ0 : 0 ≤ γ := by dsimp [γ]; linarith
  have hγ1 : γ ≤ 1 := by dsimp [γ]; linarith
  have hdγ : d ≤ (1-c0)*Real.exp (-γ) := by
    dsimp [d]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Real.exp_le_exp.mpr
    linarith
  have hb : ∀ r : ℕ, (massM (nuIter γ r)).toReal ≤ 1 := by
    intro r
    induction r with
    | zero => simp [nuIter,massM]
    | succ r ih =>
      have hrec := (soft_field_iterates_well_defined γ r).2.2.2.1
      rw [hrec, ← Real.exp_add]
      apply Real.exp_le_one_iff.mpr
      cases r with
      | zero =>
        have hz : hPot (nuIter γ 0) = 0 := by simp [nuIter,hPot,pairing]
        rw [hz]
        linarith
      | succ r =>
        have hh := hgap γ (r+1) (by omega)
        dsimp [γ] at *
        linarith
  have hsup : (⨆ r : ℕ, mIter γ r) < ∞ := by
    apply lt_of_le_of_lt _ ENNReal.one_lt_top
    apply iSup_le
    intro r
    letI : IsFiniteMeasure (nuIter γ r) := (soft_field_iterates_well_defined γ r).1
    have hf : massM (nuIter γ r) ≠ ∞ := measure_ne_top (nuIter γ r) Set.univ
    change massM (nuIter γ r) ≤ 1
    apply (ENNReal.toReal_le_toReal hf ENNReal.one_ne_top).mp
    simpa using hb r
  have hlow : BddBelow {γ : ℝ | (⨆ r : ℕ, mIter γ r) < ∞} := by
    refine ⟨0,?_⟩
    intro x hx
    by_contra hn
    have hxneg : x ≤ 0 := le_of_lt (lt_of_not_ge hn)
    have hbad := (soft_field_threshold_partial.2.1 x hxneg)
    change (⨆ r : ℕ, mIter x r) < ∞ at hx
    rw [hbad] at hx
    exact lt_irrefl _ hx
  have hsinf : gammaStar ≤ γ := csInf_le hlow hsup
  constructor
  · exact hsinf
  · dsimp [γ] at hsinf
    linarith
