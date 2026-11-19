-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOccupationStrictBeforeHorizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:27:22.735524+00:00
-- url     : https://prove2.me/submissions/a070ef7a-37e3-4bcf-84d5-9b6989e233b7

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℕ) (ω : Ω)
    (hlocalint : ∀ t : ℝ≥0,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume 0 (t : ℝ))
    (horizon : ℝ≥0)
    (hpositive : ∀ t : ℝ≥0, t < horizon → 0 < Y t ω) :
    ∀ a b : ℝ≥0, a < b → b < horizon →
      branchingOccupation Y a ω < branchingOccupation Y b ω := by
  intro a b hab hb
  let f : ℝ → ℝ := fun s => (Y (Real.toNNReal s) ω : ℝ)
  have h0a : (0 : ℝ) ≤ (a : ℝ) := a.property
  have habr : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have h0b : (0 : ℝ) ≤ (b : ℝ) := b.property
  have hsubset : Set.uIcc (a : ℝ) (b : ℝ) ⊆
      Set.uIcc (0 : ℝ) (b : ℝ) := by
    rw [Set.uIcc_of_le habr.le, Set.uIcc_of_le h0b]
    intro s hs
    exact ⟨h0a.trans hs.1, hs.2⟩
  have hf : IntervalIntegrable f volume (a : ℝ) (b : ℝ) := by
    exact (hlocalint b).mono_set hsubset
  have hge (s : ℝ) (hs : s ∈ Set.Icc (a : ℝ) (b : ℝ)) :
      (1 : ℝ) ≤ f s := by
    have hsle : Real.toNNReal s ≤ b := by
      have hreal : s ≤ (b : ℝ) := hs.2
      simpa only [Real.toNNReal_coe] using
        (Real.toNNReal_le_toNNReal hreal)
    have hst : Real.toNNReal s < horizon := hsle.trans_lt hb
    have hn := hpositive (Real.toNNReal s) hst
    have hnat : 1 ≤ Y (Real.toNNReal s) ω := by omega
    change (1 : ℝ) ≤ (Y (Real.toNNReal s) ω : ℝ)
    exact_mod_cast hnat
  have hpos : 0 < ∫ s in (a : ℝ)..(b : ℝ), f s := by
    have hlo : (b : ℝ) - (a : ℝ) ≤
        ∫ s in (a : ℝ)..(b : ℝ), f s := by
      have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume
          (a : ℝ) (b : ℝ) := intervalIntegrable_const
      calc
        (b : ℝ) - (a : ℝ) =
            ∫ s in (a : ℝ)..(b : ℝ), (1 : ℝ) := by simp
        _ ≤ ∫ s in (a : ℝ)..(b : ℝ), f s :=
          intervalIntegral.integral_mono_on (hab := habr.le)
            (hf := hconst) (hg := hf) hge
    linarith
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hlocalint a) hf
  change (∫ s in (0 : ℝ)..(a : ℝ), f s) <
      ∫ s in (0 : ℝ)..(b : ℝ), f s
  linarith
