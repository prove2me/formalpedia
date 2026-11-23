-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.rationalLowerEnvelopeAEMembershipOnSupport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:11:03.285112+00:00
-- url     : https://prove2.me/submissions/b548e786-b7f5-450a-bb65-af1db9c9f19a

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Ω → ℝ) (A B : ℝ → Set Ω)
    (hMeas : ∀ h : ℝ, NullMeasurableSet (A h) P)
    (hMono : Monotone A)
    (hMargin : ∀ y : ℝ, ∀ᵐ ω ∂P,
      g ω ≠ 0 → ω ∈ A y →
        ∃ h : ℝ, h < y ∧ ω ∈ A h)
    (hBDef : ∀ y : ℝ, ∀ ω : Ω,
      ω ∈ B y ↔
        ∃ r : ℚ, (r : ℝ) < y ∧
          ω ∈ toMeasurable P (A (r : ℝ))) :
    ∀ y : ℝ, ∀ᵐ ω ∂P,
      g ω ≠ 0 → (ω ∈ B y ↔ ω ∈ A y) := by
  classical
  have hRat : ∀ᵐ ω ∂P, ∀ r : ℚ,
      (ω ∈ toMeasurable P (A (r : ℝ)) ↔ ω ∈ A (r : ℝ)) := by
    rw [ae_all_iff]
    intro r
    filter_upwards [(hMeas (r : ℝ)).toMeasurable_ae_eq] with ω hω
    change (toMeasurable P (A (r : ℝ))) ω ↔ (A (r : ℝ)) ω
    exact ⟨Eq.mp hω, Eq.mpr hω⟩
  intro y
  filter_upwards [hRat, hMargin y] with ω hRatω hMarginω
  intro hg
  constructor
  · intro hBy
    obtain ⟨r, hry, hrM⟩ := (hBDef y ω).mp hBy
    exact hMono (le_of_lt hry) ((hRatω r).mp hrM)
  · intro hAy
    obtain ⟨h, hhy, hAh⟩ := hMarginω hg hAy
    obtain ⟨r, hhr, hry⟩ := exists_rat_btwn hhy
    exact (hBDef y ω).mpr ⟨r, hry,
      (hRatω r).mpr (hMono (le_of_lt hhr) hAh)⟩
