-- Prove2me | solution 1 for InfoBargaining.Monotone.eq1_G_rotation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:33:34.565312+00:00
-- url     : https://prove2.me/submissions/bac88eb5-e780-4e10-b519-25e481a5763e

import Mathlib
import Definitions.Def_InfoBargaining_Monotone_Setting
set_option autoImplicit false
open InfoBargaining.Monotone

theorem solution (M : Model) {α α' : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hα' : α' ∈ Set.Ioo (0 : ℝ) 1) (hle : α ≤ α') (v : ℝ) :
    (v < M.uhat → M.G v α ≤ M.G v α') ∧ (M.uhat < v → M.G v α' ≤ M.G v α) := by
  obtain ⟨h0, -⟩ := hα
  obtain ⟨h0', -⟩ := hα'
  have e : ∀ β : ℝ, 0 < β → (v - (1 - β) * M.uhat) / β = (v - M.uhat) / β + M.uhat := by
    intro β hβ; field_simp; ring
  have hmono := ProbabilityTheory.monotone_cdf M.μ
  unfold InfoBargaining.Monotone.Model.G
  rw [e α h0, e α' h0']
  constructor
  · intro hv
    apply hmono
    have : (v - M.uhat) / α ≤ (v - M.uhat) / α' := by
      have hw : 0 < M.uhat - v := by linarith
      have : (M.uhat - v) / α' ≤ (M.uhat - v) / α := div_le_div_of_nonneg_left hw.le h0 hle
      have e1 : (v - M.uhat) / α = -((M.uhat - v) / α) := by ring
      have e2 : (v - M.uhat) / α' = -((M.uhat - v) / α') := by ring
      rw [e1, e2]; linarith
    linarith
  · intro hv
    apply hmono
    have hw : 0 < v - M.uhat := by linarith
    have : (v - M.uhat) / α' ≤ (v - M.uhat) / α := div_le_div_of_nonneg_left hw.le h0 hle
    linarith
