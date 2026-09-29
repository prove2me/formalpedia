-- Prove2me | solution 1 for KerrBlackHoleThermo.evaporatingMass_solves
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T15:56:44.192357+00:00
-- url     : https://prove2.me/submissions/a77ed6e3-3c73-48d6-940e-83c584289054

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

set_option autoImplicit false

open Real

open KerrBlackHoleThermo Real in
theorem solution (M₀ : ℝ) (hM₀ : 0 < M₀) :
    evaporatingMass M₀ 0 = M₀ ∧
    ∀ t : ℝ, t < 256 * π * M₀ ^ 3 →
      HasDerivAt (evaporatingMass M₀)
        (-(768 * π)⁻¹ / evaporatingMass M₀ t ^ 2) t := by
  constructor
  · unfold evaporatingMass
    rw [zero_div, sub_zero, ← Real.rpow_natCast, ← Real.rpow_mul hM₀.le]
    norm_num
  · intro t ht
    have hpi : 0 < π := pi_pos
    have hu : 0 < M₀ ^ 3 - t / (256 * π) := by
      have : t / (256 * π) < M₀ ^ 3 := by
        rw [div_lt_iff₀ (by positivity)]; linarith
      linarith
    have hf : HasDerivAt (fun y : ℝ => M₀ ^ 3 - y / (256 * π)) (-(1 / (256 * π))) t := by
      have := ((hasDerivAt_id t).div_const (256 * π)).const_sub (M₀ ^ 3)
      simpa using this
    have hd := hf.rpow_const (p := (1:ℝ) / 3) (Or.inl hu.ne')
    have hsub : (M₀ ^ 3 - t / (256 * π)) ^ ((1:ℝ) / 3 - 1)
        = (M₀ ^ 3 - t / (256 * π)) ^ ((1:ℝ) / 3) / (M₀ ^ 3 - t / (256 * π)) :=
      Real.rpow_sub_one hu.ne' _
    have hw3 : ((M₀ ^ 3 - t / (256 * π)) ^ ((1:ℝ) / 3)) ^ 3 = M₀ ^ 3 - t / (256 * π) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
    have hw : 0 < (M₀ ^ 3 - t / (256 * π)) ^ ((1:ℝ) / 3) := Real.rpow_pos_of_pos hu _
    rw [hsub] at hd
    have e : evaporatingMass M₀ t = (M₀ ^ 3 - t / (256 * π)) ^ ((1:ℝ) / 3) := rfl
    rw [e]
    show HasDerivAt (fun y : ℝ => (M₀ ^ 3 - y / (256 * π)) ^ ((1:ℝ) / 3)) _ t
    convert hd using 1
    generalize (M₀ ^ 3 - t / (256 * π)) ^ ((1:ℝ) / 3) = w at hw3 hw ⊢
    rw [← hw3]
    field_simp
    ring
