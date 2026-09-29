-- Prove2me | solution 1 for KontsevichHMS.maslov_add_symm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T20:06:23.937029+00:00
-- url     : https://prove2.me/submissions/abc2ba47-54c1-40e1-914d-a1942a44d04a

import Mathlib
import Definitions.Def_KontsevichHMS_TorusBrane

/-! 6c8c9870 KontsevichHMS.maslov_add_symm: with maslov b₁ b₂ = ⌈α₂ - α₁⌉, the sum is
⌈x⌉ + ⌈-x⌉ = ⌈x⌉ - ⌊x⌋, which is 1 exactly when x = α₂ - α₁ is not an integer. If it were an
integer k, then π α₂ = π α₁ + k π, so the unit direction vectors agree up to the sign (-1)^k,
forcing the integral directions to be parallel, i.e. det2 = 0, contradicting transversality.
No `Theorems.*` module is imported. -/

set_option autoImplicit false

open KontsevichHMS KontsevichHMS.Brane in
theorem solution (b₁ b₂ : Brane) (h : Transverse b₁ b₂) :
    maslov b₁ b₂ + maslov b₂ b₁ = 1 := by
  unfold maslov
  have hneg : b₁.grading - b₂.grading = -(b₂.grading - b₁.grading) := by ring
  rw [hneg, Int.ceil_neg]
  have key : b₂.grading - b₁.grading ∉ Set.range (Int.cast : ℤ → ℝ) := by
    rintro ⟨k, hk⟩
    apply h
    obtain ⟨t₁, ht₁, e₁⟩ := b₁.grading_dir
    obtain ⟨t₂, ht₂, e₂⟩ := b₂.grading_dir
    have hg : Real.pi * b₂.grading = Real.pi * b₁.grading + (k : ℝ) * Real.pi := by
      have : b₂.grading = b₁.grading + (k : ℝ) := by linarith
      rw [this]; ring
    rw [Prod.ext_iff] at e₁ e₂
    simp only [Prod.smul_mk, smul_eq_mul] at e₁ e₂
    obtain ⟨c₁, s₁⟩ := e₁
    obtain ⟨c₂, s₂⟩ := e₂
    rw [hg, Real.cos_add_int_mul_pi] at c₂
    rw [hg, Real.sin_add_int_mul_pi] at s₂
    have hprod : t₁ * t₂ * det2 b₁.dirR b₂.dirR = 0 := by
      unfold det2 dirR
      simp only
      have e : t₁ * t₂ * ((b₁.dir.1 : ℝ) * (b₂.dir.2 : ℝ) - (b₁.dir.2 : ℝ) * (b₂.dir.1 : ℝ))
          = (t₁ * (b₁.dir.1 : ℝ)) * (t₂ * (b₂.dir.2 : ℝ))
            - (t₁ * (b₁.dir.2 : ℝ)) * (t₂ * (b₂.dir.1 : ℝ)) := by ring
      rw [e, ← c₁, ← s₁, ← c₂, ← s₂]
      ring
    rcases mul_eq_zero.mp hprod with h0 | h0
    · exact absurd h0 (mul_ne_zero ht₁ ht₂)
    · exact h0
  rw [(Int.ceil_eq_floor_add_one_iff_notMem _).mpr key]
  ring

