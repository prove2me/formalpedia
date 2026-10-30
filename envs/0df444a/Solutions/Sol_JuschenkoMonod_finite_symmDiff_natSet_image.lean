-- Prove2me | solution 1 for JuschenkoMonod.finite_symmDiff_natSet_image
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:37:15.899728+00:00
-- url     : https://prove2.me/submissions/7fc6c56c-6007-45fd-8581-838e22c76e6b

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem finite_symmDiff_natSet_image_dev (g : Equiv.Perm ℤ) (hg : g ∈ IntervalExchange.wobbling ℤ) :
    (symmDiff natSet (g '' natSet)).Finite := by
  obtain ⟨C, hC⟩ := hg
  obtain ⟨N, hN⟩ := exists_nat_ge C
  have hb : ∀ y : ℤ, |g y - y| ≤ N := fun y => by
    have h1 := hC y
    rw [Int.dist_eq] at h1
    have h2 : (|g y - y| : ℤ) ≤ (N : ℤ) := by
      have : ((|g y - y| : ℤ) : ℝ) ≤ (N : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact h2
  refine (Set.finite_Icc (-(N : ℤ) - 1) (N : ℤ)).subset ?_
  intro x hx
  have hxmem : ∀ y : ℤ, g y = x → y ∈ natSet → x ∈ g '' natSet := fun y h hy => ⟨y, hy, h⟩
  simp only [Set.mem_Icc]
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- x ∈ ℕ, x ∉ g '' ℕ
    obtain ⟨n, rfl⟩ := h1
    refine ⟨by omega, ?_⟩
    by_contra hlt
    push Not at hlt
    -- preimage y = g⁻¹ x ≥ 0 would put x in image
    have hy : (g.symm (n : ℤ)) < 0 := by
      by_contra hy
      push Not at hy
      exact h2 ⟨g.symm n, ⟨(g.symm n).toNat, by simp [Int.toNat_of_nonneg hy]⟩, by simp⟩
    have := hb (g.symm n)
    rw [abs_le] at this
    simp at this
    omega
  · obtain ⟨⟨y, hy, rfl⟩, h2⟩ := (⟨h1, h2⟩ : x ∈ g '' natSet ∧ x ∉ natSet)
    obtain ⟨m, rfl⟩ := hy
    have := hb (m : ℤ)
    rw [abs_le] at this
    have hx : g (m : ℤ) < 0 := by
      by_contra hx; push Not at hx
      exact h2 ⟨(g m).toNat, by simp [Int.toNat_of_nonneg hx]⟩
    omega

end JuschenkoMonod

theorem solution : type_of% @JuschenkoMonod.finite_symmDiff_natSet_image_dev := @JuschenkoMonod.finite_symmDiff_natSet_image_dev
