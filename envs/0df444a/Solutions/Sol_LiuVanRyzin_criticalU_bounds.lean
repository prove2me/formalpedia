-- Prove2me | solution 1 for LiuVanRyzin.criticalU_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:32:14.107039+00:00
-- url     : https://prove2.me/submissions/e647bb95-65fd-4d3a-be36-a1a8d4b5b3a6

import Mathlib
import Definitions.Def_LiuVanRyzin_PowerModel

set_option autoImplicit false

open LiuVanRyzin in
theorem solution (p₁ p₂ α γ : ℝ) (hα : α < p₂) (hp : p₂ < p₁)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictAntiOn (criticalU p₁ p₂ α γ) (Set.Ioi p₁) ∧
      ∀ v₀ : ℝ, p₁ < v₀ → focLHS p₁ p₂ α γ v₀ = 0 →
        v₀ < p₁ + γ * (p₂ - α) ∧
          p₁ + γ * (p₂ - α) < criticalU p₁ p₂ α γ v₀ ∧
          criticalU p₁ p₂ α γ v₀ < p₁ + p₂ - α := by
  have hb : 0 < p₂ - α := by linarith
  have ha : 0 < p₁ - α := by linarith
  have hd : 0 < p₁ - p₂ := by linarith
  have hg : 0 < 1 - γ := by linarith
  have hgd : 0 < γ * (p₁ - p₂) := mul_pos hγ0 hd
  refine ⟨?_, ?_⟩
  · intro w₁ hw₁ w₂ hw₂ hlt
    simp only [Set.mem_Ioi] at hw₁ hw₂
    unfold criticalU
    have hD1 : 0 < w₁ - p₁ + γ * (p₁ - p₂) := by linarith
    have hD2 : 0 < w₂ - p₁ + γ * (p₁ - p₂) := by linarith
    rw [div_lt_div_iff₀ hD2 hD1]
    have key : 0 < γ * (p₁ - α) * (p₁ - p₂) * (1 - γ) * (w₂ - w₁) :=
      mul_pos (mul_pos (mul_pos (mul_pos hγ0 ha) hd) hg) (by linarith)
    rw [← sub_pos]
    exact key.trans_eq (by ring)
  · intro v₀ hv hfoc
    have hlt : v₀ < p₁ + γ * (p₂ - α) := by
      by_contra hge
      push Not at hge
      have ht : 0 < v₀ - p₁ := by linarith
      have hs : 0 < v₀ - p₂ := by linarith
      have hx0 : 0 ≤ (v₀ - p₁) / (v₀ - p₂) := div_nonneg ht.le hs.le
      have hx1 : (v₀ - p₁) / (v₀ - p₂) < 1 := by
        rw [div_lt_one hs]; linarith
      have hq : fillRate p₁ p₂ γ v₀ < 1 := Real.rpow_lt_one hx0 hx1 hγ0
      have hF : 0 < 1 + γ * (p₁ - p₂) / (v₀ - p₁) := by
        have := div_pos hgd ht
        linarith
      have hF2 : 1 + γ * (p₁ - p₂) / (v₀ - p₁) ≤ (p₁ - α) / (p₂ - α) := by
        rw [add_div' _ _ _ ht.ne', div_le_div_iff₀ ht hb]
        nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hge)]
      unfold focLHS at hfoc
      have hm := mul_lt_mul_of_pos_right hq hF
      rw [one_mul] at hm
      linarith
    have hD : 0 < v₀ - p₁ + γ * (p₁ - p₂) := by linarith
    refine ⟨hlt, ?_, ?_⟩
    · unfold criticalU
      rw [lt_div_iff₀ hD]
      have key : 0 < (p₁ - p₂) * (1 - γ) * (p₁ + γ * (p₂ - α) - v₀) :=
        mul_pos (mul_pos hd hg) (by linarith)
      rw [← sub_pos]
      exact key.trans_eq (by ring)
    · unfold criticalU
      rw [div_lt_iff₀ hD]
      have key : 0 < (p₁ - α) * (1 - γ) * (v₀ - p₁) :=
        mul_pos (mul_pos ha hg) (by linarith)
      rw [← sub_pos]
      exact key.trans_eq (by ring)

#print axioms solution
