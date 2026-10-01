-- Prove2me | solution 1 for MurtyKabadi.Reduction.lemma2_optimum_gap
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T09:07:30.873159+00:00
-- url     : https://prove2.me/submissions/bf24ffa6-b0a1-4161-9c87-5f22afcb1fc0

import Theorems.Thm_MurtyKabadi_Reduction_box_minimum_integer_minor_certificate
import Theorems.Thm_MurtyKabadi_Reduction_principal_minor_abs_le_encoding

open MurtyKabadi.Reduction

private lemma negative_integer_quotient_gap (q : ℝ) (k a : ℤ) (L : ℕ)
    (hq : q < 0) (hk : k ≠ 0) (ha : q * (k : ℝ) = (a : ℝ))
    (hbound : |k| ≤ (2 : ℤ) ^ L) :
    q ≤ -((2 : ℝ) ^ (-(L : ℤ))) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have ha' : (a : ℝ) ≠ 0 := by
    rw [← ha]
    exact mul_ne_zero (ne_of_lt hq) hk'
  have ha0 : a ≠ 0 := by exact_mod_cast ha'
  have ha1 : (1 : ℤ) ≤ |a| := by
    have := abs_pos.mpr ha0
    omega
  have ha1' : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast ha1
  have habs : (-q) * |(k : ℝ)| = |(a : ℝ)| := by
    simpa only [abs_mul, abs_of_neg hq] using congrArg abs ha
  have hbound' : |(k : ℝ)| ≤ (2 : ℝ) ^ L := by exact_mod_cast hbound
  have hprod : (1 : ℝ) ≤ (-q) * (2 : ℝ) ^ L := by
    calc
      1 ≤ |(a : ℝ)| := ha1'
      _ = (-q) * |(k : ℝ)| := habs.symm
      _ ≤ (-q) * (2 : ℝ) ^ L := mul_le_mul_of_nonneg_left hbound' (by linarith)
  have hdiv : (1 : ℝ) / (2 : ℝ) ^ L ≤ -q :=
    (div_le_iff₀ (by positivity)).mpr hprod
  rw [zpow_neg, zpow_natCast, ← one_div]
  linarith

theorem solution {m : ℕ} (D : Matrix (Fin m) (Fin m) ℤ) (hD : D.IsSymm) :
    (∀ x : Fin m → ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ Q (D.map (Int.cast : ℤ → ℝ)) x) ∨
    ∃ x : Fin m → ℝ, 0 ≤ x ∧ x ≤ 1 ∧
      Q (D.map (Int.cast : ℤ → ℝ)) x ≤ -((2 : ℝ) ^ (-(encSize D : ℤ))) := by
  classical
  by_cases hall : ∀ x : Fin m → ℝ, 0 ≤ x → x ≤ 1 →
      0 ≤ Q (D.map (Int.cast : ℤ → ℝ)) x
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨z, hz0, hz1, hzneg⟩ := hall
  have hcont : Continuous (Q (D.map (Int.cast : ℤ → ℝ))) := by
    unfold Q Matrix.mulVec dotProduct
    fun_prop
  have hnonempty : (Set.Icc (0 : Fin m → ℝ) 1).Nonempty :=
    ⟨0, le_rfl, zero_le_one⟩
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn hnonempty hcont.continuousOn
  have hqneg : Q (D.map (Int.cast : ℤ → ℝ)) x < 0 :=
    lt_of_le_of_lt (hmin ⟨hz0, hz1⟩) hzneg
  obtain ⟨S, hk, a, ha⟩ := box_minimum_integer_minor_certificate D hD x hx.1 hx.2
    (fun z hz0 hz1 => hmin ⟨hz0, hz1⟩)
  exact ⟨x, hx.1, hx.2, negative_integer_quotient_gap _ _ _ _ hqneg hk ha
    (principal_minor_abs_le_encoding D S)⟩
