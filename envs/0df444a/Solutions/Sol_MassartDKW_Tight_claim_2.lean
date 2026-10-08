-- Prove2me | solution 1 for MassartDKW.Tight.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:32:50.793931+00:00
-- url     : https://prove2.me/submissions/34152b5d-8075-49a3-9e2e-7026c92c51f7

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic



namespace MassartDKW.Tight

/-- `exp y ≤ 1 + y + (3/4) y²` for `0 ≤ y ≤ 1`. -/
lemma exp_le_quad {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    Real.exp y ≤ 1 + y + 3 / 4 * y ^ 2 := by
  have h := Real.exp_bound' h0 h1 (n := 2) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem claim_1_core : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    (1 + 2 * x) ^ (-(1 / 2 : ℝ)) ≤ (1 - x + 3 * x ^ 2 / 2) * Real.exp (-(0.826 * x ^ 3)) := by
  intro x hx
  obtain ⟨hx0, hx1⟩ := hx
  have hA : 0 < 1 - x + 3 * x ^ 2 / 2 := by nlinarith
  have hy0 : 0 ≤ 0.826 * x ^ 3 := by positivity
  have hx3 : x ^ 3 ≤ 1 := pow_le_one₀ hx0 hx1
  have hy1 : 0.826 * x ^ 3 ≤ 1 := by nlinarith
  have hexp := exp_le_quad hy0 hy1
  have hx6 : x ^ 6 ≤ x ^ 3 := by
    have : x ^ 6 = x ^ 3 * x ^ 3 := by ring
    rw [this]; nlinarith [pow_nonneg hx0 3]
  have hB : 1 + 0.826 * x ^ 3 + 3 / 4 * (0.826 * x ^ 3) ^ 2 ≤ 1 + 1.338 * x ^ 3 := by nlinarith
  have hpos : 0 < 1 + 2 * x := by linarith
  -- rewrite the rpow
  have hr : (1 + 2 * x) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (1 + 2 * x))⁻¹ := by
    rw [Real.rpow_neg hpos.le, Real.sqrt_eq_rpow]
  rw [hr, Real.exp_neg]
  have hs : 0 < Real.sqrt (1 + 2 * x) := Real.sqrt_pos.mpr hpos
  have he : 0 < Real.exp (0.826 * x ^ 3) := Real.exp_pos _
  rw [← div_eq_mul_inv, le_div_iff₀ he, inv_mul_eq_div, div_le_iff₀ hs]
  calc Real.exp (0.826 * x ^ 3) ≤ 1 + 1.338 * x ^ 3 := hexp.trans hB
    _ ≤ (1 - x + 3 * x ^ 2 / 2) * Real.sqrt (1 + 2 * x) := by
        rw [← Real.sqrt_sq hA.le, ← Real.sqrt_mul (sq_nonneg _)]
        apply Real.le_sqrt_of_sq_le
        nlinarith [pow_nonneg hx0 3, mul_nonneg (pow_nonneg hx0 3) (sub_nonneg.mpr hx1),
          mul_nonneg (pow_nonneg hx0 4) (sub_nonneg.mpr hx1), mul_nonneg (pow_nonneg hx0 5) (sub_nonneg.mpr hx1),
          pow_nonneg hx0 4, pow_nonneg hx0 5, pow_nonneg hx0 6]

theorem claim_2_core (n : ℕ) (hn : 1 ≤ n) (ε s' : ℝ) (hε : 0 < ε) (hs' : 0 < s')
    (hnε : 2 ≤ (n : ℝ) * ε) (hns' : 1 ≤ (n : ℝ) * s') (hx : ε ≤ 3 * s') :
    (1 + 2 * ε / (3 * s')) ^ (-(1 / 2 : ℝ)) ≤
      (1 - ε / (3 * s') + ε ^ 2 / (6 * s' ^ 2)) * Real.exp (-(ε ^ 2 * v n s') / (24 * (n : ℝ))) := by
  set x := ε / (3 * s') with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hxdef, div_le_one (by positivity)]; exact hx
  have h1 := claim_1_core x ⟨hx0, hx1⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : 1 - ε / (3 * s') + ε ^ 2 / (6 * s' ^ 2) = 1 - x + 3 * x ^ 2 / 2 := by
    rw [hxdef]; field_simp; ring
  have h2x : 2 * ε / (3 * s') = 2 * x := by rw [hxdef]; ring
  rw [hA, h2x]
  refine h1.trans ?_
  have hApos : 0 < 1 - x + 3 * x ^ 2 / 2 := by nlinarith
  apply mul_le_mul_of_nonneg_left _ hApos.le
  apply Real.exp_le_exp.mpr
  -- need: ε² v / (24 n) ≤ 0.826 x³
  have hd : 0 < s' ^ 2 - 1 / (4 * (n : ℝ) ^ 2) := by
    have : 1 / (4 * (n : ℝ) ^ 2) < s' ^ 2 := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hv : v n s' = (s' * (s' ^ 2 - 1 / (4 * (n : ℝ) ^ 2)))⁻¹ := rfl
  rw [hv, hxdef, neg_div, neg_le_neg_iff]
  set c := 1 / (4 * (n : ℝ) ^ 2) with hc
  have hE1 : ε ^ 2 * (s' * (s' ^ 2 - c))⁻¹ / (24 * (n : ℝ)) = ε ^ 2 * s' ^ 2 / (24 * n * s' ^ 3 * (s' ^ 2 - c)) := by
    field_simp
  have hE2 : 0.826 * (ε / (3 * s')) ^ 3 = 0.826 * ε ^ 3 / (27 * s' ^ 3) := by
    field_simp; ring
  rw [hE1, hE2, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [show 0.826 * ε ^ 3 * (24 * ↑n * s' ^ 3 * (s' ^ 2 - c)) = ε ^ 2 * s' ^ 3 * (0.826 * 24 * (n * ε) * (s' ^ 2 - c)) by ring,
      show ε ^ 2 * s' ^ 2 * (27 * s' ^ 3) = ε ^ 2 * s' ^ 3 * (27 * s' ^ 2) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hn2 : 1 ≤ (n : ℝ) ^ 2 * s' ^ 2 := by nlinarith
  have hq : c ≤ s' ^ 2 / 4 := by
    rw [hc, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hnε hd.le]

theorem claim_3_core (n : ℕ) (hn : 1 ≤ n) (ε s : ℝ) (hε : 0 < ε) (hs : 0 < s)
    (h1 : 1 / (n : ℝ) ≤ ε) (h2 : ε ≤ 3 * s / 2) :
    1 / (12 * (n : ℝ) * s) + ε ^ 2 * v n s / (24 * (n : ℝ)) ≤ (1 + 12 * (n : ℝ) * (s - 2 * ε / 3))⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- scaled variables
  set a := (n : ℝ) * s with ha
  set e := (n : ℝ) * ε with he
  have hapos : 0 < a := by positivity
  have he1 : 1 ≤ e := by rw [div_le_iff₀ hn0] at h1; rw [he, mul_comm]; exact h1
  have hea : e ≤ 3 * a / 2 := by rw [he, ha]; nlinarith
  have ha23 : 2 / 3 ≤ a := by linarith
  have hd : 0 < a ^ 2 - 1 / 4 := by nlinarith
  have hv : v n s = (n : ℝ) ^ 3 / (a * (a ^ 2 - 1 / 4)) := by
    rw [v, ha]; field_simp
  have hL1 : 1 / (12 * (n : ℝ) * s) = 1 / (12 * a) := by rw [ha]; ring
  have hL2 : ε ^ 2 * v n s / (24 * (n : ℝ)) = e ^ 2 / (24 * a * (a ^ 2 - 1 / 4)) := by
    rw [hv, he]; field_simp
  have hR : (1 + 12 * (n : ℝ) * (s - 2 * ε / 3))⁻¹ = 1 / (1 + 12 * a - 8 * e) := by
    rw [ha, he]; ring
  rw [hL1, hL2, hR]
  have hden : 0 < 1 + 12 * a - 8 * e := by linarith
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hden]
  nlinarith [mul_nonneg (sub_nonneg.mpr he1) (sub_nonneg.mpr hea), mul_nonneg hapos.le (sub_nonneg.mpr he1),
    mul_nonneg (mul_nonneg hapos.le hapos.le) (sub_nonneg.mpr hea), mul_nonneg (mul_nonneg hapos.le (sub_nonneg.mpr he1)) (sub_nonneg.mpr hea),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr he1) (sub_nonneg.mpr he1)) (sub_nonneg.mpr hea),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr he1) (sub_nonneg.mpr he1)) hapos.le, sq_nonneg (a - e), sq_nonneg (2*a - e - 1)]

end MassartDKW.Tight

open MassartDKW.Tight


theorem solution (n : ℕ) (hn : 1 ≤ n) (ε s' : ℝ) (hε : 0 < ε) (hs' : 0 < s')
    (hnε : 2 ≤ (n : ℝ) * ε) (hns' : 1 ≤ (n : ℝ) * s') (hx : ε ≤ 3 * s') :
    (1 + 2 * ε / (3 * s')) ^ (-(1 / 2 : ℝ)) ≤
      (1 - ε / (3 * s') + ε ^ 2 / (6 * s' ^ 2)) * Real.exp (-(ε ^ 2 * v n s') / (24 * (n : ℝ))) := by
  exact claim_2_core n hn ε s' hε hs' hnε hns' hx
