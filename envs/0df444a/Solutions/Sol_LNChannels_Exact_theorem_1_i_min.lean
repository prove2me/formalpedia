-- Prove2me | solution 1 for LNChannels.Exact.theorem_1_i_min
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:11:00.952345+00:00
-- url     : https://prove2.me/submissions/1c70f34f-9b0d-42a9-bfb5-c9eda3f6dfd8

import Mathlib
import Definitions.Def_LNChannels_Exact_uniCost

set_option autoImplicit false
open LNChannels.Exact

namespace LNMinHelp

lemma alg (k q y : ℝ) (hq1 : 1 < q) (hy : 1 < y) (hqk : (q - 1) ^ 2 = k * q) :
    0 ≤ (1 - q / y) + k / (y - 1) - k / (q - 1) := by
  have hq0 : 0 < q := by linarith
  have hk : k = (q - 1) ^ 2 / q := by field_simp; linarith
  have h1 : y - 1 ≠ 0 := by linarith
  have h2 : q - 1 ≠ 0 := by linarith
  have h3 : y ≠ 0 := by linarith
  have : (1 - q / y) + k / (y - 1) - k / (q - 1) = (y - q) ^ 2 / (y * q * (y - 1)) := by
    rw [hk]
    field_simp
    ring
  rw [this]
  have : 0 < y - 1 := by linarith
  positivity

end LNMinHelp

theorem solution (lam₂ r B : ℝ) (hB : 0 < B) (hlam₂ : 0 < lam₂) (hr : 0 < r) :
    let k := B * Real.log (1 + r / lam₂)
    let copt := B / (2 * k) * (-k + Real.sqrt (k * (k + 4))
      + 2 * Real.log ((1 / 2) * (k + Real.sqrt (k * (k + 4)) + 2)))
    let lstar := B / k * Real.log ((1 / 2) * (k + Real.sqrt (k * (k + 4)) + 2))
    IsLeast (uniCost lam₂ r B '' Set.Ioi 0) copt ∧ 0 < lstar ∧
      uniCost lam₂ r B lstar = copt := by
  intro k copt lstar
  have hρ : 1 < 1 + r / lam₂ := by
    have : 0 < r / lam₂ := by positivity
    linarith
  have hlogρ : 0 < Real.log (1 + r / lam₂) := Real.log_pos hρ
  have hk : 0 < k := mul_pos hB hlogρ
  have hρeq : (r + lam₂) / lam₂ = 1 + r / lam₂ := by field_simp; ring
  obtain ⟨D, hDdef⟩ : ∃ D, D = Real.sqrt (k * (k + 4)) := ⟨_, rfl⟩
  have hD2 : D ^ 2 = k * (k + 4) := by rw [hDdef]; exact Real.sq_sqrt (by positivity)
  have hDpos : 0 < D := by rw [hDdef]; exact Real.sqrt_pos.2 (by positivity)
  obtain ⟨q, hqdef⟩ : ∃ q, q = (1 / 2) * (k + D + 2) := ⟨_, rfl⟩
  have hq1 : 1 < q := by rw [hqdef]; linarith
  have hqk : (q - 1) ^ 2 = k * q := by
    rw [hqdef]; linear_combination (1 / 4) * hD2
  have hkq : k / (q - 1) = (D - k) / 2 := by
    rw [div_eq_iff (by linarith)]
    rw [hqdef]; linear_combination (-1 / 4) * hD2
  have hcopt : copt = B / k * (Real.log q + (D - k) / 2) := by
    simp only [copt]
    rw [← hDdef, ← hqdef]
    field_simp
    ring
  have hlstar : lstar = B / k * Real.log q := by
    simp only [lstar]
    rw [← hDdef, ← hqdef]
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hlstar_pos : 0 < lstar := by rw [hlstar]; positivity
  have hq0 : 0 < q := by linarith
  have hlogρ' : Real.log (1 + r / lam₂) = k / B := by
    simp only [k]; field_simp
  have hcost : ∀ m : ℝ, 0 < m → uniCost lam₂ r B m =
      B / k * (Real.log ((1 + r / lam₂) ^ m) + k / ((1 + r / lam₂) ^ m - 1)) := by
    intro m hm
    have hy : 1 < (1 + r / lam₂) ^ m := Real.one_lt_rpow hρ hm
    have hy1 : (1 + r / lam₂) ^ m - 1 ≠ 0 := by linarith
    unfold uniCost
    rw [hρeq, Real.log_rpow (by linarith), hlogρ']
    field_simp
  have hlow : ∀ m : ℝ, 0 < m → copt ≤ uniCost lam₂ r B m := by
    intro m hm
    have hy : 1 < (1 + r / lam₂) ^ m := Real.one_lt_rpow hρ hm
    rw [hcost m hm, hcopt]
    generalize (1 + r / lam₂) ^ m = y at hy ⊢
    have hy0 : 0 < y := by linarith
    have h1 : 1 - q / y ≤ Real.log y - Real.log q := by
      have := Real.one_sub_inv_le_log_of_pos (show 0 < y / q by positivity)
      rwa [Real.log_div hy0.ne' hq0.ne', inv_div] at this
    have h2 := LNMinHelp.alg k q y hq1 hy hqk
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hy_star : (1 + r / lam₂) ^ lstar = q := by
    have hpos : 0 < (1 + r / lam₂) ^ lstar := Real.rpow_pos_of_pos (by linarith) _
    apply Real.log_injOn_pos (Set.mem_Ioi.2 hpos) (Set.mem_Ioi.2 hq0)
    rw [Real.log_rpow (by linarith), hlogρ', hlstar]
    field_simp
  have heq : uniCost lam₂ r B lstar = copt := by
    rw [hcost lstar hlstar_pos, hy_star, hkq, hcopt]
  refine ⟨⟨⟨lstar, hlstar_pos, heq⟩, ?_⟩, hlstar_pos, heq⟩
  rintro _ ⟨m, hm, rfl⟩
  exact hlow m hm
