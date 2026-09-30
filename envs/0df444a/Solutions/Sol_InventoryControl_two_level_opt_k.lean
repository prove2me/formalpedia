-- Prove2me | solution 1 for InventoryControl.two_level_opt_k
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T05:56:27.089046+00:00
-- url     : https://prove2.me/submissions/789b4837-b7a7-462a-905a-a60d5dd249e8

import Mathlib
import Definitions.Def_InventoryControl_serial

set_option autoImplicit false

open InventoryControl in
theorem ea375955_sq (d A1 A2 e1 e2 : ℝ) (hd : 0 < d) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (he1 : 0 < e1) (he2 : 0 < e2) (k : ℝ) (hk : 0 < k) :
    twoLevelOptCost d A1 A2 e1 e2 k ^ 2
        = 2 * d * (A1 * e1 + A2 * e2 + A1 * e2 * k + A2 * e1 / k) := by
  unfold twoLevelOptCost
  have h1 : 0 ≤ A1 + A2 / k := by positivity
  have h2 : 0 ≤ e1 + k * e2 := by positivity
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  ring

open InventoryControl in
theorem solution (d A1 A2 e1 e2 : ℝ) (hd : 0 < d) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (he1 : 0 < e1) (he2 : 0 < e2) :
    (∀ k : ℝ, 0 < k → twoLevelOptCost d A1 A2 e1 e2 k ^ 2
        = 2 * d * (A1 * e1 + A2 * e2 + A1 * e2 * k + A2 * e1 / k))
      ∧ ConvexOn ℝ (Set.Ioi 0) (fun k => twoLevelOptCost d A1 A2 e1 e2 k ^ 2)
      ∧ ∀ k : ℝ, 0 < k →
          twoLevelOptCost d A1 A2 e1 e2 (Real.sqrt (A2 * e1 / (A1 * e2)))
            ≤ twoLevelOptCost d A1 A2 e1 e2 k := by
  refine ⟨fun k hk => ea375955_sq d A1 A2 e1 e2 hd hA1 hA2 he1 he2 k hk, ?_, ?_⟩
  · have hc : ConvexOn ℝ (Set.Ioi (0:ℝ)) (fun k : ℝ =>
        (2 * d * (A1 * e1 + A2 * e2)) + ((2 * d * (A1 * e2)) • k
          + (2 * d * (A2 * e1)) • k ^ (-1 : ℤ))) := by
      refine (convexOn_const _ (convex_Ioi 0)).add ?_
      refine ((convexOn_id (convex_Ioi 0)).smul (by positivity)).add ?_
      exact (convexOn_zpow (-1)).smul (by positivity)
    refine hc.congr ?_
    intro k hk
    have hk' : (0:ℝ) < k := hk
    simp only [smul_eq_mul, zpow_neg, zpow_one]
    rw [ea375955_sq d A1 A2 e1 e2 hd hA1 hA2 he1 he2 k hk']
    field_simp
    ring
  · intro k hk
    set s := Real.sqrt (A2 * e1 / (A1 * e2)) with hs
    have hq : 0 < A2 * e1 / (A1 * e2) := by positivity
    have hs0 : 0 < s := Real.sqrt_pos.mpr hq
    have hss : s ^ 2 = A2 * e1 / (A1 * e2) := Real.sq_sqrt hq.le
    have hss' : A1 * e2 * s ^ 2 = A2 * e1 := by
      rw [hss]; field_simp
    unfold twoLevelOptCost
    apply Real.sqrt_le_sqrt
    -- reduce to the squared-cost comparison
    have key : A1 * e2 * s + A2 * e1 / s ≤ A1 * e2 * k + A2 * e1 / k := by
      have hks : 0 < k * s := mul_pos hk hs0
      have hAe : 0 < A1 * e2 := by positivity
      have : (A1 * e2 * s + A2 * e1 / s) * (k * s) ≤ (A1 * e2 * k + A2 * e1 / k) * (k * s) := by
        have e1' : (A1 * e2 * s + A2 * e1 / s) * (k * s) = 2 * k * (A2 * e1) := by
          field_simp; nlinarith [hss']
        have e2' : (A1 * e2 * k + A2 * e1 / k) * (k * s) = A1 * e2 * s * (k ^ 2 + s ^ 2) := by
          field_simp; nlinarith [hss']
        rw [e1', e2', ← hss']
        nlinarith [mul_nonneg (mul_nonneg hAe.le hs0.le) (sq_nonneg (k - s))]
      exact le_of_mul_le_mul_right this hks
    have hA : 2 * (A1 + A2 / s) * d * (e1 + s * e2)
        = 2 * d * (A1 * e1 + A2 * e2 + (A1 * e2 * s + A2 * e1 / s)) := by
      field_simp; ring
    have hB : 2 * (A1 + A2 / k) * d * (e1 + k * e2)
        = 2 * d * (A1 * e1 + A2 * e2 + (A1 * e2 * k + A2 * e1 / k)) := by
      field_simp; ring
    rw [hA, hB]
    have h2d : (0:ℝ) ≤ 2 * d := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h2d
