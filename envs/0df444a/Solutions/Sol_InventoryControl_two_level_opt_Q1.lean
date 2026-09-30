-- Prove2me | solution 1 for InventoryControl.two_level_opt_Q1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T05:24:30.282792+00:00
-- url     : https://prove2.me/submissions/803aeaf2-8e80-4c0f-9859-45cb9bfa94bb

import Mathlib
import Definitions.Def_InventoryControl_serial

open InventoryControl in
theorem eb79ba85_eoq_core (A d h Q : ℝ) (hA : 0 < A) (hd : 0 < d) (hh : 0 < h) (hQ : 0 < Q) :
    eoqCost A d h (eoq A d h) ≤ eoqCost A d h Q ∧
      eoqCost A d h (eoq A d h) = Real.sqrt (2 * A * d * h) := by
  set c := Real.sqrt (2 * A * d * h) with hc
  have hcpos : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = 2 * A * d * h := Real.sq_sqrt (by positivity)
  have hs : eoq A d h = c / h := by
    unfold eoq
    rw [show 2 * A * d / h = (c / h) ^ 2 by rw [div_pow, hc2]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hval : eoqCost A d h (eoq A d h) = c := by
    rw [hs]
    unfold eoqCost
    field_simp
    nlinarith [hc2]
  refine ⟨?_, hval⟩
  rw [hval]
  unfold eoqCost
  rw [← sub_nonneg]
  have key : Q / 2 * h + d / Q * A - c = (h * Q - c) ^ 2 / (2 * h * Q) := by
    field_simp
    nlinarith [hc2]
  rw [key]
  positivity

open InventoryControl in
theorem solution (d A1 A2 e1 e2 k Q1 : ℝ) (hd : 0 < d) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (he1 : 0 < e1) (he2 : 0 < e2) (hk : 0 < k) (hQ : 0 < Q1) :
    twoLevelCost d A1 A2 e1 e2 (eoq (A1 + A2 / k) d (e1 + k * e2)) k
        ≤ twoLevelCost d A1 A2 e1 e2 Q1 k
      ∧ twoLevelCost d A1 A2 e1 e2 (eoq (A1 + A2 / k) d (e1 + k * e2)) k
          = twoLevelOptCost d A1 A2 e1 e2 k := by
  have hA : 0 < A1 + A2 / k := by positivity
  have hh : 0 < e1 + k * e2 := by positivity
  obtain ⟨h1, h2⟩ := eb79ba85_eoq_core (A1 + A2 / k) d (e1 + k * e2) Q1 hA hd hh hQ
  exact ⟨h1, h2⟩

#print axioms solution
