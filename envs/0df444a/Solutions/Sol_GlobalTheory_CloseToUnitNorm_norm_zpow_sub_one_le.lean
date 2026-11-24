-- Prove2me | solution 1 for GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T01:45:06.914385+00:00
-- url     : https://prove2.me/submissions/48c31bf5-0185-4e76-8da9-8db07d3b4738

import Mathlib


theorem solution {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - (1 : C)‖ < (1 : ℝ)) (i : ℤ) : ‖u ^ i - (1 : C)‖ ≤ ‖u - (1 : C)‖ := by
  have a := IsUltrametricDist.norm_add_le_max (u-1) (1:C)
  have b := IsUltrametricDist.norm_add_le_max (1-u) u
  rw [sub_add_cancel,norm_one] at a
  rw [sub_add_cancel,norm_one,norm_sub_rev (1:C) u] at b
  have hu : ‖u‖ = 1 := le_antisymm (a.trans (max_le h.le le_rfl)) (by rcases le_max_iff.mp b with bad|good <;> linarith)
  have ne : u ≠ 0 := by intro e; simp [e] at hu
  have natB (v : C) (hv : ‖v‖ = 1) (k : ℕ) : ‖v^k-1‖ ≤ ‖v-1‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show v^(k+1)-1 = (v^k-1)*v + (v-1) by ring]
      apply (IsUltrametricDist.norm_add_le_max _ _).trans
      simpa [norm_mul,hv] using max_le ih le_rfl
  cases i with
  | ofNat n => simpa using natB u hu n
  | negSucc n =>
    have hv : ‖u⁻¹‖ = 1 := by simp [hu]
    have e : ‖u⁻¹-1‖ = ‖u-1‖ := by
      rw [show u⁻¹-1 = (1-u)*u⁻¹ by field_simp]; simp [norm_mul,hv,norm_sub_rev]
    simpa [zpow_negSucc,inv_pow,e] using (natB u⁻¹ hv (n+1)).trans e.le
