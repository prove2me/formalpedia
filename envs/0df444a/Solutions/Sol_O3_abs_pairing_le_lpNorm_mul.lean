-- Prove2me | solution 1 for O3.abs_pairing_le_lpNorm_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:01:17.931217+00:00
-- url     : https://prove2.me/submissions/93717688-15db-4491-918b-263139b21af1

import Mathlib
import Definitions.Def_O3_Geometry
import Theorems.Thm_O3_lpNorm_nonneg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
import Theorems.Thm_O3_pairing_le_lpNorm_mul
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p q : ℝ} (hpq : p.HolderConjugate q)
    {d : ℕ} (x y : Point d) :
    |pairing x y| ≤ lpNorm p x * lpNorm q y := by
  rw [abs_le]
  constructor
  · have h := pairing_le_lpNorm_mul hpq (-x) y
    have hB : 0 ≤ lpNorm p x * lpNorm q y :=
      mul_nonneg (lpNorm_nonneg p x) (lpNorm_nonneg q y)
    have h' : -pairing x y ≤ lpNorm p x * lpNorm q y := by
      simpa only [pairing_neg_left, lpNorm_neg] using h
    linarith
  · exact pairing_le_lpNorm_mul hpq x y
end O3
