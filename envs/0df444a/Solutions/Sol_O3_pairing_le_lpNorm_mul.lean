-- Prove2me | solution 1 for O3.pairing_le_lpNorm_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:59:03.688603+00:00
-- url     : https://prove2.me/submissions/dac73e02-3f0d-4688-b713-80bd1b2d7c09

import Mathlib
import Definitions.Def_O3_Geometry
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
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
    pairing x y ≤ lpNorm p x * lpNorm q y := by
  simpa [pairing, lpNorm, lpPower] using
    (Real.inner_le_Lp_mul_Lq (Finset.univ : Finset (Fin d)) x y hpq)
end O3
