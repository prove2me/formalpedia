-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.AB_eq_pI_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:54.81086+00:00
-- url     : https://prove2.me/submissions/b93664a4-5a08-4016-8633-91f7cf68e640

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_AB_eq_pI_real
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_denom_ne_zero_nat
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_numer_ne_zero_nat

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) (hs : 1 ≤ s) :
    matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) * matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) =
    p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) • 1 := by
  have hk' : 1 ≤ (k : ℤ) := by omega
  have hb' : 1 ≤ (b : ℤ) := by omega
  have hs' : 1 ≤ (s : ℤ) := by omega
  have hr' : 0 ≤ (r : ℤ) := Int.natCast_nonneg r
  have hd := denom_ne_zero_nat n k b r hk hb
  have hn_num := numer_ne_zero_nat n k b r s hk hb hs
  -- Use AB_eq_pI_real and map back
  have h_inj : Function.Injective (↑· : ℚ → ℝ) := Rat.cast_injective
  have h_real := AB_eq_pI_real n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) hn hk' hs' hb' hr' hd hn_num
  ext i j
  apply h_inj
  have h_entry := congr_fun (congr_fun h_real i) j
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
             Matrix.map_apply] at h_entry ⊢
  convert h_entry using 1
  · simp only [Rat.cast_sum, Rat.cast_mul]
  · simp only [smul_eq_mul]
    split_ifs <;> simp
end GroupTheoreticShannonCapacity.Construction
