-- Prove2me | solution 1 for LovaszTheta.shannonCapacity_cycle_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:51:23.36849+00:00
-- url     : https://prove2.me/submissions/e185988c-eeb4-409a-ad48-3938f56ac7f9

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Theorems.Thm_LovaszTheta_indepNum_strongPow_cycle_five_real
public import Theorems.Thm_LovaszTheta_indepNum_strongPow_cycle_five_two

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}
namespace LovaszTheta
theorem _root_.solution : shannonCapacity (cycleGraph 5) = Real.sqrt 5 := by
  have hterm : ∀ k : ℕ,
      ((strongPow (cycleGraph 5) (k + 1)).indepNum : ℝ) ^ (1 / ((k : ℝ) + 1)) ≤ Real.sqrt 5 := by
    intro k
    have h := indepNum_strongPow_cycle_five_real (k + 1)
    calc ((strongPow (cycleGraph 5) (k + 1)).indepNum : ℝ) ^ (1 / ((k : ℝ) + 1))
        ≤ (Real.sqrt 5 ^ (k + 1)) ^ (1 / ((k : ℝ) + 1)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h (by positivity)
      _ = Real.sqrt 5 := by
          rw [show (1 / ((k : ℝ) + 1)) = ((k + 1 : ℕ) : ℝ)⁻¹ by push_cast; rw [one_div]]
          exact Real.pow_rpow_inv_natCast (Real.sqrt_nonneg 5) (Nat.succ_ne_zero k)
  have hbdd : BddAbove (Set.range fun k : ℕ =>
      ((strongPow (cycleGraph 5) (k + 1)).indepNum : ℝ) ^ (1 / ((k : ℝ) + 1))) :=
    ⟨Real.sqrt 5, by rintro _ ⟨k, rfl⟩; exact hterm k⟩
  apply le_antisymm (ciSup_le hterm)
  have h1 := le_ciSup hbdd 1
  rw [indepNum_strongPow_cycle_five_two] at h1
  convert h1 using 1
  rw [Real.sqrt_eq_rpow]
  norm_num
end LovaszTheta
