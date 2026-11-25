-- Prove2me | solution 1 for LovaszTheta.indepNum_strongPow_cycle_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:47.588853+00:00
-- url     : https://prove2.me/submissions/8ac326c6-4ca8-4503-ba7e-ba8e5290d114

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Theorems.Thm_LovaszTheta_indepNum_strongPow_cycle_five_real

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}
namespace LovaszTheta
theorem _root_.solution (k : ℕ) :
    (strongPow (cycleGraph 5) k).indepNum ^ 2 ≤ 5 ^ k := by
  have h := indepNum_strongPow_cycle_five_real k
  have h2 : ((strongPow (cycleGraph 5) k).indepNum : ℝ) ^ 2 ≤ (Real.sqrt 5 ^ k) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)] at h2
  exact_mod_cast h2
end LovaszTheta
