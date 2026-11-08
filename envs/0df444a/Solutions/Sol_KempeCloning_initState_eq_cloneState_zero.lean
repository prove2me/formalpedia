-- Prove2me | solution 1 for KempeCloning.initState_eq_cloneState_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:37:51.782312+00:00
-- url     : https://prove2.me/submissions/6723b469-0982-431a-afc8-8ba6b73f179d

import Definitions.Def_KempeCloning_initState
import Definitions.Def_KempeCloning_cloneState

open KempeCloning in
theorem solution (m N : ℕ) :
    KempeCloning.initState m N = KempeCloning.cloneState m N 0 := by
  unfold KempeCloning.initState KempeCloning.cloneState
  rw [Finset.sum_range_one]
  simp only [Nat.choose_zero_right, Nat.add_zero, Nat.sub_zero, Nat.sub_self, Nat.choose_self,
    Nat.cast_one, Real.sqrt_one, inv_one, Complex.ofReal_one, pow_zero, one_mul, one_smul]
