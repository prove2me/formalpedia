-- Prove2me | solution 1 for InventoryBounds.stationary_value_derivative
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:36:30.226518+00:00
-- url     : https://prove2.me/submissions/3b1c4058-11ce-4728-aba4-5d79be52e9cd

import Definitions.Def_InventoryBounds_StationaryValuation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring

set_option autoImplicit false
open InventoryBounds
open scoped BigOperators

theorem solution (T : ℕ) (ρ : ℝ) :
    HasDerivAt (valueFormula T) (valueDerivative T ρ) ρ := by
  have hsum : HasDerivAt (fun x : ℝ => ∑ k ∈ Finset.range T, x ^ k)
      (∑ k ∈ Finset.range T, (k : ℝ) * ρ ^ (k - 1)) ρ := by
    exact HasDerivAt.fun_sum (fun k _ => hasDerivAt_pow k ρ)
  have h := ((hasDerivAt_const ρ (T : ℝ)).mul
      ((hasDerivAt_const ρ (1 : ℝ)).sub (hasDerivAt_id ρ))).add
    ((((hasDerivAt_id ρ).const_mul 2).sub_const 1).mul hsum)
  convert h using 1 <;> (first | rfl | (dsimp [valueFormula, valueDerivative]; ring))

#print axioms solution



