-- Prove2me | solution 1 for MazurReduction.abscissa_valuation_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T10:15:05.648659+00:00
-- url     : https://prove2.me/submissions/ce6d75fd-1ced-4273-8926-7caa54961948

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Uses the generic valuation-ring coordinate lemmas from Anthropic's FLT
formalization, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
open WithZero

theorem solution
    (p : ℕ) [Fact p.Prime]
    (W : WeierstrassCurve (Rat.padicValuation p).valuationSubring)
    {x y : ℚ} (h : (W.map (Rat.padicValuation p).valuationSubring.subtype).toAffine.Equation x y)
    (hx : x ∉ (Rat.padicValuation p).valuationSubring) :
    exp (2 : ℤ) ≤ Rat.padicValuation p x := by
  let v := Rat.padicValuation p
  let A := v.valuationSubring
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
  have hy0 : y ≠ 0 := WeierstrassCurve.Affine.Y_ne_zero_of_X_notMem W h hx
  obtain ⟨hr, hrnot⟩ := WeierstrassCurve.Affine.X_cubed_div_Y_sq_notMem_nonunits W h hx
  have hr0 : x ^ 3 / y ^ 2 ≠ 0 := div_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hy0)
  have hrv : v (x ^ 3 / y ^ 2) = 1 := by
    apply le_antisymm
    · exact hr
    · apply (inv_le_one₀ (show 0 < v (x ^ 3 / y ^ 2) from
        (zero_lt_iff).mpr ((map_ne_zero v).mpr hr0))).mp
      rw [← map_inv₀]
      exact A.inv_mem_of_notMem_nonunits hrnot
  have hxlt : 1 < v x := lt_of_not_ge hx
  have heq : 3 * padicValRat p x = 2 * padicValRat p y := by
    rw [map_div₀, map_pow, map_pow] at hrv
    simp only [v, Rat.padicValuation, hx0, hy0, if_false, Valuation.coe_mk,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, ← exp_nsmul, ← exp_sub,
      ← exp_zero, exp_injective.eq_iff, nsmul_eq_mul] at hrv
    omega
  have hxneg : padicValRat p x < 0 := by
    simp only [v, Rat.padicValuation, hx0, if_false, Valuation.coe_mk,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, ← exp_zero, exp_lt_exp] at hxlt
    omega
  have hxle : padicValRat p x ≤ -2 := by omega
  simp only [v, Rat.padicValuation, hx0, if_false, Valuation.coe_mk,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, exp_le_exp]
  omega
