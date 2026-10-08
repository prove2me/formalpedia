-- Prove2me | solution 1 for MazurReduction.odd_prime_division_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T10:35:42.457408+00:00
-- url     : https://prove2.me/submissions/8ba977eb-ae09-439e-9625-5e94b0d340ed

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_MazurReduction_abscissa_valuation_ge_two
import Theorems.Thm_MazurReduction_leading_coefficient_root_bound
open WithZero
open MazurReduction

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (W : WeierstrassCurve (Rat.padicValuation p).valuationSubring)
    {x y : ℚ}
    (h : (W.map (Rat.padicValuation p).valuationSubring.subtype).toAffine.Equation x y)
    (hx : x ∉ (Rat.padicValuation p).valuationSubring) :
    ((W.map (Rat.padicValuation p).valuationSubring.subtype).preΨ' p).eval x ≠ 0 := by
  let v := Rat.padicValuation p
  let Wq := W.map v.valuationSubring.subtype
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hlc : (Wq.preΨ' p).leadingCoeff = p := by
    rw [Wq.leadingCoeff_preΨ' hp0, if_neg (Nat.not_even_iff_odd.mpr hpodd)]
  have hc : ∀ i, v ((Wq.preΨ' p).coeff i) ≤ 1 := by
    intro i
    dsimp only [Wq]
    rw [W.map_preΨ', Polynomial.coeff_map]
    exact ((W.preΨ' p).coeff i).property
  intro hr
  have hb := leading_coefficient_root_bound v (Wq.preΨ' p)
    (Wq.natDegree_preΨ'_pos hp hp0) hc hr (lt_of_not_ge hx)
  rw [hlc, Rat.padicValuation_self] at hb
  have he : exp (1 : ℤ) ≤ exp (-1 : ℤ) * v x := by
    calc
      exp (1 : ℤ) = exp (-1 : ℤ) * exp (2 : ℤ) := by rw [← exp_add]; norm_num
      _ ≤ exp (-1 : ℤ) * v x :=
        mul_le_mul_of_nonneg_left (abscissa_valuation_ge_two p W h hx) zero_le
  have hpos : 1 < exp (1 : ℤ) := by rw [← exp_zero, exp_lt_exp]; norm_num
  exact (not_le_of_gt (hpos.trans_le he)) hb
