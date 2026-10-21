-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.canonical_fibre_product_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T17:46:44.669237+00:00
-- url     : https://prove2.me/submissions/903fd120-4285-4020-a6dd-bf9038309d77

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     (∏ i : Fin d.m, (w i.succ : Real)) / (∏ i : Fin d.m, (v i.succ : Real)) =
       (d.base.theta : Real) ^ d.m) := by
  classical
  simp only [Fin.cases_succ, Rat.cast_div]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprod :
      (∏ i : Fin d.m, (((Nat.ceil (Real.log (d.q i.val)) : Nat) : Rat) : Real)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hx := d.x_one_le (i.val + 1)
    rw [d.x_log i.val] at hx
    have hcast : (((Nat.ceil (Real.log (d.q i.val)) : Nat) : Rat) : Real) =
        (Nat.ceil (Real.log (d.q i.val)) : Real) := by norm_cast
    rw [hcast]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hprod]
