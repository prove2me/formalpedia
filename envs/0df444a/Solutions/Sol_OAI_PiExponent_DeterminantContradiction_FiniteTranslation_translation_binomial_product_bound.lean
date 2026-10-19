-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:08:24.346663+00:00
-- url     : https://prove2.me/submissions/e3d2f389-cee1-4f44-8294-2d56041d420c

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ)‖ ≤
      Real.exp (Real.log 4 * ∑ i : Fin d.m, (t.1.1 i : ℝ)) := by
  let a : Fin d.m → ℕ := fun i => t.1.1 i
  let b : Fin d.m → ℕ := fun i => r.2.1 i.succ
  let c : Fin d.m → ℕ := fun i => t.2.1 i
  have hfactor (i : Fin d.m) :
      (a i).choose (b i) * (a i - b i).choose (c i) ≤ 4 ^ a i := by
    have hfirst : (a i).choose (b i) ≤ 2 ^ a i :=
      Nat.choose_le_two_pow _ _
    have hsecond : (a i - b i).choose (c i) ≤ 2 ^ a i :=
      (Nat.choose_le_two_pow _ _).trans
        (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) (Nat.sub_le _ _))
    calc
      (a i).choose (b i) * (a i - b i).choose (c i) ≤
          2 ^ a i * 2 ^ a i := Nat.mul_le_mul hfirst hsecond
      _ = 4 ^ a i := by rw [← mul_pow]; rfl
  have hprod :
      (∏ i : Fin d.m, (a i).choose (b i) * (a i - b i).choose (c i)) ≤
        4 ^ (∑ i : Fin d.m, a i) := by
    calc
      (∏ i : Fin d.m, (a i).choose (b i) * (a i - b i).choose (c i)) ≤
          ∏ i : Fin d.m, 4 ^ a i :=
        Finset.prod_le_prod' (fun i _ => hfactor i)
      _ = 4 ^ (∑ i : Fin d.m, a i) :=
        Finset.prod_pow_eq_pow_sum Finset.univ a 4
  calc
    ‖((∏ i : Fin d.m,
        (a i).choose (b i) * (a i - b i).choose (c i) : ℕ) : ℂ)‖ =
        ((∏ i : Fin d.m,
          (a i).choose (b i) * (a i - b i).choose (c i) : ℕ) : ℝ) :=
      Complex.norm_natCast _
    _ ≤ ((4 ^ (∑ i : Fin d.m, a i) : ℕ) : ℝ) := Nat.cast_le.mpr hprod
    _ = (4 : ℝ) ^ (∑ i : Fin d.m, a i) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
    _ = Real.exp (Real.log 4 * ∑ i : Fin d.m, (a i : ℝ)) := by
      rw [← Nat.cast_sum, mul_comm, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 4)]
