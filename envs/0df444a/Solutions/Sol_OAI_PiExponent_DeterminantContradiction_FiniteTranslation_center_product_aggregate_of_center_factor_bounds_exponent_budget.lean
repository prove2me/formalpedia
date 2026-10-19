-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds_exponent_budget
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:12:30.440629+00:00
-- url     : https://prove2.me/submissions/990aa70e-b2fb-40b2-9ef9-7fe375038713

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r)
    (hsupport :
      (∑ i : Fin d.m,
        MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i *
          (t.2.1 i : ℕ)) ≤ (t.2.2 : ℕ)) :
    (Real.log (2 * (d.K : ℝ)) + nu) *
        (∑ i : Fin d.m, ((t.1.1 i - r.2.1 i.succ - t.2.1 i : ℕ) : ℝ)) -
      nu * (∑ i : Fin d.m,
        MatrixArithmetic.logWeights (finiteDenominators d) i *
          ((t.1.1 i - r.2.1 i.succ - t.2.1 i : ℕ) : ℝ)) ≤
      -nu * (weight d t.1 - ∑ i : Fin d.m,
        MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) +
      H * (nu / d.F0 + (Real.log (2 * (d.K : ℝ)) + nu) / d.wstar) := by
  classical
  let w := MatrixArithmetic.logWeights (finiteDenominators d)
  let a : Fin d.m → ℕ := t.1.1
  let u : Fin d.m → ℕ := fun i => r.2.1 i.succ
  let b : Fin d.m → ℕ := fun i => (t.2.1 i : ℕ)
  let e : Fin d.m → ℕ := fun i => a i - u i - b i
  let T := MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0
  let C : ℝ := Real.log (2 * (d.K : ℝ)) + nu
  have hw (i : Fin d.m) : d.wstar ≤ w i := by
    calc
      d.wstar ≤ d.x (i.val + 1) := d.wstar_lower i
      _ = w i := by
        simpa only [w, MatrixArithmetic.logWeights, finiteDenominators] using d.x_log i.val
  have hw0 (i : Fin d.m) : 0 ≤ w i := d.wstar_pos.le.trans (hw i)

  -- The column simplex bounds the total remaining exponent mass.
  have hcol : (∑ i : Fin d.m, w i * (a i : ℝ)) ≤ H := by
    have hm : a ∈ realWeightedSimplex w H := t.1.property
    exact (Finset.mem_filter.mp hm).2
  have hmass : (∑ i : Fin d.m, (e i : ℝ)) ≤ H / d.wstar := by
    apply (le_div_iff₀ d.wstar_pos).mpr
    have hm : d.wstar * (∑ i : Fin d.m, (e i : ℝ)) ≤
        ∑ i : Fin d.m, w i * (a i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hea : e i ≤ a i := by
        dsimp only [e]
        omega
      calc
        d.wstar * (e i : ℝ) ≤ w i * (e i : ℝ) :=
          mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)
        _ ≤ w i * (a i : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hea) (hw0 i)
    nlinarith only [hm, hcol]

  -- The support budget and ceiling inequality control the weighted tail.
  have hrow : (d.v0 : ℝ) * (r.2.1 0 : ℝ) +
      (∑ i : Fin d.m, (w i / (d.base.theta : ℝ)) * (u i : ℝ)) < H := by
    have hh : (∑ j : Fin (d.m + 1),
        InterpolationMatrix.rowWeights d.v0 d.base.theta w j * (r.2.1 j : ℝ)) < H :=
      (Finset.mem_filter.mp r.2.property).2
    rw [Fin.sum_univ_succ] at hh
    simpa [InterpolationMatrix.rowWeights, u] using hh
  have hrow0 : (d.v0 : ℝ) * (r.2.1 0 : ℝ) ≤ H := by
    have hrest : 0 ≤ ∑ i : Fin d.m,
        (w i / (d.base.theta : ℝ)) * (u i : ℝ) :=
      Finset.sum_nonneg fun i hi =>
        mul_nonneg (div_nonneg (hw0 i) d.base.theta_pos.le) (Nat.cast_nonneg _)
    linarith only [hrow, hrest]
  have hbudget : (∑ i : Fin d.m, (T i : ℝ) * (b i : ℝ)) ≤ (r.2.1 0 : ℝ) := by
    have hs : (∑ i : Fin d.m, (T i : ℝ) * (b i : ℝ)) ≤
        ((t.2.2 : ℕ) : ℝ) := by
      exact_mod_cast hsupport
    have hl : (t.2.2 : ℕ) ≤ r.2.1 0 := Nat.le_of_lt_succ t.2.2.isLt
    exact hs.trans (by exact_mod_cast hl)
  have hT (i : Fin d.m) : d.F0 * w i ≤ (d.v0 : ℝ) * (T i : ℝ) := by
    have hc : d.F0 * w i / (d.v0 : ℝ) ≤ (T i : ℝ) := Nat.le_ceil _
    have hm := (div_le_iff₀ d.v0_pos).mp hc
    nlinarith only [hm]
  have htail : (∑ i : Fin d.m, w i * (b i : ℝ)) ≤ H / d.F0 := by
    have hFT : d.F0 * (∑ i : Fin d.m, w i * (b i : ℝ)) ≤
        (d.v0 : ℝ) * (∑ i : Fin d.m, (T i : ℝ) * (b i : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hm := mul_le_mul_of_nonneg_right (hT i)
        (Nat.cast_nonneg (b i) : (0 : ℝ) ≤ (b i : ℝ))
      nlinarith only [hm]
    have hv := mul_le_mul_of_nonneg_left hbudget d.v0_pos.le
    apply (le_div_iff₀ d.F0_pos).mpr
    nlinarith only [hFT, hv, hrow0]

  -- Natural subtraction yields a lower bound, even when a row coordinate exceeds a.
  have hdecomp : weight d t.1 - (∑ i : Fin d.m, w i * (u i : ℝ)) -
      (∑ i : Fin d.m, w i * (b i : ℝ)) ≤
      ∑ i : Fin d.m, w i * (e i : ℝ) := by
    calc
      weight d t.1 - (∑ i : Fin d.m, w i * (u i : ℝ)) -
          (∑ i : Fin d.m, w i * (b i : ℝ)) =
          ∑ i : Fin d.m, w i * ((a i : ℝ) - (u i : ℝ) - (b i : ℝ)) := by
        change (∑ i : Fin d.m, w i * (a i : ℝ)) -
          (∑ i : Fin d.m, w i * (u i : ℝ)) -
          (∑ i : Fin d.m, w i * (b i : ℝ)) = _
        simp only [mul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin d.m, w i * (e i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hn : a i ≤ u i + b i + e i := by
          dsimp only [e]
          omega
        have hr : (a i : ℝ) ≤ (u i : ℝ) + (b i : ℝ) + (e i : ℝ) := by
          exact_mod_cast hn
        exact mul_le_mul_of_nonneg_left (by linarith only [hr]) (hw0 i)

  have hC : 0 ≤ C := by
    have hK : (1 : ℝ) ≤ (d.K : ℝ) := by exact_mod_cast d.K_pos
    have hlog : 0 ≤ Real.log (2 * (d.K : ℝ)) :=
      Real.log_nonneg (by linarith only [hK])
    exact add_nonneg hlog hnu
  have hm := mul_le_mul_of_nonneg_left hmass hC
  have ht := mul_le_mul_of_nonneg_left htail hnu
  have hd := mul_le_mul_of_nonneg_left hdecomp hnu
  change C * (∑ i : Fin d.m, (e i : ℝ)) -
      nu * (∑ i : Fin d.m, w i * (e i : ℝ)) ≤
    -nu * (weight d t.1 - ∑ i : Fin d.m, w i * (u i : ℝ)) +
      H * (nu / d.F0 + C / d.wstar)
  have heq : H * (nu / d.F0 + C / d.wstar) =
      nu * (H / d.F0) + C * (H / d.wstar) := by ring
  rw [heq]
  nlinarith only [hm, ht, hd]
