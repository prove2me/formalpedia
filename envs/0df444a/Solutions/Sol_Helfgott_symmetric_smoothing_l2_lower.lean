-- Prove2me | solution 1 for Helfgott.symmetric_smoothing_l2_lower
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T21:11:28.893046+00:00
-- url     : https://prove2.me/submissions/b130c0bb-31ae-4ced-bd81-1b9a12789218

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
A rigorous elementary lower bound for the L² mass of the compact symmetric
smoothing in Helfgott, arXiv:1312.7748v2, (4.3), used in §7.2. The variable
is translated by one: η_circle(t+1) = (1-t²)^3 exp(-t²/2) on [-1,1].
The lower bound 16/25 is derived here using a cubic lower Taylor polynomial
for exp(-u), then exact polynomial integration. Written by Codex.
-/

open MeasureTheory
open scoped Interval

namespace Helfgott

lemma exp_neg_lower_cubic (u : ℝ) (hu : 0 ≤ u) :
    1 - u + u ^ 2 / 2 - u ^ 3 / 6 ≤ Real.exp (-u) := by
  let g₂ : ℝ → ℝ := fun t => 1 - t + t ^ 2 / 2 - Real.exp (-t)
  have hg₂ (t : ℝ) : HasDerivAt g₂ (-1 + t + Real.exp (-t)) t := by
    dsimp [g₂]
    convert! (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
      (((hasDerivAt_id t).pow 2).div_const 2)).sub
      (((hasDerivAt_id t).neg).exp) using 1 <;> simp <;> ring
  have hm₂ : Monotone g₂ := monotone_of_hasDerivAt_nonneg hg₂ (by
    intro t
    have ht := Real.add_one_le_exp (-t)
    change 0 ≤ -1 + t + Real.exp (-t)
    linarith)
  have h₂ (t : ℝ) (ht : 0 ≤ t) : 0 ≤ g₂ t := by
    have h := hm₂ ht
    simpa [g₂] using h
  let g₃ : ℝ → ℝ := fun t => Real.exp (-t) - 1 + t - t ^ 2 / 2 + t ^ 3 / 6
  have hg₃ (t : ℝ) : HasDerivAt g₃ (g₂ t) t := by
    dsimp [g₃, g₂]
    convert! (((((((hasDerivAt_id t).neg).exp).sub (hasDerivAt_const t (1 : ℝ))).add
      (hasDerivAt_id t)).sub (((hasDerivAt_id t).pow 2).div_const 2)).add
      (((hasDerivAt_id t).pow 3).div_const 6)) using 1 <;> simp <;> ring
  have hm₃ : MonotoneOn g₃ (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (by dsimp [g₃]; fun_prop)
      (fun t _ => (hg₃ t).hasDerivWithinAt)
      (fun t ht => h₂ t (Set.mem_Ici.mp (interior_subset ht)))
  have h := hm₃ (by simp : (0 : ℝ) ∈ Set.Ici 0) hu hu
  dsimp [g₃] at h
  norm_num at h
  linarith

theorem symmetric_smoothing_l2_lower :
    (16 / 25 : ℝ) ≤ ∫ t in (-1 : ℝ)..1,
      ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2 := by
  let P : ℝ → ℝ := fun t =>
    (1 - t ^ 2) ^ 6 * (1 - t ^ 2 + t ^ 4 / 2 - t ^ 6 / 6)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
      P t ≤ ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2 := by
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have he := exp_neg_lower_cubic (t ^ 2) ht2
    have hexp : Real.exp (-(t ^ 2) / 2) ^ 2 = Real.exp (-(t ^ 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow, ← pow_mul, hexp]
    dsimp [P]
    convert! mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ (1 - t ^ 2) ^ 6) using 1 <;>
      (first | rfl | ring | (ext x; ring))
  let Q : ℝ → ℝ := fun t => (1 / 1 : ℝ) * t ^ 1 / 1 + (-7 / 1 : ℝ) * t ^ 3 / 3 + (43 / 2 : ℝ) * t ^ 5 / 5 + (-229 / 6 : ℝ) * t ^ 7 / 7 + (87 / 2 : ℝ) * t ^ 9 / 9 + (-67 / 2 : ℝ) * t ^ 11 / 11 + (107 / 6 : ℝ) * t ^ 13 / 13 + (-13 / 2 : ℝ) * t ^ 15 / 15 + (3 / 2 : ℝ) * t ^ 17 / 17 + (-1 / 6 : ℝ) * t ^ 19 / 19
  have hQ (t : ℝ) : HasDerivAt Q (P t) t := by
    dsimp [Q, P]
    convert! (((((((((((hasDerivAt_const t (0 : ℝ)).add ((((hasDerivAt_id t).pow 1).const_mul (1 / 1 : ℝ)).div_const 1)).add ((((hasDerivAt_id t).pow 3).const_mul (-7 / 1 : ℝ)).div_const 3)).add ((((hasDerivAt_id t).pow 5).const_mul (43 / 2 : ℝ)).div_const 5)).add ((((hasDerivAt_id t).pow 7).const_mul (-229 / 6 : ℝ)).div_const 7)).add ((((hasDerivAt_id t).pow 9).const_mul (87 / 2 : ℝ)).div_const 9)).add ((((hasDerivAt_id t).pow 11).const_mul (-67 / 2 : ℝ)).div_const 11)).add ((((hasDerivAt_id t).pow 13).const_mul (107 / 6 : ℝ)).div_const 13)).add ((((hasDerivAt_id t).pow 15).const_mul (-13 / 2 : ℝ)).div_const 15)).add ((((hasDerivAt_id t).pow 17).const_mul (3 / 2 : ℝ)).div_const 17)).add ((((hasDerivAt_id t).pow 19).const_mul (-1 / 6 : ℝ)).div_const 19)) using 1
    all_goals try funext x
    all_goals simp
    all_goals ring
  have hpint : (∫ t in (-1 : ℝ)..1, P t) = 3104768 / 4849845 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t)
      ((by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _)]
    norm_num [Q]
  have hmono : (∫ t in (-1 : ℝ)..1, P t) ≤
      ∫ t in (-1 : ℝ)..1, ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2)).intervalIntegrable _ _
    · exact hpoint
  rw [hpint] at hmono
  exact le_trans (by norm_num) hmono

end Helfgott

theorem solution :
    (16 / 25 : ℝ) ≤ ∫ t in (-1 : ℝ)..1,
      ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2 :=
  Helfgott.symmetric_smoothing_l2_lower

#print axioms solution
