-- Prove2me | solution 1 for MayersBC.toussaint
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:15:35.706111+00:00
-- url     : https://prove2.me/submissions/ac425dba-f9fe-4da8-a529-e270109d0fbe

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsProbDist
import Definitions.Def_FuchsVdGraaf_bhattacharyya
import Definitions.Def_MayersBC_kolmogorov

/-- One term of Toussaint's inequality: `a + b - 2√(ab) = (√a - √b)² ≤ |a - b|`. -/
private lemma toussaint_term {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a + b - 2 * Real.sqrt (a * b) ≤ |a - b| := by
  set s := Real.sqrt a with hs
  set t := Real.sqrt b with ht
  have hs0 : 0 ≤ s := Real.sqrt_nonneg a
  have ht0 : 0 ≤ t := Real.sqrt_nonneg b
  have hsa : s ^ 2 = a := Real.sq_sqrt ha
  have htb : t ^ 2 = b := Real.sq_sqrt hb
  have hab : Real.sqrt (a * b) = s * t := Real.sqrt_mul ha b
  rw [hab, ← hsa, ← htb]
  rcases le_total t s with h | h
  · rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  · rw [abs_of_nonpos (by nlinarith)]
    nlinarith

theorem solution {J : Type} [Fintype J] (p0 p1 : J → ℝ)
    (h0 : FuchsVdGraaf.IsProbDist p0) (h1 : FuchsVdGraaf.IsProbDist p1) :
    1 - FuchsVdGraaf.bhattacharyya p0 p1 ≤ MayersBC.kolmogorov p0 p1 / 2 := by
  have hsum : ∑ j, (p0 j + p1 j - 2 * Real.sqrt (p0 j * p1 j)) ≤ ∑ j, |p0 j - p1 j| :=
    Finset.sum_le_sum fun j _ => toussaint_term (h0.1 j) (h1.1 j)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h0.2, h1.2, ← Finset.mul_sum] at hsum
  unfold FuchsVdGraaf.bhattacharyya MayersBC.kolmogorov
  linarith
