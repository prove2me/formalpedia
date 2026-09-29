-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.weighted_convex_hlawka
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T20:40:01.550207+00:00
-- url     : https://prove2.me/submissions/8bd25b7e-99b9-4a3f-84e8-60c071900950

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_WeightedConvex
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# A weighted three-point convexity inequality

The scalar input to the sharp construction is a weighted Hlawka inequality
for any convex function on the real line. The proof uses chords and orders
the three points; it needs no integral representation of convex functions.
-/

open HlawkaSchatten.DiagonalConstruction

private theorem weighted_jensen {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) (x y : ℝ) :
    (a + b) * f ((a * x + b * y) / (a + b)) ≤ a * f x + b * f y := by
  have h := hf.2 (Set.mem_univ x) (Set.mem_univ y)
    (div_nonneg ha hab.le) (div_nonneg hb hab.le)
    (show a / (a + b) + b / (a + b) = 1 by field_simp)
  simp only [smul_eq_mul] at h
  have he : a / (a + b) * x + b / (a + b) * y =
      (a * x + b * y) / (a + b) := by ring
  rw [he] at h
  have hm := mul_le_mul_of_nonneg_left h hab.le
  have h1 : (a + b) * (a / (a + b)) = a := mul_div_cancel₀ a hab.ne'
  have h2 : (a + b) * (b / (a + b)) = b := mul_div_cancel₀ b hab.ne'
  simpa only [mul_add, ← mul_assoc, h1, h2] using hm

private theorem convex_chord {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {x z u : ℝ} (hxz : x < z) (hxu : x ≤ u) (huz : u ≤ z) :
    (z - x) * f u ≤ (z - u) * f x + (u - x) * f z := by
  have h := weighted_jensen hf (sub_nonneg.mpr huz) (sub_nonneg.mpr hxu)
    (by linarith : 0 < (z - u) + (u - x)) x z
  have he : ((z - u) * x + (u - x) * z) / ((z - u) + (u - x)) = u := by
    apply (div_eq_iff (by linarith : (z - u) + (u - x) ≠ 0)).mpr
    ring
  rw [he] at h
  convert h using 1
  ring

private theorem two_chords {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {x z u v A B a b : ℝ} (hxz : x < z)
    (hxu : x ≤ u) (huz : u ≤ z) (hxv : x ≤ v) (hvz : v ≤ z)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hmass : A + B = a + b) (hmoment : A * u + B * v = a * x + b * z) :
    A * f u + B * f v ≤ a * f x + b * f z := by
  have hu := mul_le_mul_of_nonneg_left (convex_chord hf hxz hxu huz) hA
  have hv := mul_le_mul_of_nonneg_left (convex_chord hf hxz hxv hvz) hB
  have hleft : A * (z - u) + B * (z - v) = (z - x) * a := by
    linear_combination z * hmass - hmoment
  have hright : A * (u - x) + B * (v - x) = (z - x) * b := by
    linear_combination hmoment - x * hmass
  apply (mul_le_mul_iff_right₀ (sub_pos.mpr hxz)).mp
  calc
    (z - x) * (A * f u + B * f v) ≤
        (A * (z - u) + B * (z - v)) * f x +
          (A * (u - x) + B * (v - x)) * f z := by nlinarith
    _ = (z - x) * (a * f x + b * f z) := by rw [hleft, hright]; ring

private theorem weightedPairs_swap12 (f : ℝ → ℝ) (a b c x y z : ℝ) :
    weightedPairs f a b c x y z = weightedPairs f b a c y x z := by
  unfold weightedPairs
  ac_rfl

private theorem weightedPairs_swap23 (f : ℝ → ℝ) (a b c x y z : ℝ) :
    weightedPairs f a b c x y z = weightedPairs f a c b x z y := by
  unfold weightedPairs
  ac_rfl

private theorem weightedTotal_swap12 (f : ℝ → ℝ) (a b c x y z : ℝ) :
    weightedTotal f a b c x y z = weightedTotal f b a c y x z := by
  unfold weightedTotal
  ac_rfl

private theorem weightedTotal_swap23 (f : ℝ → ℝ) (a b c x y z : ℝ) :
    weightedTotal f a b c x y z = weightedTotal f a c b x z y := by
  unfold weightedTotal
  ac_rfl

private theorem weighted_convex_ordered {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {a b c x y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hxy : x ≤ y) (hyz : y ≤ z) :
    weightedPairs f a b c x y z ≤ weightedTotal f a b c x y z := by
  have hab : 0 < a + b := add_pos ha hb
  have hac : 0 < a + c := add_pos ha hc
  have hbc : 0 < b + c := add_pos hb hc
  have hS : 0 < a + b + c := add_pos hab hc
  let m := (a * x + b * y + c * z) / (a + b + c)
  have hm : (a + b + c) * m = a * x + b * y + c * z := by
    dsimp [m]
    field_simp
  have hxz := hxy.trans hyz
  rcases eq_or_lt_of_le hxz with heq | hlt
  · have hyeq : y = z := le_antisymm hyz (heq ▸ hxy)
    subst x
    subst y
    have hmean (A B : ℝ) (hAB : 0 < A + B) :
        (A * z + B * z) / (A + B) = z := by
      apply (div_eq_iff hAB.ne').mpr
      ring
    simp only [weightedPairs, weightedTotal, hmean a b hab, hmean a c hac,
      hmean b c hbc]
    have hall : (a * z + b * z + c * z) / (a + b + c) = z := by
      apply (div_eq_iff hS.ne').mpr
      ring
    rw [hall]
    ring_nf
    rfl
  have hxm : x < m := by
    apply (lt_div_iff₀ hS).mpr
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hxy), mul_pos hc (sub_pos.mpr hlt)]
  have hmz : m < z := by
    apply (div_lt_iff₀ hS).mpr
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hyz), mul_pos ha (sub_pos.mpr hlt)]
  by_cases hym : y ≤ m
  · have hmv : m ≤ (a * x + c * z) / (a + c) := by
      apply (le_div_iff₀ hac).mpr
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hym)]
    have hvz : (a * x + c * z) / (a + c) ≤ z := by
      apply (div_le_iff₀ hac).mpr
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hxz)]
    have hmw : m ≤ (b * y + c * z) / (b + c) := by
      apply (le_div_iff₀ hbc).mpr
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hxm.le)]
    have hwz : (b * y + c * z) / (b + c) ≤ z := by
      apply (div_le_iff₀ hbc).mpr
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hyz)]
    have htwo := two_chords hf hmz hmv hvz hmw hwz hac.le hbc.le
      (show (a + c) + (b + c) = (a + b + c) + c by ring)
      (show (a + c) * ((a * x + c * z) / (a + c)) +
        (b + c) * ((b * y + c * z) / (b + c)) =
          (a + b + c) * m + c * z by
        rw [mul_div_cancel₀ _ hac.ne', mul_div_cancel₀ _ hbc.ne', hm]
        ring)
    have hone := weighted_jensen hf ha.le hb.le hab x y
    dsimp only [weightedPairs, weightedTotal]
    change _ ≤ a * f x + b * f y + c * f z + (a + b + c) * f m
    linarith
  · have hmy : m ≤ y := le_of_not_ge hym
    have hxu : x ≤ (a * x + b * y) / (a + b) := by
      apply (le_div_iff₀ hab).mpr
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hxy)]
    have hum : (a * x + b * y) / (a + b) ≤ m := by
      apply (div_le_iff₀ hab).mpr
      nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hmz.le)]
    have hxv : x ≤ (a * x + c * z) / (a + c) := by
      apply (le_div_iff₀ hac).mpr
      nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hxz)]
    have hvm : (a * x + c * z) / (a + c) ≤ m := by
      apply (div_le_iff₀ hac).mpr
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hmy)]
    have htwo := two_chords hf hxm hxu hum hxv hvm hab.le hac.le
      (show (a + b) + (a + c) = a + (a + b + c) by ring)
      (show (a + b) * ((a * x + b * y) / (a + b)) +
        (a + c) * ((a * x + c * z) / (a + c)) =
          a * x + (a + b + c) * m by
        rw [mul_div_cancel₀ _ hab.ne', mul_div_cancel₀ _ hac.ne', hm]
        ring)
    have hone := weighted_jensen hf hb.le hc.le hbc y z
    dsimp only [weightedPairs, weightedTotal]
    change _ ≤ a * f x + b * f y + c * f z + (a + b + c) * f m
    linarith

theorem solution {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x y z : ℝ) :
    weightedPairs f a b c x y z ≤ weightedTotal f a b c x y z := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · exact weighted_convex_ordered hf ha hb hc hxy hyz
    · rcases le_total x z with hxz | hzx
      · rw [weightedPairs_swap23, weightedTotal_swap23]
        exact weighted_convex_ordered hf ha hc hb hxz hzy
      · rw [weightedPairs_swap23, weightedTotal_swap23,
          weightedPairs_swap12, weightedTotal_swap12]
        exact weighted_convex_ordered hf hc ha hb hzx hxy
  · rcases le_total x z with hxz | hzx
    · rw [weightedPairs_swap12, weightedTotal_swap12]
      exact weighted_convex_ordered hf hb ha hc hyx hxz
    · rcases le_total y z with hyz | hzy
      · rw [weightedPairs_swap12, weightedTotal_swap12,
          weightedPairs_swap23, weightedTotal_swap23]
        exact weighted_convex_ordered hf hb hc ha hyz hzx
      · rw [weightedPairs_swap12, weightedTotal_swap12,
          weightedPairs_swap23, weightedTotal_swap23,
          weightedPairs_swap12, weightedTotal_swap12]
        exact weighted_convex_ordered hf hc hb ha hzy hyx
