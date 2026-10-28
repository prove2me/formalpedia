-- Prove2me | solution 1 for NonconvexCost.Complexity.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:28:21.161982+00:00
-- url     : https://prove2.me/submissions/23364cea-f4bc-40b0-bb28-17e5c750fd92

import Mathlib

open Set

theorem solution (h s : ℝ → ℝ) (p q : ℝ) (hs : ConvexOn ℝ (Icc p q) s)
    (hhs : ConvexOn ℝ (Icc p q) (h + s)) (x y : ℝ) (hpx : p ≤ x) (hxy : x < y) (hyq : y ≤ q)
    (c a b : ℝ) (hc : HasDerivWithinAt h c (Icc x q) x) (hc0 : 0 ≤ c)
    (ha : HasDerivWithinAt s a (Icc x q) x) (hb : HasDerivWithinAt s b (Icc p y) y) :
    a - b ≤ (h y - h x) / (y - x) := by
  have hsR : ConvexOn ℝ (Icc x q) s := hs.subset (Icc_subset_Icc hpx le_rfl) (convex_Icc x q)
  have hsL : ConvexOn ℝ (Icc p y) s := hs.subset (Icc_subset_Icc le_rfl hyq) (convex_Icc p y)
  have hhsR : ConvexOn ℝ (Icc x q) (h + s) :=
    hhs.subset (Icc_subset_Icc hpx le_rfl) (convex_Icc x q)
  have hxR : x ∈ Icc x q := ⟨le_rfl, (hxy.trans_le hyq).le⟩
  have hyR : y ∈ Icc x q := ⟨hxy.le, hyq⟩
  have hxL : x ∈ Icc p y := ⟨hpx, hxy.le⟩
  have hyL : y ∈ Icc p y := ⟨hpx.trans hxy.le, le_rfl⟩
  have h1 : a ≤ slope s x y := hsR.le_slope_of_hasDerivWithinAt hxR hyR hxy ha
  have h2 : slope s x y ≤ b := hsL.slope_le_of_hasDerivWithinAt hxL hyL hxy hb
  have h3 : c + a ≤ slope (h + s) x y :=
    hhsR.le_slope_of_hasDerivWithinAt hxR hyR hxy (hc.add ha)
  have e : slope (h + s) x y = slope h x y + slope s x y := by
    simp only [slope_def_field, Pi.add_apply]; ring
  rw [← slope_def_field]
  linarith
