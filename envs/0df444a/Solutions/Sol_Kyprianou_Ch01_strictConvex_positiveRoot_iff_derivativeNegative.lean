-- Prove2me | solution 1 for Kyprianou.Ch01.strictConvex_positiveRoot_iff_derivativeNegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T12:11:51.127847+00:00
-- url     : https://prove2.me/submissions/8f583adf-2057-40bd-ac51-e934e42c5e12

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology
set_option autoImplicit false

/-- A strictly convex superlinear-at-infinity function has a positive second zero
    precisely when its right derivative at its initial zero is negative. -/
theorem solution
    (f : ℝ → ℝ) (d : ℝ)
    (hconv : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) f)
    (hzero : f 0 = 0)
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    (hlarge : Tendsto f atTop atTop)
    (hd : HasDerivWithinAt f d (Set.Ici (0 : ℝ)) 0) :
    ((∃ theta : ℝ, 0 < theta ∧ f theta = 0) ↔ d < 0) := by
  constructor
  · rintro ⟨theta, ht, heq⟩
    have hs := hconv.lt_slope_of_hasDerivWithinAt
      (by simp) (by simp [ht.le]) ht hd
    have hsl : slope f 0 theta = 0 := by
      rw [slope_def_field, hzero, heq]
      simp
    rwa [hsl] at hs
  · intro hneg
    have hn : ∃ᶠ x in 𝓝[>] (0 : ℝ), slope f 0 x < 0 :=
      hd.liminf_right_slope_le hneg
    have hnear : ∃ᶠ x in 𝓝[>] (0 : ℝ),
        slope f 0 x < 0 ∧ 0 < x :=
      hn.and_eventually self_mem_nhdsWithin
    obtain ⟨x, hs, hx⟩ := hnear.exists
    have hxneg : f x < 0 := by
      have hsl : slope f 0 x = f x / x := by
        rw [slope_def_field, hzero]
        simp
      rw [hsl] at hs
      have hh := (div_lt_iff₀ hx).mp hs
      linarith
    have hlarge_pos : ∀ᶠ y in atTop, 0 < f y :=
      hlarge.eventually (eventually_gt_atTop (0 : ℝ))
    obtain ⟨y, hypos, hxy⟩ :=
      (hlarge_pos.and (eventually_gt_atTop x)).exists
    have hc : ContinuousOn f (Set.Icc x y) :=
      hcont.mono (fun z hz => le_trans hx.le hz.1)
    have hz : (0 : ℝ) ∈ Set.Icc (f x) (f y) :=
      ⟨le_of_lt hxneg, le_of_lt hypos⟩
    obtain ⟨t, ht, hft⟩ :=
      intermediate_value_Icc hxy.le hc hz
    exact ⟨t, lt_of_lt_of_le hx ht.1, hft⟩
