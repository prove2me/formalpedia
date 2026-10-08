-- Prove2me | solution 1 for NagaevLD.GenMoment.eq_2_47
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:24:30.106362+00:00
-- url     : https://prove2.me/submissions/6d8e4972-d9ec-4f1f-be3d-6295b4a9df3a

import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory


/-- (2.47), p. 767: for `h = g′(x/n)` the supremum of `e^{hu - g(u)}` over `u ≥ 0` is attained
at `u = x/n` and equals `e^{hx/n - g(x/n)}`. -/
theorem solution (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0))
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    IsGreatest ((fun u : ℝ => Real.exp (h * u - g u)) '' Set.Ici 0)
      (Real.exp (h * (x / n) - g (x / n))) := by
  have ht : 0 ≤ x / (n : ℝ) := div_nonneg hx.le (Nat.cast_nonneg _)
  have hm : MonotoneOn (deriv g) (Set.Ici 0) := by
    intro a ha b hb hab
    rw [(hg a ha).deriv, (hg b hb).deriv]
    exact hg'mono ha hb hab
  have hc : ConvexOn ℝ (Set.Ici 0) g :=
    (hm.mono interior_subset).convexOn_of_deriv (convex_Ici 0)
      (fun u hu => (hg u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hg u (interior_subset hu)).differentiableAt.differentiableWithinAt)
  refine ⟨⟨x / n, ht, rfl⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  apply Real.exp_le_exp.mpr
  subst h
  rcases lt_trichotomy (x / (n : ℝ)) u with hlt | heq | hgt
  · have hs := hc.le_slope_of_hasDerivAt ht hu hlt (hg _ ht)
    rw [slope_def_field] at hs
    have hs' := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    nlinarith
  · rw [heq]
  · have hs := hc.slope_le_of_hasDerivAt hu ht hgt (hg _ ht)
    rw [slope_def_field] at hs
    have hs' := (div_le_iff₀ (sub_pos.mpr hgt)).mp hs
    nlinarith

#print axioms solution
