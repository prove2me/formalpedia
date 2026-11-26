-- Prove2me | solution 1 for Kyprianou.Ch04.rightHalfPlaneIdentityFromRealRayV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:48:32.269853+00:00
-- url     : https://prove2.me/submissions/a8a38dad-90dc-4ff5-a1bc-2d2382919f6b

import Mathlib
open Complex Filter Set Topology
set_option autoImplicit false

/-- Equality on the real ray determines continuous holomorphic functions on the closed half-plane. -/
theorem solution (f g : ℂ → ℂ)
    (hf : DiffContOnCl ℂ f {z : ℂ | 0 < z.re})
    (hg : DiffContOnCl ℂ g {z : ℂ | 0 < z.re})
    (hr : ∀ x : ℝ, 1 ≤ x → f (x : ℂ) = g (x : ℂ)) :
    ∀ z : ℂ, 0 ≤ z.re → f z = g z := by
  let H : Set ℂ := {z | 0 < z.re}
  have hOpen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have ha := (Complex.analyticOnNhd_iff_differentiableOn hOpen).2 hf.differentiableOn
  have hb := (Complex.analyticOnNhd_iff_differentiableOn hOpen).2 hg.differentiableOn
  have hc : IsPreconnected H := (convex_halfSpace_re_gt 0).isPreconnected
  have h1 : (1 : ℂ) ∈ H := by norm_num [H]
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact_mod_cast (ne_of_gt hx)
  have he : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ), f (x : ℂ) = g (x : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hr x (le_of_lt hx)
  have hEq := ha.eqOn_of_preconnected_of_frequently_eq hb hc h1 (ht.frequently he.frequently)
  intro z hz
  have hzcl : z ∈ closure H := by
    apply Metric.mem_closure_iff.2
    intro ε hε
    refine ⟨z + ((ε/2 : ℝ) : ℂ), ?_, ?_⟩
    · change 0 < (z + ((ε/2 : ℝ) : ℂ)).re
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    · rw [dist_comm, dist_eq_norm]
      simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
  haveI : NeBot (𝓝[H] z) := mem_closure_iff_nhdsWithin_neBot.mp hzcl
  have hfa := (hf.continuousOn z hzcl).mono subset_closure
  have hga := (hg.continuousOn z hzcl).mono subset_closure
  exact tendsto_nhds_unique hfa (hga.congr' (eventually_mem_nhdsWithin.mono fun w hw => (hEq hw).symm))
