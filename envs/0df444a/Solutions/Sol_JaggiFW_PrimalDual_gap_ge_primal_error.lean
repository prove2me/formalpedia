-- Prove2me | solution 1 for JaggiFW.PrimalDual.gap_ge_primal_error
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:05:57.030712+00:00
-- url     : https://prove2.me/submissions/9e0f5d73-7f5e-4d65-8c3a-390d904197f0

import Mathlib
import Definitions.Def_JaggiFW_PrimalDual_Setting

set_option autoImplicit false

open Filter Topology

lemma jfp_lin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (hDconv : Convex ℝ D)
    (f : E → ℝ) (hfC1 : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ D f) (x s : E) (hx : x ∈ D) (hs : s ∈ D) :
    f x + fderiv ℝ f x (s - x) ≤ f s := by
  have hdiff : DifferentiableAt ℝ f x := (hfC1.differentiable (by norm_num)) x
  set v := s - x with hv
  set g : ℝ → ℝ := fun t => f (x + t • v) with hg
  have hlin : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf0 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    simpa using hdiff.hasFDerivAt
  have hgd : HasDerivAt g (fderiv ℝ f x v) 0 := hf0.comp_hasDerivAt (0 : ℝ) hlin
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hgd).mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope g 0 t ≤ f s - f x := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hconv := hfconv.2 hx hs (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
    have e : (1 - t) • x + t • s = x + t • v := by
      rw [hv, smul_sub, sub_smul, one_smul]; abel
    rw [e] at hconv
    simp only [smul_eq_mul] at hconv
    rw [slope_def_field]
    simp only [hg, zero_smul, add_zero, sub_zero]
    rw [div_le_iff₀ ht.1]
    nlinarith
  exact (by linarith [le_of_tendsto hslope hev] : f x + fderiv ℝ f x v ≤ f s)

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (hDc : IsCompact D) (hDconv : Convex ℝ D)
    (f : E → ℝ) (hfC1 : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ D f)
    (xstar : E) (hxstar : xstar ∈ D) (hmin : ∀ y ∈ D, f xstar ≤ f y) :
    (∀ x ∈ D, ∀ s ∈ D, f x + fderiv ℝ f x (s - x) ≤ f s) ∧
      (∀ x ∈ D, f x - f xstar ≤ JaggiFW.PrimalDual.dualityGap f D x) := by
  refine ⟨fun x hx s hs => jfp_lin D hDconv f hfC1 hfconv x s hx hs, fun x hx => ?_⟩
  have h := jfp_lin D hDconv f hfC1 hfconv x xstar hx hxstar
  unfold JaggiFW.PrimalDual.dualityGap
  have hbdd : BddAbove ((fun s => fderiv ℝ f x (x - s)) '' D) := by
    have hc : Continuous (fun s => fderiv ℝ f x (x - s)) :=
      (fderiv ℝ f x).continuous.comp (continuous_const.sub continuous_id)
    exact (hDc.image hc).bddAbove
  have this : fderiv ℝ f x (x - xstar) ≤ sSup ((fun s => fderiv ℝ f x (x - s)) '' D) :=
    le_csSup hbdd ⟨xstar, hxstar, rfl⟩
  rw [map_sub] at this
  rw [map_sub] at h
  linarith
