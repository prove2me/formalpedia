-- Prove2me | solution 1 for NoHair.Weyl.maximum_principle_off_axis
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:08:20.568085+00:00
-- url     : https://prove2.me/submissions/a9b28a26-fd4e-4458-ac58-59c5d975e2c1

import Definitions.Def_NoHair_vacuumErnst
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open NoHair.Weyl Set Filter Topology

private theorem second_nonpos_at_max {h : ℝ → ℝ} {x : ℝ}
    (hc : ContinuousAt h x) (hm : IsLocalMax h x) : deriv (deriv h) x ≤ 0 := by
  by_contra! hpos
  have hn := isLocalMin_of_deriv_deriv_pos hpos hm.deriv_eq_zero hc
  have heq : h =ᶠ[𝓝 x] (fun _ => h x) := by
    filter_upwards [show ∀ᶠ t in 𝓝 x, h t ≤ h x from hm,
      show ∀ᶠ t in 𝓝 x, h x ≤ h t from hn] with t h₁ h₂
    exact le_antisymm h₁ h₂
  have hzero : deriv (deriv h) x = 0 := by simpa using heq.deriv.deriv_eq
  exact hpos.ne' hzero

private theorem slice_s {f : OrbitPoint → ℝ} (hf : Differentiable ℝ f) (s z : ℝ) :
    HasDerivAt (fun t : ℝ => f (t, z)) (ds f (s, z)) s :=
  (hf (s,z)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))

private theorem slice_z {f : OrbitPoint → ℝ} (hf : Differentiable ℝ f) (s z : ℝ) :
    HasDerivAt (fun t : ℝ => f (s, t)) (dz f (s, z)) z :=
  (hf (s,z)).hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z s).prodMk (hasDerivAt_id z))

private def tilted (f : OrbitPoint → ℝ) (b δ : ℝ) (q : OrbitPoint) : ℝ :=
  f q + δ * ((q.1 - b) + (q.2 ^ 2 - b ^ 2))

/-- The strictly subharmonic perturbation cannot attain an interior maximum. -/
private theorem no_tilted_max {f : OrbitPoint → ℝ} (hf : ContDiff ℝ 2 f)
    (hsub : ∀ q, 0 ≤ scaledLaplacian f q) (b : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : OrbitPoint) (hm : IsLocalMax (tilted f b δ) p) : False := by
  have hd := hf.differentiable (by norm_num)
  have hfd := hf.fderiv_right (m := 1) (by norm_num)
  have hds : Differentiable ℝ (ds f) :=
    (hfd.clm_apply (show ContDiff ℝ 1 (fun _ : OrbitPoint => ((1,0) : OrbitPoint)) from
      contDiff_const)).differentiable_one
  have hdz : Differentiable ℝ (dz f) :=
    (hfd.clm_apply (show ContDiff ℝ 1 (fun _ : OrbitPoint => ((0,1) : OrbitPoint)) from
      contDiff_const)).differentiable_one
  let g := tilted f b δ
  have hg : Continuous g := by
    have := hf.continuous
    change Continuous (fun q : OrbitPoint => f q + δ * ((q.1-b) + (q.2^2-b^2)))
    fun_prop (disch := assumption)
  have hms : IsLocalMax (fun t : ℝ => g (t,p.2)) p.1 :=
    hm.comp_continuous (g := fun t : ℝ => (t,p.2)) (by fun_prop)
  have hmz : IsLocalMax (fun t : ℝ => g (p.1,t)) p.2 :=
    hm.comp_continuous (g := fun t : ℝ => (p.1,t)) (by fun_prop)
  have hgs : deriv (fun t : ℝ => g (t,p.2)) = fun t => ds f (t,p.2) + δ := by
    funext t
    simpa [g, tilted] using ((slice_s hd t p.2).fun_add
      ((((hasDerivAt_id' t).sub_const b).add_const (p.2 ^ 2 - b ^ 2)).const_mul δ)).deriv
  have hgz : deriv (fun t : ℝ => g (p.1,t)) = fun t => dz f (p.1,t) + δ * (2*t) := by
    funext t
    simpa [g, tilted] using ((slice_z hd p.1 t).fun_add
      (((((hasDerivAt_id' t).fun_pow 2).sub_const (b ^ 2)).const_add (p.1-b)).const_mul δ)).deriv
  have hs := second_nonpos_at_max (hg.comp (show Continuous (fun t : ℝ => (t,p.2)) by
    fun_prop)).continuousAt hms
  have hz := second_nonpos_at_max (hg.comp (show Continuous (fun t : ℝ => (p.1,t)) by
    fun_prop)).continuousAt hmz
  change deriv (deriv (fun t : ℝ => g (t,p.2))) p.1 ≤ 0 at hs
  change deriv (deriv (fun t : ℝ => g (p.1,t))) p.2 ≤ 0 at hz
  rw [hgs, ((slice_s hds p.1 p.2).add_const δ).deriv] at hs
  rw [hgz, ((slice_z hdz p.1 p.2).fun_add
    (((hasDerivAt_id' p.2).const_mul 2).const_mul δ)).deriv] at hz
  simp only [mul_one] at hz
  have hh := hsub p
  unfold scaledLaplacian at hh
  have he := Real.exp_pos (2*p.1)
  nlinarith only [hh, hs, mul_nonpos_of_nonneg_of_nonpos he.le hz, mul_pos he hδ]

theorem solution (f : OrbitPoint → ℝ)
    (hf : ContDiff ℝ 2 f) (hsub : ∀ p, 0 ≤ scaledLaplacian f p)
    (hbound : ∃ C : ℝ, ∀ p, f p ≤ C)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ p : OrbitPoint,
      R ≤ Real.exp (2 * p.1) + p.2 ^ 2 → f p ≤ ε) :
    ∀ p, f p ≤ 0 := by
  intro p
  by_contra! hp
  obtain ⟨C, hC⟩ := hbound
  let ε := f p / 2
  have hε : 0 < ε := half_pos hp
  obtain ⟨R, hR⟩ := hdecay ε hε
  obtain ⟨b, hb⟩ := exists_gt (max (max 1 R) (max p.1 |p.2|))
  have hb1 : 1 < b := lt_of_le_of_lt ((le_max_left 1 R).trans (le_max_left _ _)) hb
  have hbR : R < b := lt_of_le_of_lt ((le_max_right 1 R).trans (le_max_left _ _)) hb
  have hbp : p.1 < b := lt_of_le_of_lt ((le_max_left p.1 |p.2|).trans (le_max_right _ _)) hb
  have hbz : |p.2| < b := lt_of_le_of_lt ((le_max_right p.1 |p.2|).trans (le_max_right _ _)) hb
  have hb0 : 0 < b := by linarith
  have hZ := abs_lt.mp hbz
  have hrad : R ≤ Real.exp (2*b) := by linarith [Real.add_one_le_exp (2*b)]
  have hzrad : R ≤ b^2 := by nlinarith [mul_nonneg hb0.le (sub_nonneg.mpr hb1.le)]
  let loss := b - p.1 + (b^2 - p.2^2)
  have hloss : 0 < loss := by
    dsimp [loss]
    nlinarith [mul_pos (sub_pos.mpr hZ.2) (show 0 < b+p.2 by linarith [hZ.1])]
  let δ := (f p - ε)/(2*(loss+1))
  have hgap : 0 < f p - ε := by dsimp [ε]; linarith
  have hδ : 0 < δ := div_pos hgap (by positivity)
  have hmul : δ * (2*(loss+1)) = f p - ε := div_mul_cancel₀ _ (by positivity)
  have hgp : ε < tilted f b δ p := by
    change ε < f p + δ * ((p.1-b)+(p.2^2-b^2))
    have hmul' : δ * (2*((b-p.1+(b^2-p.2^2))+1)) = f p - ε := hmul
    nlinarith only [hmul', hδ, hgap]
  let l := min (p.1-1) (b+(ε-C)/δ)
  have hlp : l < p.1 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hlbound : (l-b)*δ ≤ ε-C := (le_div_iff₀ hδ).mp
    (by have := min_le_right (p.1-1) (b+(ε-C)/δ); dsimp [l]; linarith)
  let K : Set OrbitPoint := Icc l b ×ˢ Icc (-b) b
  have hpK : p ∈ K := ⟨⟨hlp.le, hbp.le⟩, ⟨hZ.1.le, hZ.2.le⟩⟩
  have hcont : Continuous (tilted f b δ) := by
    have := hf.continuous
    unfold tilted
    fun_prop (disch := assumption)
  obtain ⟨q, hq, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    (show K.Nonempty from ⟨p, hpK⟩) hcont.continuousOn
  obtain ⟨⟨hql,hqr⟩,⟨hqb,hqt⟩⟩ := hq
  have hqg := lt_of_lt_of_le hgp ((isMaxOn_iff.mp hmax) p hpK)
  have hzsq : q.2^2 ≤ b^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqt) (show 0 ≤ b+q.2 by linarith)]
  have hqf : ε < f q := by
    unfold tilted at hqg
    linarith [mul_nonpos_of_nonneg_of_nonpos hδ.le
      (show (q.1-b)+(q.2^2-b^2) ≤ 0 by linarith)]
  have hl : l < q.1 := by
    apply lt_of_le_of_ne hql
    intro he
    unfold tilted at hqg
    rw [← he] at hqg
    nlinarith [hC q, mul_nonpos_of_nonneg_of_nonpos hδ.le (sub_nonpos.mpr hzsq)]
  have inside : Real.exp (2*q.1) + q.2^2 < R := by
    by_contra! hout
    exact (hR q hout).not_gt hqf
  have hr : q.1 < b := by
    apply lt_of_le_of_ne hqr
    intro he
    rw [he] at inside
    linarith [sq_nonneg q.2]
  have hbottom : -b < q.2 := by
    apply lt_of_le_of_ne hqb
    intro he
    rw [← he, neg_sq] at inside
    linarith [Real.exp_pos (2*q.1)]
  have htop : q.2 < b := by
    apply lt_of_le_of_ne hqt
    intro he
    rw [he] at inside
    linarith [Real.exp_pos (2*q.1)]
  exact no_tilted_max hf hsub b hδ q
    (hmax.isLocalMax (prod_mem_nhds (Icc_mem_nhds hl hr) (Icc_mem_nhds hbottom htop)))
