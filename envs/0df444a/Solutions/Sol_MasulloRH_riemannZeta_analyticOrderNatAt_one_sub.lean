-- Prove2me | solution 1 for MasulloRH.riemannZeta_analyticOrderNatAt_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T02:26:37.594078+00:00
-- url     : https://prove2.me/submissions/37f2551d-7d47-4fe5-8882-529fdb57aac2

import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open MeasureTheory Set
open scoped Topology ContDiff
open MasulloRH
set_option autoImplicit false

theorem solution (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    analyticOrderNatAt riemannZeta (1 - s) = analyticOrderNatAt riemannZeta s := by
  let b : ℂ := 2 * (Real.pi : ℂ)
  let U : ℂ → ℂ := fun z => 2 * b ^ (-z) * Complex.Gamma z * Complex.cos ((Real.pi : ℂ) * z / 2)
  have hpos : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re := by
    change Complex.re ⁻¹' Ioi 0 ∈ 𝓝 s
    exact Complex.continuous_re.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds h0)
  have hlt : ∀ᶠ z : ℂ in 𝓝 s, z.re < 1 := by
    change Complex.re ⁻¹' Iio 1 ∈ 𝓝 s
    exact Complex.continuous_re.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds h1)
  have hnotneg : ∀ z : ℂ, 0 < z.re → ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro z hz n heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith
  have hnotone : ∀ z : ℂ, z.re < 1 → z ≠ 1 := by
    intro z hz heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith
  have hFE : ∀ᶠ z : ℂ in 𝓝 s, riemannZeta (1 - z) = U z * riemannZeta z := by
    filter_upwards [hpos, hlt] with z hz0 hz1
    simpa [U, b] using (riemannZeta_one_sub (hnotneg z hz0) (hnotone z hz1))
  have hGamma : AnalyticAt ℂ Complex.Gamma s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hpos] with z hz
    apply Complex.differentiableAt_Gamma z
    exact hnotneg z hz
  have hb : b ≠ 0 := by
    simp [b, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  letI : NeZero b := ⟨hb⟩
  have hpow : AnalyticAt ℂ (fun z : ℂ => b ^ (-z)) s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [] with z
    simpa [Function.comp_def] using
      (differentiableAt_const_cpow_of_neZero b (-z)).comp z (by fun_prop)
  have harg : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) * z / 2) s := by
    fun_prop
  have hcos : AnalyticAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z / 2)) s :=
    Complex.analyticAt_cos.comp harg
  have hU : AnalyticAt ℂ U s := by
    change AnalyticAt ℂ (((fun _ : ℂ => 2) * (fun z : ℂ => b ^ (-z))) * Complex.Gamma *
      (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z / 2))) s
    exact ((analyticAt_const.mul hpow).mul hGamma).mul hcos
  have hGamma0 : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (hnotneg s h0)
  have hpow0 : b ^ (-s) ≠ 0 := by
    intro hz
    exact hb ((Complex.cpow_eq_zero_iff b (-s)).mp hz).1
  have hcos0 : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    apply (Complex.cos_ne_zero_iff).2
    intro k hk
    have hr := congrArg Complex.re hk
    have hi := congrArg Complex.im hk
    norm_num [Complex.mul_re, Complex.div_re, Complex.add_re, Complex.sub_re,
      Complex.natCast_re, Complex.intCast_re] at hr hi
    have hp : 0 < Real.pi := Real.pi_pos
    have hkeq : s.re = (2 * (k : ℝ) + 1) := by
      nlinarith [hr]
    have hk0 : (k : ℝ) < 0 := by
      by_contra hn
      have hkge : (0 : ℝ) ≤ k := le_of_not_gt hn
      nlinarith [hkeq]
    have hklt : k < 0 := by exact_mod_cast hk0
    have hkneg : (k : ℝ) ≤ -1 := by
      have hkneg_int : k ≤ -1 := by omega
      exact_mod_cast hkneg_int
    nlinarith [hkeq]
  have hU0 : U s ≠ 0 := by
    simp [U, hGamma0, hpow0, hcos0]
  have hf : AnalyticAt ℂ riemannZeta s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hlt] with z hz
    apply differentiableAt_riemannZeta
    exact hnotone z hz
  let g : ℂ → ℂ := fun z => 1 - z
  have hg : AnalyticAt ℂ g s := by
    dsimp [g]
    fun_prop
  have hgd : deriv g s ≠ 0 := by
    have hderiv : deriv g s = (-1 : ℂ) := by
      simpa [g] using (deriv_const_sub_id (𝕜 := ℂ) (x := s) (1 : ℂ))
    rw [hderiv]
    norm_num
  have hcomp : analyticOrderAt (riemannZeta ∘ g) s = analyticOrderAt riemannZeta (g s) :=
    analyticOrderAt_comp_of_deriv_ne_zero hg hgd
  have hcongr : analyticOrderAt (riemannZeta ∘ g) s = analyticOrderAt (U * riemannZeta) s := by
    apply analyticOrderAt_congr
    filter_upwards [hFE] with z hz
    simpa [Function.comp_def, g] using hz
  have hmul : analyticOrderAt (U * riemannZeta) s =
      analyticOrderAt U s + analyticOrderAt riemannZeta s :=
    analyticOrderAt_mul hU hf
  have hUord : analyticOrderAt U s = 0 := hU.analyticOrderAt_eq_zero.mpr hU0
  have hord : analyticOrderAt riemannZeta (1 - s) = analyticOrderAt riemannZeta s := by
    rw [← hcomp, hcongr, hmul, hUord, zero_add]
  simpa [analyticOrderNatAt, g] using congrArg ENat.toNat hord

