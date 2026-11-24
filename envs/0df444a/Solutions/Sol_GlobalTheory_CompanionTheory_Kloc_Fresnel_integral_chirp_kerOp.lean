-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.integral_chirp_kerOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:27:56.213807+00:00
-- url     : https://prove2.me/submissions/c413b1d1-f199-43cd-ad4e-4a4480b7836d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_chirpS_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_kerS_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_norm_cexp_le_one_of_re_nonpos
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_integral_gauss_kerOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
theorem _root_.solution (C : ℂ) (k a : ℝ) (hk : k ≠ 0) (ha : a = 2 * |k|) (R : V ≃ₗᵢ[ℝ] V)
    (φ : 𝓢(V, ℂ)) :
    ∫ t : V, chirp k t * kerOp C a R (chirpS k φ) t =
      C * (Real.pi / (-(2 * Real.pi * k * I) : ℂ)) ^ (Module.finrank ℝ V / 2 : ℂ) * ∫ v, φ v := by
  have ha0 : a ≠ 0 := by rw [ha]; have := abs_pos.2 hk; positivity
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  set b₀ : ℂ := -(2 * Real.pi * k * I) with hb₀
  have hb₀0 : b₀ ≠ 0 := by
    simp only [hb₀, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hkC) Complex.I_ne_zero
  have hb₀re : b₀.re = 0 := by simp [hb₀]
  set b : ℝ → ℂ := fun δ => (δ : ℂ) + b₀ with hbdef
  have hbc : Continuous b := by simp only [hbdef]; fun_prop
  have hb0 : b 0 = b₀ := by simp [hbdef]
  have hbre : ∀ δ : ℝ, (b δ).re = δ := by intro δ; simp [hbdef, hb₀re]
  have hpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  set f := chirpS k φ with hf
  have hKi : Integrable (kerOp C a R f) := by
    rw [← kerS_coe C a ha0 R f]; exact (kerS C a ha0 R f).integrable

  have h1 : Filter.Tendsto (fun δ : ℝ => ∫ t : V, cexp (-(b δ) * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t : V, chirp k t * kerOp C a R f t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖kerOp C a R f t‖) ?_ ?_ hKi.norm ?_
    · refine Filter.Eventually.of_forall fun δ => ?_
      refine Continuous.aestronglyMeasurable ?_ |>.mul hKi.aestronglyMeasurable
      fun_prop
    · filter_upwards [hpos] with δ hδ
      refine Filter.Eventually.of_forall fun t => ?_
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) (norm_cexp_le_one_of_re_nonpos ?_)
      have : (-(b δ) * ((‖t‖ ^ 2 : ℝ) : ℂ)).re = -(δ * ‖t‖ ^ 2) := by
        rw [Complex.re_mul_ofReal, Complex.neg_re, hbre]; ring
      rw [this]
      have : 0 ≤ δ * ‖t‖ ^ 2 := by positivity
      linarith
    · refine Filter.Eventually.of_forall fun t => ?_
      have hc : Continuous fun δ : ℝ => cexp (-(b δ) * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t := by
        fun_prop
      have hv : cexp (-(b 0) * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t =
          chirp k t * kerOp C a R f t := by
        rw [hb0, chirp, hb₀]
        congr 2
        ring
      exact ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).congr' (by simp) |>.trans (by rw [hv])

  have hsl : (Real.pi / b₀ : ℂ) ∈ Complex.slitPlane := by
    have : (Real.pi / b₀ : ℂ) = ((1 / (2 * k) : ℝ) : ℂ) * I := by
      rw [hb₀]
      push_cast
      field_simp
      simp
    rw [this, Complex.mem_slitPlane_iff]
    right
    have : (1 / (2 * k) : ℝ) ≠ 0 := by positivity
    simpa using this
  have h2 : Filter.Tendsto (fun δ : ℝ => (Real.pi / b δ : ℂ) ^ (Module.finrank ℝ V / 2 : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Real.pi / b₀ : ℂ) ^ (Module.finrank ℝ V / 2 : ℂ))) := by
    have hc : Filter.Tendsto (fun δ : ℝ => (Real.pi / b δ : ℂ)) (nhds 0) (nhds (Real.pi / b₀ : ℂ)) := by
      have := (hbc.tendsto 0)
      rw [hb0] at this
      exact tendsto_const_nhds.div this hb₀0
    exact ((continuousAt_cpow_const hsl).tendsto.comp hc).mono_left nhdsWithin_le_nhds
  have h3 : Filter.Tendsto (fun δ : ℝ => ∫ v : V, f v *
        cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b δ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ v, φ v)) := by
    have hfi : Integrable (f : V → ℂ) := f.integrable
    refine tendsto_integral_filter_of_dominated_convergence (fun v => ‖f v‖) ?_ ?_ hfi.norm ?_
    · filter_upwards [hpos] with δ hδ
      have hbδ : b δ ≠ 0 := by
        intro h; have := hbre δ; rw [h] at this; simp at this; linarith
      refine hfi.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
      refine Complex.continuous_exp.comp (Continuous.neg (Continuous.div_const ?_ _))
      fun_prop
    · filter_upwards [hpos] with δ hδ
      refine Filter.Eventually.of_forall fun v => ?_
      rw [norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) (norm_cexp_le_one_of_re_nonpos ?_)
      have hr : (0 : ℝ) ≤ Real.pi ^ 2 * a ^ 2 * ‖v‖ ^ 2 := by positivity
      have e : ((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b δ) =
          ((Real.pi ^ 2 * a ^ 2 * ‖v‖ ^ 2 : ℝ) : ℂ) / b δ := by push_cast; ring
      rw [e, Complex.neg_re, Complex.div_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero, hbre]
      have : 0 ≤ (Real.pi ^ 2 * a ^ 2 * ‖v‖ ^ 2) * δ / Complex.normSq (b δ) :=
        div_nonneg (mul_nonneg hr hδ.le) (Complex.normSq_nonneg _)
      linarith
    · refine Filter.Eventually.of_forall fun v => ?_
      have hc : Filter.Tendsto (fun δ : ℝ => f v *
          cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b δ))) (nhds 0)
          (nhds (f v * cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b₀)))) := by
        have := (hbc.tendsto 0)
        rw [hb0] at this
        exact (((tendsto_const_nhds.div this hb₀0).neg).cexp).const_mul _
      have hv : f v * cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b₀)) = φ v := by
        rw [hf, chirpS_apply, chirp, mul_comm (cexp _) (φ v), mul_assoc, ← Complex.exp_add]
        have ha2 : (a : ℂ) ^ 2 = 4 * (k : ℂ) ^ 2 := by
          have : a ^ 2 = 4 * k ^ 2 := by rw [ha, mul_pow, sq_abs]; norm_num
          exact_mod_cast this
        have : (2 * Real.pi * I * (k : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ) +
            -((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b₀)) = 0 := by
          rw [ha2, hb₀]
          field_simp
          ring_nf
          simp only [Complex.I_sq]
          ring
        rw [this]
        simp
      rw [← hv]
      exact hc.mono_left nhdsWithin_le_nhds
  have h4 := ((h2.const_mul C).mul h3)
  have h5 : (fun δ : ℝ => ∫ t : V, cexp (-(b δ) * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun δ : ℝ => C * (Real.pi / b δ : ℂ) ^ (Module.finrank ℝ V / 2 : ℂ) * ∫ v : V, f v *
        cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b δ)) := by
    filter_upwards [hpos] with δ hδ
    exact integral_gauss_kerOp C a ha0 R (by rw [hbre]; exact hδ) f
  exact tendsto_nhds_unique (h1.congr' h5) h4
end GlobalTheory.CompanionTheory.Kloc.Fresnel
