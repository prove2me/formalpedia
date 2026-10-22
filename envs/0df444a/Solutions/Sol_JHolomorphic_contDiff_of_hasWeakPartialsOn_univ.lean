-- Prove2me | solution 1 for JHolomorphic.contDiff_of_hasWeakPartialsOn_univ
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T21:38:29.670351+00:00
-- url     : https://prove2.me/submissions/21a92c34-390c-4ee8-9f73-0f64c33820c3

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_uniformCauchySeqOn_normed_convolution
import Theorems.Thm_JHolomorphic_fderiv_normed_convolution_eq_of_hasWeakPartialsOn
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.RealDeriv



namespace JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution ENNReal

theorem contDiff_of_hasWeakPartialsOn_univ_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    {v vs vt vss vst vts vtt : ℂ → E} (hv : Continuous v)
    (hvsc : HasCompactSupport vs) (hvtc : HasCompactSupport vt)
    (h1 : HasWeakPartialsOn Set.univ v vs vt) (h2 : HasWeakPartialsOn Set.univ vs vss vst)
    (h3 : HasWeakPartialsOn Set.univ vt vts vtt)
    (hs : MemLp vs (ENNReal.ofReal p) volume) (ht : MemLp vt (ENNReal.ofReal p) volume)
    (hss : MemLp vss (ENNReal.ofReal p) volume) (hst : MemLp vst (ENNReal.ofReal p) volume)
    (hts : MemLp vts (ENNReal.ofReal p) volume) (htt : MemLp vtt (ENNReal.ofReal p) volume) :
    ContDiff ℝ 1 v := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hq1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 (by linarith)
  -- mollifiers
  let φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by positivity, by gcongr; norm_num⟩
  have hφr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    show Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0)
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  set w : ℕ → ℂ → E := fun n => (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] v with hw
  set S : ℕ → ℂ → E := fun n => (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] vs with hS
  set T : ℕ → ℂ → E := fun n => (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] vt with hT
  have hvli : LocallyIntegrable v volume := hv.locallyIntegrable
  have hwcd : ∀ n, ContDiff ℝ 1 (w n) := fun n =>
    (φ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) (φ n).contDiff_normed hvli
  have hSc : ∀ n, Continuous (S n) := fun n =>
    (φ n).hasCompactSupport_normed.continuous_convolution_left _ (φ n).continuous_normed
      (hs.locallyIntegrable hq1)
  have hTc : ∀ n, Continuous (T n) := fun n =>
    (φ n).hasCompactSupport_normed.continuous_convolution_left _ (φ n).continuous_normed
      (ht.locallyIntegrable hq1)
  have hwd := fun n z => fderiv_normed_convolution_eq_of_hasWeakPartialsOn (φ n) h1 hvli z
  -- uniform limits of the mollified partials
  have hUS := uniformCauchySeqOn_normed_convolution p hp φ hφr hvsc hs h2 hss hst
  have hUT := uniformCauchySeqOn_normed_convolution p hp φ hφr hvtc ht h3 hts htt
  have lim_of : ∀ F : ℕ → ℂ → E, UniformCauchySeqOn F atTop Set.univ →
      ∃ g : ℂ → E, TendstoUniformly F g atTop := by
    intro F hF
    have hpt : ∀ z, ∃ y, Tendsto (fun n => F n z) atTop (𝓝 y) := fun z =>
      cauchySeq_tendsto_of_complete (hF.cauchySeq (Set.mem_univ z))
    choose g hg using hpt
    exact ⟨g, tendstoUniformlyOn_univ.1 (hF.tendstoUniformlyOn_of_tendsto fun z _ => hg z)⟩
  obtain ⟨gS, hgS⟩ := lim_of S hUS
  obtain ⟨gT, hgT⟩ := lim_of T hUT
  have hgSc : Continuous gS := hgS.continuous (Eventually.of_forall hSc).frequently
  have hgTc : Continuous gT := hgT.continuous (Eventually.of_forall hTc).frequently
  -- decomposition of real-linear maps on `ℂ`
  have dec : ∀ A : ℂ →L[ℝ] E,
      A = Complex.reCLM.smulRight (A 1) + Complex.imCLM.smulRight (A Complex.I) := by
    intro A
    ext z
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      apply Complex.ext <;> simp
    rw [ContinuousLinearMap.add_apply, smulRight_apply, smulRight_apply, Complex.reCLM_apply,
      Complex.imCLM_apply]
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul]
  set G : ℂ → ℂ →L[ℝ] E := fun z =>
    Complex.reCLM.smulRight (gS z) + Complex.imCLM.smulRight (gT z) with hG
  have hnb : ∀ a b : E, ‖Complex.reCLM.smulRight a + Complex.imCLM.smulRight b‖ ≤ ‖a‖ + ‖b‖ :=
    fun a b => (norm_add_le _ _).trans (add_le_add
      (opNorm_le_bound _ (norm_nonneg _) fun z => by
        rw [smulRight_apply, Complex.reCLM_apply, norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (norm_nonneg _))
      (opNorm_le_bound _ (norm_nonneg _) fun z => by
        rw [smulRight_apply, Complex.imCLM_apply, norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) (norm_nonneg _)))
  have hTU : TendstoUniformly (fun n z => fderiv ℝ (w n) z) G atTop := by
    rw [Metric.tendstoUniformly_iff] at hgS hgT ⊢
    intro ε hε
    filter_upwards [hgS (ε / 2) (by linarith), hgT (ε / 2) (by linarith)] with n hn1 hn2
    intro z
    rw [dist_eq_norm]
    have e : G z - fderiv ℝ (w n) z = Complex.reCLM.smulRight (gS z - S n z) +
        Complex.imCLM.smulRight (gT z - T n z) := by
      rw [dec (fderiv ℝ (w n) z), (hwd n z).1, (hwd n z).2]
      ext y
      simp only [hG, hS, hT, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        smulRight_apply, smul_sub]
      abel
    rw [e]
    have := hnb (gS z - S n z) (gT z - T n z)
    rw [← dist_eq_norm, ← dist_eq_norm] at this
    linarith [hn1 z, hn2 z]
  have hder : ∀ x, HasFDerivAt v (G x) x :=
    hasFDerivAt_of_tendstoUniformly hTU
      (fun n x => ((hwcd n).differentiable one_ne_zero x).hasFDerivAt)
      (fun x => ContDiffBump.convolution_tendsto_right_of_continuous hφr hv x)
  have hGc : Continuous G :=
    ((smulRightL ℝ ℂ E Complex.reCLM).continuous.comp hgSc).add
      ((smulRightL ℝ ℂ E Complex.imCLM).continuous.comp hgTc)
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hder x).differentiableAt, ?_⟩
  have : fderiv ℝ v = G := funext fun x => (hder x).fderiv
  rw [this]
  exact hGc

end JHolomorphic

open JHolomorphic

open MeasureTheory

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    {v vs vt vss vst vts vtt : ℂ → E} (hv : Continuous v)
    (hvsc : HasCompactSupport vs) (hvtc : HasCompactSupport vt)
    (h1 : HasWeakPartialsOn Set.univ v vs vt) (h2 : HasWeakPartialsOn Set.univ vs vss vst)
    (h3 : HasWeakPartialsOn Set.univ vt vts vtt)
    (hs : MemLp vs (ENNReal.ofReal p) volume) (ht : MemLp vt (ENNReal.ofReal p) volume)
    (hss : MemLp vss (ENNReal.ofReal p) volume) (hst : MemLp vst (ENNReal.ofReal p) volume)
    (hts : MemLp vts (ENNReal.ofReal p) volume) (htt : MemLp vtt (ENNReal.ofReal p) volume) :
    ContDiff ℝ 1 v :=
  contDiff_of_hasWeakPartialsOn_univ_aux p hp hv hvsc hvtc h1 h2 h3 hs ht hss hst hts htt
