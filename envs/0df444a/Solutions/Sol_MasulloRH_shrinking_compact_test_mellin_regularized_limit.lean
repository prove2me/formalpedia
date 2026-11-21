-- Prove2me | solution 1 for MasulloRH.shrinking_compact_test_mellin_regularized_limit
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:51:39.603096+00:00
-- url     : https://prove2.me/submissions/058b44ce-df90-4f9b-815a-1d956097b898

import Mathlib
import Theorems.Thm_MasulloRH_weighted_positive_zeta_zeros_two_term_scaling
import Theorems.Thm_MasulloRH_shrinking_compact_test_mellin_zero_scaling

open MeasureTheory Filter Set FourierTransform
open scoped Topology SchwartzMap FourierTransform

namespace MasulloAudit

private abbrev PositiveZero :=
  {z : ℂ // Zeta23.IsNontrivialZero z ∧ 0 < z.im}

private noncomputable def complexSchwartzTest (h : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℂ) :=
  h.postcompCLM Complex.ofRealCLM

private lemma complexSchwartzTest_apply (h : 𝓢(ℝ, ℝ)) (x : ℝ) :
    complexSchwartzTest h x = (h x : ℂ) := rfl

private lemma hasCompactSupport_complexSchwartzTest (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) :
    HasCompactSupport (complexSchwartzTest h) := by
  have he : Function.support (complexSchwartzTest h) = Function.support h := by
    ext x
    simp [Function.mem_support, complexSchwartzTest_apply]
  unfold HasCompactSupport tsupport at *
  rwa [he]

private noncomputable def reFourierTest (h : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℝ) :=
  (𝓕 (complexSchwartzTest h)).postcompCLM Complex.reCLM

private lemma reFourierTest_apply (h : 𝓢(ℝ, ℝ)) (ξ : ℝ) :
    reFourierTest h ξ = (𝓕 (complexSchwartzTest h : ℝ → ℂ) ξ).re := rfl

private lemma reFourierTest_eq_cos (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) (ξ : ℝ) :
    reFourierTest h ξ = ∫ x : ℝ, Real.cos (-2*Real.pi*x*ξ)*h x := by
  let f := complexSchwartzTest h
  have hfC := hasCompactSupport_complexSchwartzTest h hC
  have hC : Continuous (fun x : ℝ ↦ Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I)*f x) := by
    have hx : Continuous (fun x : ℝ ↦ -2*Real.pi*x*ξ) := by fun_prop
    exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hx).mul_const _)).mul f.continuous
  have hI := hC.integrable_of_hasCompactSupport (μ := volume) hfC.mul_left
  have he := integral_re (𝕜 := ℂ) hI
  change (∫ x : ℝ, (Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I)*f x).re) =
    (∫ x : ℝ, Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I)*f x).re at he
  rw [reFourierTest_apply, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  change (Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I)*complexSchwartzTest h x).re = _
  rw [complexSchwartzTest_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

private lemma reFourierTest_even (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) :
    Function.Even (reFourierTest h) := by
  intro ξ
  rw [reFourierTest_eq_cos h hC, reFourierTest_eq_cos h hC]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show -2*Real.pi*x*(-ξ) = -(-2*Real.pi*x*ξ) by ring, Real.cos_neg]

private lemma reFourierTest_integral (h : 𝓢(ℝ, ℝ)) :
    (∫ ξ : ℝ, reFourierTest h ξ) = h 0 := by
  let f := complexSchwartzTest h
  have hF : Integrable (𝓕 (f : ℝ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 f).integrable
  have hInv := f.integrable.fourierInv_fourier_eq hF (v := (0:ℝ)) f.continuous.continuousAt
  rw [Real.fourierInv_eq] at hInv
  have hAll : (∫ ξ : ℝ, 𝓕 (f : ℝ → ℂ) ξ) = f 0 := by
    simpa only [inner_zero_right, AddChar.map_zero_eq_one, one_smul] using hInv
  have he := integral_re (𝕜 := ℂ) hF
  change (∫ ξ : ℝ, (𝓕 (f : ℝ → ℂ) ξ).re) = (∫ ξ : ℝ, 𝓕 (f : ℝ → ℂ) ξ).re at he
  simp only [reFourierTest_apply]
  rw [he, hAll]
  exact Complex.ofReal_re _

private lemma integral_positive_reFourierTest (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) :
    (∫ ξ in Ioi (0:ℝ), reFourierTest h ξ) = h 0 / 2 := by
  let F := reFourierTest h
  have hE : (∫ ξ in Iic (0:ℝ), F ξ) = ∫ ξ in Ioi (0:ℝ), F ξ := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]
    simp only [neg_zero]
    exact setIntegral_congr_fun measurableSet_Ioi (fun ξ _ ↦ reFourierTest_even h hC ξ)
  have hSum := integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi (F.integrable (μ := volume))
  have hFull : (∫ ξ : ℝ, F ξ) = h 0 := reFourierTest_integral h
  rw [compl_Ioi, hE, hFull] at hSum
  change (∫ ξ in Ioi (0:ℝ), F ξ) = h 0 / 2
  linarith

private lemma integrable_log_mul_schwartz (g : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ ↦ (Real.log |x| : ℂ) * g x) := by
  let K := Icc (-1 : ℝ) 1
  let f (x : ℝ) := (Real.log |x| : ℂ) * g x
  have hf : Measurable f := by
    unfold f
    exact (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp measurable_abs)).mul
      g.continuous.measurable
  have hLog : IntegrableOn (fun x : ℝ ↦ Real.log |x|) K := by
    simp only [Real.log_abs, K]
    have h : IntegrableOn (fun x : ℝ ↦ Real.log x) (Ioc (-1 : ℝ) 1) :=
      (intervalIntegral.intervalIntegrable_log' (a := (-1 : ℝ)) (b := 1)).1
    simpa only [IntegrableOn, Measure.restrict_congr_set Ioc_ae_eq_Icc] using h
  let C := SchwartzMap.seminorm ℝ 0 0 g
  have hNear : IntegrableOn f K := by
    refine (hLog.norm.const_mul C).mono' hf.aestronglyMeasurable ?_
    filter_upwards [] with x
    dsimp only [f]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ g x) (abs_nonneg _)
  have hFar : IntegrableOn f Kᶜ := by
    have hI := (g.integrable_pow_mul volume 1).integrableOn (s := Kᶜ)
    refine hI.mono' hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hx
    have hx' : 1 < |x| := lt_of_not_ge fun he ↦ hx (abs_le.mp he)
    have hx'' : 0 < |x| := zero_lt_one.trans hx'
    dsimp only [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hx'.le), pow_one]
    exact mul_le_mul_of_nonneg_right
      ((Real.log_le_sub_one_of_pos hx'').trans (sub_le_self _ zero_le_one)) (norm_nonneg _)
  have h := hNear.union hFar
  simpa only [union_compl_self, integrableOn_univ, f] using h


private noncomputable def signedMellinTest (h : 𝓢(ℝ, ℝ)) (ε : ℝ) (z : ℂ) : ℝ :=
  (∫ x : ℝ, Complex.exp ((ε:ℂ)*(z-1/2)*(x:ℂ)) * (h x : ℂ)).re

private noncomputable def realFourierLogPairing (h : 𝓢(ℝ, ℝ)) : ℝ :=
  (∫ u : ℝ, (Real.log |u| : ℂ) * 𝓕 (complexSchwartzTest h : ℝ → ℂ) u).re

private lemma integrable_log_mul_cos_transform (h : 𝓢(ℝ, ℝ)) :
    Integrable (fun u : ℝ ↦ Real.log |u| * reFourierTest h u) := by
  let f := complexSchwartzTest h
  have hi := (integrable_log_mul_schwartz (𝓕 f)).re
  change Integrable (fun u : ℝ ↦ ((Real.log |u| : ℂ) * (𝓕 f) u).re) at hi
  apply hi.congr
  filter_upwards [] with u
  rw [reFourierTest_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

private lemma integrableOn_log_mul_cos_transform (h : 𝓢(ℝ, ℝ)) :
    IntegrableOn (fun u : ℝ ↦ Real.log u * reFourierTest h u) (Ioi 0) := by
  refine (integrable_log_mul_cos_transform h).integrableOn.congr_fun
    (fun u hu ↦ ?_) measurableSet_Ioi
  dsimp only
  rw [abs_of_pos (show 0 < u from hu)]

private lemma realFourierLogPairing_eq_twice_half (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) :
    realFourierLogPairing h = 2 * ∫ u in Ioi (0:ℝ), Real.log u * reFourierTest h u := by
  let f := complexSchwartzTest h
  let g (u : ℝ) := Real.log |u| * reFourierTest h u
  have hG : Integrable g := integrable_log_mul_cos_transform h
  have hGi : Integrable (fun u : ℝ ↦ (Real.log |u| : ℂ)*𝓕 (f : ℝ → ℂ) u) := by
    simpa only [SchwartzMap.fourier_coe] using integrable_log_mul_schwartz (𝓕 f)
  have hRi := integral_re (𝕜 := ℂ) hGi
  change (∫ u : ℝ, ((Real.log |u| : ℂ)*𝓕 (f : ℝ → ℂ) u).re) =
    realFourierLogPairing h at hRi
  have he : (∫ u : ℝ, g u) = realFourierLogPairing h := by
    rw [← hRi]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [g]
    rw [reFourierTest_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hEv : Function.Even g := fun u ↦ by
    dsimp only [g]
    rw [abs_neg, reFourierTest_even h hC u]
  have hH : (∫ u in Iic (0:ℝ), g u) = ∫ u in Ioi (0:ℝ), g u := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]
    simp only [neg_zero]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u _ ↦ hEv u)
  have hHalf : (∫ u in Ioi (0:ℝ), g u) = ∫ u in Ioi (0:ℝ), Real.log u * reFourierTest h u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only [g]
    rw [abs_of_pos (show 0 < u from hu)]
  have hAll := integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi hG
  rw [compl_Ioi,hH,hHalf,he] at hAll
  linarith

private lemma tendsto_scale_log_zero :
    Tendsto (fun δ : ℝ ↦ δ*(1+Real.log δ⁻¹)) (𝓝[>] 0) (𝓝 0) := by
  have hLog := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one
  simp only [Real.rpow_one] at hLog
  have h := (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))).sub hLog
  rw [sub_zero] at h
  refine h.congr ?_
  intro δ
  rw [id_eq, Real.log_inv]
  ring

private lemma tendsto_div_scale {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε : ℝ ↦ ε/c) (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hC : Continuous (fun ε : ℝ ↦ ε/c) := continuous_id.div_const _
    simpa only [zero_div] using
      (hC.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact div_pos hε hc

private lemma tendsto_projected_fourier_finite_part (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) :
    Tendsto (fun ε : ℝ ↦ 2*ε*(∑' z : PositiveZero,
        (Zeta23.zeroMult z.val : ℝ) * reFourierTest h (ε*z.val.im/(2*Real.pi))) - h 0*Real.log ε⁻¹)
      (𝓝[>] 0) (𝓝 (realFourierLogPairing h)) := by
  let c := 2*Real.pi
  have hc₁ : 1 ≤ c := by dsimp [c]; linarith [Real.pi_gt_three]
  have hc : 0 < c := zero_lt_one.trans_le hc₁
  let F := reFourierTest h
  let S (ε : ℝ) : ℝ := 2*ε*(∑' z : PositiveZero,
    (Zeta23.zeroMult z.val : ℝ) * F (ε*z.val.im/c))
  let T := realFourierLogPairing h
  obtain ⟨B,hB,hBound⟩ := MasulloRH.weighted_positive_zeta_zeros_two_term_scaling F
  have hF : (∫ u in Ioi (0:ℝ), F u) = h 0/2 := integral_positive_reFourierTest h hC
  have hT : T = 2*(∫ u in Ioi (0:ℝ), Real.log u*F u) :=
    realFourierLogPairing_eq_twice_half h hC
  have hJ : (∫ u in Ioi (0:ℝ), (Real.log u-Real.log c)*F u) =
      (∫ u in Ioi (0:ℝ), Real.log u*F u)-Real.log c*(∫ u in Ioi (0:ℝ), F u) := by
    simp_rw [sub_mul]
    rw [integral_sub (integrableOn_log_mul_cos_transform h)
      (F.integrable.const_mul _).integrableOn, integral_const_mul]
  have hLim : Tendsto (fun ε : ℝ ↦ S ε-h 0*Real.log ε⁻¹-T) (𝓝[>] 0) (𝓝 0) := by
    let D (ε : ℝ) := (2*c*B) * ((ε/c)*(1+Real.log ((ε/c)⁻¹)))
    have hD : Tendsto D (𝓝[>] 0) (𝓝 0) := by
      simpa only [D,mul_zero,Function.comp_def] using
        (tendsto_scale_log_zero.comp (tendsto_div_scale hc)).const_mul (2*c*B)
    refine squeeze_zero_norm' ?_ hD
    have hSmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < c := nhdsWithin_le_nhds (Iio_mem_nhds hc)
    filter_upwards [self_mem_nhdsWithin,hSmall] with ε hε hε'
    have hε0 : 0 < ε := hε
    let δ := ε/c
    have hδ : 0 < δ := div_pos hε0 hc
    have hδ₁ : δ ≤ 1 := (div_le_one₀ hc).mpr hε'.le
    obtain ⟨_,hBδ⟩ := hBound δ hδ hδ₁
    let U := ∑' z : PositiveZero, (Zeta23.zeroMult z.val : ℝ)*F (δ*z.val.im)
    change |δ*U - (1/c)*Real.log δ⁻¹*(∫ u in Ioi (0:ℝ), F u) -
      (1/c)*(∫ u in Ioi (0:ℝ), (Real.log u-Real.log c)*F u)| ≤ _ at hBδ
    have hS : S ε = 2*ε*U := by
      unfold S U δ
      congr 1
      apply tsum_congr
      intro z
      congr 2
      ring
    have hL : Real.log δ⁻¹ = Real.log ε⁻¹+Real.log c := by
      unfold δ
      rw [Real.log_inv, Real.log_div hε0.ne' hc.ne', Real.log_inv]
      ring
    have hEq : S ε-h 0*Real.log ε⁻¹-T =
        (2*c)*(δ*U - (1/c)*Real.log δ⁻¹*(∫ u in Ioi (0:ℝ),F u) -
          (1/c)*(∫ u in Ioi (0:ℝ), (Real.log u-Real.log c)*F u)) := by
      rw [hS,hJ,hF,hT,hL]
      unfold δ
      field_simp [hc.ne']
      ring
    rw [Real.norm_eq_abs,hEq,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*c)]
    calc
      _ ≤ (2*c)*(B*δ*(1+Real.log δ⁻¹)) := mul_le_mul_of_nonneg_left hBδ (by positivity)
      _ = D ε := by dsimp [D,δ]; ring
  have hShift := hLim.add (tendsto_const_nhds (x := T))
  rw [zero_add] at hShift
  refine hShift.congr (fun ε ↦ ?_)
  change S ε-h 0*Real.log ε⁻¹-T+T = S ε-h 0*Real.log ε⁻¹
  ring


/-- The finite spectral term after subtracting the leading logarithm for the actual
Mellin values of a shrinking real compact test. -/
theorem shrinking_compact_test_mellin_regularized_limit_aux (h : 𝓢(ℝ, ℝ)) (hC : HasCompactSupport h) :
    Tendsto (fun ε : ℝ ↦ 2*ε*(∑' z : PositiveZero,
        (Zeta23.zeroMult z.val : ℝ)*signedMellinTest h ε z.val) - h 0*Real.log ε⁻¹)
      (𝓝[>] 0) (𝓝 (realFourierLogPairing h)) := by
  let c := 2*Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  let M (ε : ℝ) (z : PositiveZero) := (Zeta23.zeroMult z.val : ℝ)*signedMellinTest h ε z.val
  let F := reFourierTest h
  let W (ε : ℝ) (z : PositiveZero) := (Zeta23.zeroMult z.val : ℝ)*F (ε*z.val.im/c)
  have hPrevious := MasulloRH.shrinking_compact_test_mellin_zero_scaling h hC
  obtain ⟨ε₀,hε₀,_,_,hM⟩ := hPrevious.1
  obtain ⟨_,_,hW⟩ := MasulloRH.weighted_positive_zeta_zeros_two_term_scaling F
  have hTilt : Tendsto (fun ε : ℝ ↦ ∑' z : PositiveZero,
      (2*ε)*((Zeta23.zeroMult z.val : ℝ) *
        (signedMellinTest h ε z.val - F (ε*z.val.im/c)))) (𝓝[>] 0) (𝓝 0) :=
    hPrevious.2
  have hSmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < min ε₀ c :=
    nhdsWithin_le_nhds (Iio_mem_nhds (lt_min hε₀ hc))
  have hShift : Tendsto (fun ε : ℝ ↦ (2*ε)*(∑' z : PositiveZero, M ε z) -
      (2*ε)*(∑' z : PositiveZero, W ε z)) (𝓝[>] 0) (𝓝 0) := by
    refine hTilt.congr' ?_
    filter_upwards [self_mem_nhdsWithin,hSmall] with ε hε hε'
    have hε0 : 0 < ε := hε
    have hεM : ε ≤ ε₀ := (hε'.trans_le (min_le_left _ _)).le
    have hεW : ε/c ≤ 1 := (div_le_one₀ hc).mpr (hε'.trans_le (min_le_right _ _)).le
    have hMS : Summable (M ε) := (hM ε hε0 hεM).1
    have hWS : Summable (W ε) := by
      have hS := (hW (ε/c) (div_pos hε0 hc) hεW).1
      refine hS.congr (fun z ↦ ?_)
      dsimp only [W]
      rw [show ε/c*z.val.im = ε*z.val.im/c by ring]
    have he : (fun z : PositiveZero ↦ (2*ε)*((Zeta23.zeroMult z.val : ℝ) *
        (signedMellinTest h ε z.val - F (ε*z.val.im/c)))) =
        fun z : PositiveZero ↦ (2*ε)*(M ε z-W ε z) := by
      funext z
      unfold M W
      ring
    rw [he, tsum_mul_left, hMS.tsum_sub hWS, mul_sub]
  have hLim := hShift.add (tendsto_projected_fourier_finite_part h hC)
  rw [zero_add] at hLim
  refine hLim.congr ?_
  intro ε
  change (2*ε)*(∑' z : PositiveZero, M ε z) - (2*ε)*(∑' z : PositiveZero, W ε z) +
      ((2*ε)*(∑' z : PositiveZero, W ε z) - h 0*Real.log ε⁻¹) =
    (2*ε)*(∑' z : PositiveZero, M ε z) - h 0*Real.log ε⁻¹
  ring

end MasulloAudit

open MeasureTheory

theorem solution (h : SchwartzMap ℝ ℝ) (hC : HasCompactSupport h) :
    Filter.Tendsto
      (fun ε : ℝ ↦ 2*ε*(∑' z : {z : ℂ // Zeta23.IsNontrivialZero z ∧ 0 < z.im},
          (Zeta23.zeroMult z.val : ℝ) *
            (∫ x : ℝ, Complex.exp ((ε:ℂ)*(z.val-1/2)*(x:ℂ)) * (h x : ℂ)).re) -
        h 0*Real.log ε⁻¹)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((∫ u : ℝ, (Real.log |u| : ℂ) *
        FourierTransform.fourier (fun x : ℝ ↦ (h x : ℂ)) u).re)) := by
  exact MasulloAudit.shrinking_compact_test_mellin_regularized_limit_aux h hC
