-- Prove2me | solution 1 for NumberField.TateGlobal.integrableOn_and_differentiable_setIntegral_mul_ideleNorm_cpow_of_norm_le_min_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/44142537-1a58-5715-aa06-565698af4f29

import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_integrableOn_and_differentiable_setIntegral_mul_ideleNorm_cpow_of_norm_le_min_pow
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField NumberField.TateGlobal MeasureTheory

noncomputable section

namespace Ws1
namespace K1

open Complex in

theorem differentiable_integral_mul_exp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w : α → ℂ} {ℓ : α → ℝ}
    (hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun a => w a * Complex.exp (s * ℓ a)) μ)
    (hmeas' : ∀ s : ℂ, AEStronglyMeasurable (fun a => w a * ℓ a * Complex.exp (s * ℓ a)) μ)
    (hdom : ∀ s₀ : ℂ, ∃ b : α → ℝ, Integrable b μ ∧
      (∀ᵐ a ∂μ, ∀ s : ℂ, s ∈ Metric.ball s₀ 1 →
        (1 + |ℓ a|) * (‖w a‖ * Real.exp (s.re * ℓ a)) ≤ b a)) :
    Differentiable ℂ fun s : ℂ => ∫ a, w a * Complex.exp (s * ℓ a) ∂μ := by
  intro s₀
  obtain ⟨b, hb_int, hb⟩ := hdom s₀
  have hnorm : ∀ (s : ℂ) (a : α), ‖w a * Complex.exp (s * ℓ a)‖
      = ‖w a‖ * Real.exp (s.re * ℓ a) := by
    intro s a
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hnorm' : ∀ (s : ℂ) (a : α), ‖w a * ℓ a * Complex.exp (s * ℓ a)‖
      = |ℓ a| * (‖w a‖ * Real.exp (s.re * ℓ a)) := by
    intro s a
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have : (s * (ℓ a : ℂ)).re = s.re * ℓ a := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [this]
    ring
  have hF_int : Integrable (fun a => w a * Complex.exp (s₀ * ℓ a)) μ := by
    refine Integrable.mono' hb_int (hmeas s₀) ?_
    filter_upwards [hb] with a ha
    rw [hnorm s₀ a]
    calc ‖w a‖ * Real.exp (s₀.re * ℓ a)
        ≤ (1 + |ℓ a|) * (‖w a‖ * Real.exp (s₀.re * ℓ a)) := by
          have h1 : (0:ℝ) ≤ ‖w a‖ * Real.exp (s₀.re * ℓ a) :=
            mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
          nlinarith [abs_nonneg (ℓ a)]
      _ ≤ b a := ha s₀ (Metric.mem_ball_self one_pos)
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun (s : ℂ) (a : α) => w a * ℓ a * Complex.exp (s * ℓ a))
    (bound := b)
    (Metric.ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun s => hmeas s)
    hF_int
    (hmeas' s₀)
    (by
      filter_upwards [hb] with a ha s hs
      rw [hnorm' s a]
      calc |ℓ a| * (‖w a‖ * Real.exp (s.re * ℓ a))
          ≤ (1 + |ℓ a|) * (‖w a‖ * Real.exp (s.re * ℓ a)) := by
            have h1 : (0:ℝ) ≤ ‖w a‖ * Real.exp (s.re * ℓ a) :=
              mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
            nlinarith [abs_nonneg (ℓ a)]
        _ ≤ b a := ha s hs)
    hb_int
    (by
      filter_upwards with a s _
      have hinner : HasDerivAt (fun s : ℂ => s * (ℓ a : ℂ)) (ℓ a : ℂ) s := by
        simpa using (hasDerivAt_id s).mul_const ((ℓ a : ℝ) : ℂ)
      have hexp : HasDerivAt (fun s : ℂ => Complex.exp (s * ℓ a))
          (Complex.exp (s * ℓ a) * (ℓ a : ℂ)) s :=
        (Complex.hasDerivAt_exp (s * ℓ a)).comp s hinner
      have := hexp.const_mul (w a)
      convert this using 1
      · rfl
      ring)
  exact (hkey.2).differentiableAt

theorem rpow_le_rpow_add_one_add_rpow_sub_one {x σ σ₀ : ℝ} (hx : 0 < x) (h : |σ - σ₀| < 1) :
    x ^ σ ≤ x ^ (σ₀ + 1) + x ^ (σ₀ - 1) := by
  have h1 : σ ≤ σ₀ + 1 := by linarith [(abs_lt.mp h).2]
  have h2 : σ₀ - 1 ≤ σ := by linarith [(abs_lt.mp h).1]
  rcases le_or_gt 1 x with hx1 | hx1
  · calc x ^ σ ≤ x ^ (σ₀ + 1) := Real.rpow_le_rpow_of_exponent_le hx1 h1
      _ ≤ x ^ (σ₀ + 1) + x ^ (σ₀ - 1) := le_add_of_nonneg_right (Real.rpow_nonneg hx.le _)
  · calc x ^ σ ≤ x ^ (σ₀ - 1) := Real.rpow_le_rpow_of_exponent_ge hx hx1.le h2
      _ ≤ x ^ (σ₀ + 1) + x ^ (σ₀ - 1) := le_add_of_nonneg_left (Real.rpow_nonneg hx.le _)

theorem one_add_abs_log_le {x : ℝ} (hx : 0 < x) : 1 + |Real.log x| ≤ 1 + x + x⁻¹ := by
  have h1 : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx]
  have h2 : -Real.log x ≤ x⁻¹ := by
    rw [← Real.log_inv]
    linarith [Real.log_le_sub_one_of_pos (inv_pos.mpr hx)]
  have h3 : |Real.log x| ≤ x + x⁻¹ := by
    rw [abs_le]
    constructor
    · linarith [hx.le]
    · linarith [(inv_pos.mpr hx).le]
  linarith

theorem expand_six {x σ₀ : ℝ} (hx : 0 < x) :
    (1 + x + x⁻¹) * (x ^ (σ₀ + 1) + x ^ (σ₀ - 1)) =
      x ^ (σ₀ + 1) + x ^ (σ₀ - 1) + x ^ (σ₀ + 2) + x ^ σ₀ + x ^ σ₀ + x ^ (σ₀ - 2) := by
  have hx0 : x ≠ 0 := hx.ne'
  have e1 : x ^ (σ₀ + 1) = x ^ σ₀ * x := Real.rpow_add_one hx0 σ₀
  have e2 : x ^ (σ₀ - 1) = x ^ σ₀ / x := Real.rpow_sub_one hx0 σ₀
  have e3 : x ^ (σ₀ + 2) = x ^ σ₀ * x * x := by
    rw [show σ₀ + 2 = (σ₀ + 1) + 1 by ring, Real.rpow_add_one hx0, e1]
  have e4 : x ^ (σ₀ - 2) = x ^ σ₀ / x / x := by
    rw [show σ₀ - 2 = (σ₀ - 1) - 1 by ring, Real.rpow_sub_one hx0, e2]
  rw [e1, e2, e3, e4]
  field_simp
  ring

end Ws1.K1

end

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D)
    (htemp : ∀ r : ℝ, ∃ k : ℕ, IntegrableOn
      (fun a => min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k * ideleNorm F a ^ r) D ν)
    (h : (AdeleRing (𝓞 F) F)ˣ → ℂ) (hh : AEStronglyMeasurable h (ν.restrict D))
    (hdec : ∀ k : ℕ, ∃ C : ℝ, ∀ a ∈ D, ‖h a‖ ≤ C * min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k) :
    (∀ s : ℂ, IntegrableOn (fun a => h a * ((ideleNorm F a : ℝ) : ℂ) ^ s) D ν) ∧
      Differentiable ℂ (fun s : ℂ => ∫ a in D, h a * ((ideleNorm F a : ℝ) : ℂ) ^ s ∂ν) := by

  have hN0 : ∀ a : (AdeleRing (𝓞 F) F)ˣ, 0 < ideleNorm F a := fun a => ideleNorm_pos a
  have hNc : Continuous (ideleNorm F) := NumberField.TateGlobal.continuous_ideleNorm F
  have hNm : Measurable (ideleNorm F) := hNc.measurable
  have hLc : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => Real.log (ideleNorm F a) :=
    Real.continuousOn_log.comp_continuous hNc fun a => (hN0 a).ne'

  have hcpow : ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (s : ℂ),
      ((ideleNorm F a : ℝ) : ℂ) ^ s = Complex.exp (s * (Real.log (ideleNorm F a) : ℝ)) := by
    intro a s
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hN0 a).ne'),
      ← Complex.ofReal_log (hN0 a).le, mul_comm]
  have hexp_re : ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (σ : ℝ),
      Real.exp (σ * Real.log (ideleNorm F a)) = ideleNorm F a ^ σ := by
    intro a σ
    rw [Real.rpow_def_of_pos (hN0 a), mul_comm]

  have hm0 : ∀ a : (AdeleRing (𝓞 F) F)ˣ, 0 ≤ min (ideleNorm F a) (ideleNorm F a)⁻¹ := fun a =>
    le_min (hN0 a).le (inv_pos.mpr (hN0 a)).le
  have hm1 : ∀ a : (AdeleRing (𝓞 F) F)ˣ, min (ideleNorm F a) (ideleNorm F a)⁻¹ ≤ 1 := by
    intro a
    rcases le_or_gt (ideleNorm F a) 1 with h1 | h1
    · exact min_le_of_left_le h1
    · exact min_le_of_right_le (inv_le_one_of_one_le₀ h1.le)
  have hm_meas : Measurable fun a : (AdeleRing (𝓞 F) F)ˣ => min (ideleNorm F a) (ideleNorm F a)⁻¹ :=
    hNm.min hNm.inv

  have hmono : ∀ (e : ℝ) (k K : ℕ), k ≤ K →
      IntegrableOn (fun a => min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k * ideleNorm F a ^ e) D ν →
      IntegrableOn (fun a => min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ K * ideleNorm F a ^ e) D ν := by
    intro e k K hkK hint
    refine Integrable.mono' hint ((hm_meas.pow_const K).mul (hNm.pow_const e)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun a => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (hm0 a) K) (Real.rpow_nonneg (hN0 a).le e))]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (hm0 a) (hm1 a) hkK)
      (Real.rpow_nonneg (hN0 a).le e)

  have hnorm : ∀ (s : ℂ) (a : (AdeleRing (𝓞 F) F)ˣ),
      ‖h a * ((ideleNorm F a : ℝ) : ℂ) ^ s‖ = ‖h a‖ * ideleNorm F a ^ s.re := by
    intro s a
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hN0 a)]

  have hcont_cpow : ∀ s : ℂ, Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => ((ideleNorm F a : ℝ) : ℂ) ^ s :=
    fun s => (Complex.continuous_ofReal.comp hNc).cpow continuous_const fun a =>
      Complex.ofReal_mem_slitPlane.mpr (hN0 a)
  have haesm : ∀ s : ℂ,
      AEStronglyMeasurable (fun a => h a * ((ideleNorm F a : ℝ) : ℂ) ^ s) (ν.restrict D) :=
    fun s => hh.mul (hcont_cpow s).aestronglyMeasurable

  have hint : ∀ s : ℂ, IntegrableOn (fun a => h a * ((ideleNorm F a : ℝ) : ℂ) ^ s) D ν := by
    intro s
    obtain ⟨k, hk⟩ := htemp s.re
    obtain ⟨C, hC⟩ := hdec k
    refine Integrable.mono' (hk.const_mul C) (haesm s) ?_
    filter_upwards [ae_restrict_mem hD] with a ha
    rw [hnorm s a]
    calc ‖h a‖ * ideleNorm F a ^ s.re
        ≤ (C * min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k) * ideleNorm F a ^ s.re :=
          mul_le_mul_of_nonneg_right (hC a ha) (Real.rpow_nonneg (hN0 a).le _)
      _ = C * (min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k * ideleNorm F a ^ s.re) := by ring
  refine ⟨hint, ?_⟩

  have hfun : (fun s : ℂ => ∫ a in D, h a * ((ideleNorm F a : ℝ) : ℂ) ^ s ∂ν)
      = fun s : ℂ => ∫ a, h a * Complex.exp (s * (Real.log (ideleNorm F a) : ℝ)) ∂(ν.restrict D) := by
    funext s
    simp_rw [hcpow]
  rw [hfun]
  refine Ws1.K1.differentiable_integral_mul_exp ?_ ?_ ?_
  · intro s
    simp_rw [← hcpow]
    exact haesm s
  · intro s
    have h1 : AEStronglyMeasurable (fun a => h a * ((Real.log (ideleNorm F a) : ℝ) : ℂ)) (ν.restrict D) :=
      hh.mul (Complex.continuous_ofReal.comp hLc).aestronglyMeasurable
    have h2 : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ =>
        Complex.exp (s * (Real.log (ideleNorm F a) : ℝ)) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hLc))
    exact h1.mul h2.aestronglyMeasurable
  · intro s₀

    obtain ⟨k₁, hk₁⟩ := htemp (s₀.re + 1)
    obtain ⟨k₂, hk₂⟩ := htemp (s₀.re - 1)
    obtain ⟨k₃, hk₃⟩ := htemp (s₀.re + 2)
    obtain ⟨k₄, hk₄⟩ := htemp s₀.re
    obtain ⟨k₅, hk₅⟩ := htemp (s₀.re - 2)
    obtain ⟨C, hC⟩ := hdec (k₁ + k₂ + k₃ + k₄ + k₅)
    have I₁ := hmono _ _ (k₁ + k₂ + k₃ + k₄ + k₅) (by omega) hk₁
    have I₂ := hmono _ _ (k₁ + k₂ + k₃ + k₄ + k₅) (by omega) hk₂
    have I₃ := hmono _ _ (k₁ + k₂ + k₃ + k₄ + k₅) (by omega) hk₃
    have I₄ := hmono _ _ (k₁ + k₂ + k₃ + k₄ + k₅) (by omega) hk₄
    have I₅ := hmono _ _ (k₁ + k₂ + k₃ + k₄ + k₅) (by omega) hk₅
    refine ⟨fun a => C * (min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ (k₁ + k₂ + k₃ + k₄ + k₅) *
        ((1 + ideleNorm F a + (ideleNorm F a)⁻¹) *
          (ideleNorm F a ^ (s₀.re + 1) + ideleNorm F a ^ (s₀.re - 1)))), ?_, ?_⟩
    ·
      have hsum := ((((I₁.add I₂).add I₃).add I₄).add I₄).add I₅
      refine (hsum.const_mul C).congr (Filter.Eventually.of_forall fun a => ?_)
      simp only [Pi.add_apply]
      rw [Ws1.K1.expand_six (hN0 a)]
      ring
    · filter_upwards [ae_restrict_mem hD] with a ha s hs
      have hs' : |s.re - s₀.re| < 1 := by
        have hd : dist s s₀ < 1 := Metric.mem_ball.mp hs
        rw [← Complex.sub_re]
        exact lt_of_le_of_lt (Complex.abs_re_le_norm _) (by rwa [Complex.dist_eq] at hd)
      rw [hexp_re]
      have hA := Ws1.K1.rpow_le_rpow_add_one_add_rpow_sub_one (σ := s.re) (hN0 a) hs'
      have hB := Ws1.K1.one_add_abs_log_le (hN0 a)
      have hpos₁ : 0 ≤ 1 + |Real.log (ideleNorm F a)| := by positivity
      have hpos₂ : 0 ≤ ideleNorm F a ^ (s₀.re + 1) + ideleNorm F a ^ (s₀.re - 1) := by
        have := Real.rpow_nonneg (hN0 a).le (s₀.re + 1)
        have := Real.rpow_nonneg (hN0 a).le (s₀.re - 1)
        linarith
      calc (1 + |Real.log (ideleNorm F a)|) * (‖h a‖ * ideleNorm F a ^ s.re)
          = ‖h a‖ * ((1 + |Real.log (ideleNorm F a)|) * ideleNorm F a ^ s.re) := by ring
        _ ≤ (C * min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ (k₁ + k₂ + k₃ + k₄ + k₅)) *
              ((1 + ideleNorm F a + (ideleNorm F a)⁻¹) *
                (ideleNorm F a ^ (s₀.re + 1) + ideleNorm F a ^ (s₀.re - 1))) := by
            refine mul_le_mul (hC a ha) ?_ (mul_nonneg hpos₁ (Real.rpow_nonneg (hN0 a).le _))
              (le_trans (norm_nonneg _) (hC a ha))
            exact mul_le_mul hB hA (Real.rpow_nonneg (hN0 a).le _)
              (add_nonneg (add_nonneg zero_le_one (hN0 a).le) (inv_pos.mpr (hN0 a)).le)
        _ = _ := by ring

end S_NumberField_TateGlobal_integrableOn_and_differentiable_setIntegral_mul_ideleNorm_cpow_of_norm_le_min_pow
end P2MW
export P2MW.S_NumberField_TateGlobal_integrableOn_and_differentiable_setIntegral_mul_ideleNorm_cpow_of_norm_le_min_pow (solution)
