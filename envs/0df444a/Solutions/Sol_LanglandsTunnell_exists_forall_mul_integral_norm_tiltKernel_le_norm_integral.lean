-- Prove2me | solution 1 for LanglandsTunnell.exists_forall_mul_integral_norm_tiltKernel_le_norm_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/923dc1a3-2236-57bf-aa68-28fd115f30e8

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Theorems.Thm_LanglandsTunnell_exists_logBox_mul_setIntegral_le_setIntegral_tiltKernel
import Theorems.Thm_LanglandsTunnell_exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_forall_mul_integral_norm_tiltKernel_le_norm_integral

set_option autoImplicit false

open MeasureTheory Set

open Filter Topology

namespace K8ML

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma re_mul_le_norm (u z : ℂ) (hu : ‖u‖ = 1) : (u * z).re ≤ ‖z‖ := by
  calc (u * z).re ≤ ‖u * z‖ := Complex.re_le_norm _
    _ = ‖z‖ := by rw [norm_mul, hu, one_mul]

theorem norm_integral_ge_of_phase_coherent
    (F : X → ℂ) (hF : Integrable F μ) (S : Set X) (hS : MeasurableSet S)
    (u : ℂ) (hu : ‖u‖ = 1) (c η : ℝ) (hc : 0 ≤ c)
    (hcoh : ∀ x ∈ S, c * ‖F x‖ ≤ (u * F x).re)
    (htail : ∫ x in Sᶜ, ‖F x‖ ∂μ ≤ η * ∫ x, ‖F x‖ ∂μ) :
    (c * (1 - η) - η) * ∫ x, ‖F x‖ ∂μ ≤ ‖∫ x, F x ∂μ‖ := by
  have hFn : Integrable (fun x => ‖F x‖) μ := hF.norm
  have huF : Integrable (fun x => u * F x) μ := hF.const_mul u
  have h1 : (u * ∫ x, F x ∂μ).re ≤ ‖∫ x, F x ∂μ‖ := re_mul_le_norm u _ hu
  have h2 : (u * ∫ x, F x ∂μ).re = ∫ x, (u * F x).re ∂μ := by
    rw [← integral_const_mul]
    simpa only [RCLike.re_to_complex] using (integral_re huF).symm
  have hsplit : ∫ x, (u * F x).re ∂μ = (∫ x in S, (u * F x).re ∂μ) + ∫ x in Sᶜ, (u * F x).re ∂μ :=
    (integral_add_compl hS huF.re).symm
  have hsplitN : ∫ x, ‖F x‖ ∂μ = (∫ x in S, ‖F x‖ ∂μ) + ∫ x in Sᶜ, ‖F x‖ ∂μ :=
    (integral_add_compl hS hFn).symm
  have hSge : c * ∫ x in S, ‖F x‖ ∂μ ≤ ∫ x in S, (u * F x).re ∂μ := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hFn.const_mul c).integrableOn huF.re.integrableOn hS (fun x hx => hcoh x hx)
  have hScge : -(∫ x in Sᶜ, ‖F x‖ ∂μ) ≤ ∫ x in Sᶜ, (u * F x).re ∂μ := by
    rw [← integral_neg]
    refine setIntegral_mono_on hFn.neg.integrableOn huF.re.integrableOn hS.compl (fun x _ => ?_)
    have h := Complex.abs_re_le_norm (u * F x)
    rw [norm_mul, hu, one_mul] at h
    have := (abs_le.mp h).1
    linarith
  have htot : 0 ≤ ∫ x, ‖F x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have htailnn : 0 ≤ ∫ x in Sᶜ, ‖F x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have hSn : ∫ x in S, ‖F x‖ ∂μ = (∫ x, ‖F x‖ ∂μ) - ∫ x in Sᶜ, ‖F x‖ ∂μ := by linarith

  have key : c * ((∫ x, ‖F x‖ ∂μ) - ∫ x in Sᶜ, ‖F x‖ ∂μ) - (∫ x in Sᶜ, ‖F x‖ ∂μ) ≤ ‖∫ x, F x ∂μ‖ := by
    rw [← hSn]; linarith
  have hct : c * (∫ x in Sᶜ, ‖F x‖ ∂μ) ≤ c * (η * ∫ x, ‖F x‖ ∂μ) := mul_le_mul_of_nonneg_left htail hc
  nlinarith [key, hct, htail]

end K8ML

namespace FbCoh

theorem exp_neg_pi_div_sq_le (n : ℕ) (w : ℝ) (hw : 0 < w) :
    Real.exp (-(Real.pi * (w ^ 2)⁻¹)) ≤ ((n.factorial : ℝ) / Real.pi ^ n) * w ^ (2 * n) := by
  set x : ℝ := Real.pi * (w ^ 2)⁻¹ with hx
  have hxpos : 0 < x := by positivity
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h := Real.pow_div_factorial_le_exp x hxpos.le n

  have h1 : Real.exp (-x) ≤ (n.factorial : ℝ) / x ^ n := by
    rw [Real.exp_neg, le_div_iff₀ (pow_pos hxpos n)]
    rw [div_le_iff₀ hfac] at h
    calc (Real.exp x)⁻¹ * x ^ n ≤ (Real.exp x)⁻¹ * (Real.exp x * n.factorial) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = n.factorial := by field_simp
  refine h1.trans (le_of_eq ?_)
  simp only [hx]
  rw [mul_pow, inv_pow, ← pow_mul]
  field_simp

theorem integrableOn_rpow_mul_exp_kernel (a : ℝ) (ha : a ≠ 0) (r : ℝ) :
    IntegrableOn (fun w : ℝ => w ^ r * Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))) (Ioi 0) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (-r / 2)
  obtain ⟨N, hN⟩ := exists_nat_ge r
  set Cn : ℝ := (n.factorial : ℝ) / Real.pi ^ n with hCn
  have hCn0 : 0 ≤ Cn := by positivity
  have hb : 0 < Real.pi * a ^ 2 := by positivity
  have hmaj : IntegrableOn (fun w : ℝ => (Cn + w ^ (N : ℝ)) * Real.exp (-(Real.pi * a ^ 2) * w ^ 2)) (Ioi 0) := by
    have h1 : IntegrableOn (fun w : ℝ => w ^ (N : ℝ) * Real.exp (-(Real.pi * a ^ 2) * w ^ 2)) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_sq hb (by have : (0:ℝ) ≤ N := N.cast_nonneg; linarith)
    have h0 : IntegrableOn (fun w : ℝ => Real.exp (-(Real.pi * a ^ 2) * w ^ 2)) (Ioi 0) :=
      (integrable_exp_neg_mul_sq hb).integrableOn
    have h2 := (h0.const_mul Cn).add h1
    exact h2.congr (Eventually.of_forall (fun w => by simp only [Pi.add_apply]; ring))
  refine Integrable.mono' hmaj ?_ ?_
  · refine ((ContinuousOn.mul (fun w hw => ?_) ?_)).aestronglyMeasurable measurableSet_Ioi
    · exact (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hw))).continuousWithinAt
    · refine (Real.continuous_exp.comp_continuousOn ?_)
      refine ContinuousOn.neg (ContinuousOn.mul continuousOn_const (ContinuousOn.add ?_ ?_))
      · exact ContinuousOn.inv₀ (continuousOn_pow 2) (fun w hw => (pow_pos (mem_Ioi.mp hw) 2).ne')
      · exact (continuousOn_const.mul (continuousOn_pow 2))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun w (hw : 0 < w) => ?_))
    rw [Real.norm_of_nonneg (by positivity)]
    have hsplit : Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))
        = Real.exp (-(Real.pi * (w ^ 2)⁻¹)) * Real.exp (-(Real.pi * a ^ 2) * w ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    have hwN : 0 ≤ w ^ (N : ℝ) := by positivity
    by_cases hw1 : w ≤ 1
    · have hexp := exp_neg_pi_div_sq_le n w hw
      have hpow : w ^ r * w ^ (2 * n) ≤ 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hw]
        refine Real.rpow_le_one hw.le hw1 ?_
        push_cast
        linarith
      calc w ^ r * Real.exp (-(Real.pi * (w ^ 2)⁻¹)) ≤ w ^ r * (Cn * w ^ (2 * n)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = Cn * (w ^ r * w ^ (2 * n)) := by ring
        _ ≤ Cn * 1 := mul_le_mul_of_nonneg_left hpow hCn0
        _ ≤ Cn + w ^ (N : ℝ) := by linarith
    · push_neg at hw1
      have h1 : Real.exp (-(Real.pi * (w ^ 2)⁻¹)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 ≤ Real.pi * (w ^ 2)⁻¹ := by positivity
        linarith)
      have h2 : w ^ r ≤ w ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le hw1.le hN
      calc w ^ r * Real.exp (-(Real.pi * (w ^ 2)⁻¹)) ≤ w ^ (N : ℝ) * 1 :=
            mul_le_mul h2 h1 (Real.exp_nonneg _) (by positivity)
        _ ≤ Cn + w ^ (N : ℝ) := by linarith

end FbCoh

open FbCoh in
set_option maxHeartbeats 4000000 in
theorem solution
    (a : ℝ) (ha : a ≠ 0) (A B : ℂ) (τ : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ y →
      (1 - ε) * ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
          ‖((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-((y : ℂ) + (τ : ℂ) * Complex.I)) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)‖
        ≤ ‖∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
          ((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-((y : ℂ) + (τ : ℂ) * Complex.I)) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)‖ := by

  set η : ℝ := min ε 1 / 3 with hη
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη1 : η ≤ 1 / 3 := by rw [hη]; have := min_le_right ε 1; linarith
  have hηε : η ≤ ε / 3 := by rw [hη]; have := min_le_left ε 1; linarith
  set α : ℝ := A.re with hα
  set β : ℝ := B.re with hβ
  set L : ℝ := (abs A.im) + (abs B.im) with hL
  have hL0 : 0 ≤ L := by positivity
  set δ : ℝ := η / (2 * (L + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hLδ : L * δ ≤ η / 2 := by
    rw [hδ]; rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]; nlinarith

  obtain ⟨R₁, hR₁⟩ := LanglandsTunnell.exists_logBox_mul_setIntegral_le_setIntegral_tiltKernel a ha α β η δ hη0 hδ0

  set y₀ : ℝ := |β| / 2 + 1 / 2 with hy₀
  set R₂ : ℝ := (2 * |τ| * Real.exp (4 * δ) / η) ^ 2 + 1 with hR₂
  refine ⟨max (max R₁ y₀) R₂, fun y hy => ?_⟩
  have hy1 : R₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy0 : y₀ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy2 : R₂ ≤ y := le_trans (le_max_right _ _) hy
  have hy₀pos : 0 < y₀ := by positivity
  have hypos : 0 < y := by linarith
  have hR₂1 : (1:ℝ) ≤ R₂ := by rw [hR₂]; nlinarith [sq_nonneg (2 * |τ| * Real.exp (4 * δ) / η)]
  have hy1' : 1 ≤ y := by linarith
  obtain ⟨ℓw, ℓr, hgrow, hbox⟩ := hR₁ y hy1

  set S : ℂ := (y : ℂ) + (τ : ℂ) * Complex.I with hS
  have hSre : S.re = y := by simp [hS]
  have hSim : S.im = τ := by simp [hS]
  set G : ℝ → ℝ → ℂ := fun w r => ((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-S) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B *
      (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ) with hG
  set T : ℝ → ℝ → ℝ := fun w r => (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ α * r ^ β *
      Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) with hT
  have hnormG : ∀ w r : ℝ, 0 < w → 0 < r → ‖G w r‖ = T w r := by
    intro w r hw hr
    have hv : 0 < 1 + ((w * r) ^ 2)⁻¹ := by positivity
    simp only [hG, hT]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_cpow_eq_rpow_re_of_pos hw,
      Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
      Complex.neg_re, hSre]
  have hTnn : ∀ w r : ℝ, 0 < w → 0 < r → 0 ≤ T w r := fun w r hw hr => by rw [← hnormG w r hw hr]; exact norm_nonneg _

  set μp : Measure ℝ := volume.restrict (Ioi (0:ℝ)) with hμp
  set μ2 : Measure (ℝ × ℝ) := μp.prod μp with hμ2
  set F : ℝ × ℝ → ℂ := fun p => G p.1 p.2 with hF

  have hcpx : ∀ z : ℂ, Measurable fun x : ℝ => ((x : ℝ) : ℂ) ^ z := fun z => (Complex.measurable_ofReal).pow_const z
  have hFm : Measurable F := by
    simp only [hF, hG]
    have m1 : Measurable fun p : ℝ × ℝ => p.1 := measurable_fst
    have m2 : Measurable fun p : ℝ × ℝ => p.2 := measurable_snd
    have mv : Measurable fun p : ℝ × ℝ => (1 : ℝ) + ((p.1 * p.2) ^ 2)⁻¹ := (((m1.mul m2).pow_const 2).inv).const_add 1
    have mt : Measurable fun p : ℝ × ℝ => (((1 + ((p.1 * p.2) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-S) :=
      (Complex.measurable_ofReal.comp mv).pow_const _
    have me : Measurable fun p : ℝ × ℝ => ((Real.exp (-(Real.pi * (p.2 ^ 2 + (p.1 ^ 2)⁻¹ + a ^ 2 * p.1 ^ 2))) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        ((((m2.pow_const 2).add (m1.pow_const 2).inv).add ((m1.pow_const 2).const_mul _)).const_mul _).neg)
    exact ((mt.mul ((hcpx A).comp m1)).mul ((hcpx B).comp m2)).mul me

  have hβ' : -1 < β + 2 * y₀ := by rw [hy₀]; have := neg_abs_le β; linarith
  have hInt : Integrable F μ2 := by
    have hw_int := integrableOn_rpow_mul_exp_kernel a ha (α + 2 * y₀)
    have hr_int : IntegrableOn (fun r : ℝ => r ^ (β + 2 * y₀) * Real.exp (-Real.pi * r ^ 2)) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos hβ'
    have hmaj : Integrable (fun p : ℝ × ℝ => (p.1 ^ (α + 2 * y₀) * Real.exp (-(Real.pi * ((p.1 ^ 2)⁻¹ + a ^ 2 * p.1 ^ 2)))) *
        (p.2 ^ (β + 2 * y₀) * Real.exp (-Real.pi * p.2 ^ 2))) μ2 := hw_int.mul_prod hr_int
    refine Integrable.mono' hmaj hFm.aestronglyMeasurable ?_
    have hae : ∀ᵐ p ∂μ2, p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := by
      rw [hμ2, hμp, Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    refine hae.mono (fun p hp => ?_)
    obtain ⟨hw, hr⟩ := hp
    have hw0 : 0 < p.1 := hw
    have hr0 : 0 < p.2 := hr
    show ‖G p.1 p.2‖ ≤ _
    rw [hnormG p.1 p.2 hw0 hr0]
    simp only [hT]

    set u : ℝ := (p.1 * p.2) ^ 2 with hu
    have hu0 : 0 < u := by positivity
    have htilt : (1 + u⁻¹) ^ (-y) ≤ u ^ y₀ := by
      have h1 : (1 + u⁻¹) ^ (-y) ≤ (1 + u⁻¹) ^ (-y₀) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · have : 0 ≤ u⁻¹ := by positivity
          linarith
        · linarith
      have h2 : (1 + u⁻¹) ^ (-y₀) ≤ u ^ y₀ := by
        rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
        apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        rw [inv_le_comm₀ (by positivity) hu0]
        have : u⁻¹ ≤ 1 + u⁻¹ := by linarith
        exact this
      exact h1.trans h2
    have hupow : u ^ y₀ = p.1 ^ (2 * y₀) * p.2 ^ (2 * y₀) := by
      rw [hu, mul_pow, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul hw0.le, ← Real.rpow_mul hr0.le]; norm_num
    have hE2 : Real.exp (-(Real.pi * (p.2 ^ 2 + (p.1 ^ 2)⁻¹ + a ^ 2 * p.1 ^ 2)))
        = Real.exp (-(Real.pi * ((p.1 ^ 2)⁻¹ + a ^ 2 * p.1 ^ 2))) * Real.exp (-Real.pi * p.2 ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hE2]
    have hrest : 0 ≤ p.1 ^ α * p.2 ^ β * (Real.exp (-(Real.pi * ((p.1 ^ 2)⁻¹ + a ^ 2 * p.1 ^ 2))) * Real.exp (-Real.pi * p.2 ^ 2)) := by
      positivity
    calc (1 + ((p.1 * p.2) ^ 2)⁻¹) ^ (-y) * p.1 ^ α * p.2 ^ β *
          (Real.exp (-(Real.pi * ((p.1 ^ 2)⁻¹ + a ^ 2 * p.1 ^ 2))) * Real.exp (-Real.pi * p.2 ^ 2))
        = (1 + u⁻¹) ^ (-y) * (p.1 ^ α * p.2 ^ β * (Real.exp (-(Real.pi * ((p.1 ^ 2)⁻¹ + a ^ 2 * p.1 ^ 2))) * Real.exp (-Real.pi * p.2 ^ 2))) := by
          rw [hu]; ring
      _ ≤ u ^ y₀ * (p.1 ^ α * p.2 ^ β * (Real.exp (-(Real.pi * ((p.1 ^ 2)⁻¹ + a ^ 2 * p.1 ^ 2))) * Real.exp (-Real.pi * p.2 ^ 2))) :=
          mul_le_mul_of_nonneg_right htilt hrest
      _ = (p.1 ^ (α + 2 * y₀) * Real.exp (-(Real.pi * ((p.1 ^ 2)⁻¹ + a ^ 2 * p.1 ^ 2)))) *
          (p.2 ^ (β + 2 * y₀) * Real.exp (-Real.pi * p.2 ^ 2)) := by
          rw [hupow, Real.rpow_add hw0, Real.rpow_add hr0]; ring

  have hIter : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), G w r) = ∫ p, F p ∂μ2 := by
    rw [hμ2, integral_prod _ hInt]
  have hIterN : (∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), ‖G w r‖) = ∫ p, ‖F p‖ ∂μ2 := by
    rw [hμ2, integral_prod _ hInt.norm]

  set Bw : Set ℝ := Icc (Real.exp (ℓw - δ)) (Real.exp (ℓw + δ)) with hBw
  set Br : Set ℝ := Icc (Real.exp (ℓr - δ)) (Real.exp (ℓr + δ)) with hBr
  have hBw_sub : Bw ⊆ Ioi 0 := fun w hw => (Real.exp_pos _).trans_le hw.1
  have hBr_sub : Br ⊆ Ioi 0 := fun r hr => (Real.exp_pos _).trans_le hr.1
  set Sbox : Set (ℝ × ℝ) := Bw ×ˢ Br with hSbox
  have hSm : MeasurableSet Sbox := measurableSet_Icc.prod measurableSet_Icc
  have hrestr : μ2.restrict Sbox = (volume.restrict Bw).prod (volume.restrict Br) := by
    rw [hμ2, hμp, hSbox, ← Measure.prod_restrict, Measure.restrict_restrict measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hBw_sub, inter_eq_left.mpr hBr_sub]
  have hboxInt : (∫ p in Sbox, ‖F p‖ ∂μ2) = ∫ w in Bw, ∫ r in Br, T w r := by
    rw [hrestr, integral_prod _ ((hInt.norm.mono_measure (by rw [← hrestr]; exact Measure.restrict_le_self)))]
    refine setIntegral_congr_fun measurableSet_Icc (fun w hw => ?_)
    refine setIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
    exact hnormG w r (hBw_sub hw) (hBr_sub hr)
  have hallT : (∫ p, ‖F p‖ ∂μ2) = ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ), T w r := by
    rw [← hIterN]
    refine setIntegral_congr_fun measurableSet_Ioi (fun w hw => ?_)
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    exact hnormG w r hw hr

  have htot0 : 0 ≤ ∫ p, ‖F p‖ ∂μ2 := integral_nonneg (fun _ => norm_nonneg _)
  have htail : ∫ p in Sboxᶜ, ‖F p‖ ∂μ2 ≤ η * ∫ p, ‖F p‖ ∂μ2 := by
    have hsplit := integral_add_compl hSm hInt.norm
    have hb : (1 - η) * ∫ p, ‖F p‖ ∂μ2 ≤ ∫ p in Sbox, ‖F p‖ ∂μ2 := by
      rw [hallT, hboxInt]; exact hbox
    linarith

  have hΔ_le : L * δ + (abs S.im) * Real.exp (4 * δ) * Real.exp (-(2 * (ℓw + ℓr))) ≤ η := by
    rw [hSim]
    have h1 : Real.exp (-(2 * (ℓw + ℓr))) ≤ y ^ (-(1/2:ℝ)) := by
      have : Real.exp (-(2 * (ℓw + ℓr))) = (Real.exp (ℓw + ℓr)) ^ (-(2:ℝ)) := by
        rw [← Real.exp_mul]; congr 1; ring
      rw [this]
      calc (Real.exp (ℓw + ℓr)) ^ (-(2:ℝ)) ≤ (y ^ ((1:ℝ)/4)) ^ (-(2:ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hgrow (by norm_num)
        _ = y ^ (-(1/2:ℝ)) := by rw [← Real.rpow_mul hypos.le]; norm_num
    have h2 : |τ| * Real.exp (4 * δ) * y ^ (-(1/2:ℝ)) ≤ η / 2 := by
      have hysqrt : (2 * |τ| * Real.exp (4 * δ) / η) ≤ y ^ ((1:ℝ)/2) := by
        have : (2 * |τ| * Real.exp (4 * δ) / η) ^ 2 ≤ y := by rw [hR₂] at hy2; linarith
        calc 2 * |τ| * Real.exp (4 * δ) / η = ((2 * |τ| * Real.exp (4 * δ) / η) ^ 2) ^ ((1:ℝ)/2) := by
              rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
          _ ≤ y ^ ((1:ℝ)/2) := Real.rpow_le_rpow (by positivity) this (by norm_num)
      have hyhalf : 0 < y ^ ((1:ℝ)/2) := by positivity
      rw [Real.rpow_neg hypos.le]
      rw [div_le_iff₀ hη0] at hysqrt
      rw [show |τ| * Real.exp (4 * δ) * (y ^ ((1:ℝ)/2))⁻¹ = (|τ| * Real.exp (4 * δ)) / y ^ ((1:ℝ)/2) by ring,
        div_le_iff₀ hyhalf]
      nlinarith
    calc L * δ + |τ| * Real.exp (4 * δ) * Real.exp (-(2 * (ℓw + ℓr)))
        ≤ η / 2 + |τ| * Real.exp (4 * δ) * y ^ (-(1/2:ℝ)) := by gcongr
      _ ≤ η / 2 + η / 2 := by linarith
      _ = η := by ring
  have hΔπ : L * δ + (abs S.im) * Real.exp (4 * δ) * Real.exp (-(2 * (ℓw + ℓr))) ≤ Real.pi := by
    have := Real.two_le_pi; linarith
  obtain ⟨u, hu, hcohpt⟩ :=
    LanglandsTunnell.exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re S A B δ ℓw ℓr hδ0.le hΔπ
  set cΔ : ℝ := Real.cos (L * δ + (abs S.im) * Real.exp (4 * δ) * Real.exp (-(2 * (ℓw + ℓr)))) with hcΔ
  have hcΔ_ge : 1 - η ≤ cΔ := by
    have hD0 : 0 ≤ L * δ + (abs S.im) * Real.exp (4 * δ) * Real.exp (-(2 * (ℓw + ℓr))) := by positivity
    have h := Real.one_sub_sq_div_two_le_cos (x := L * δ + (abs S.im) * Real.exp (4 * δ) * Real.exp (-(2 * (ℓw + ℓr))))
    rw [hcΔ]
    nlinarith [hΔ_le, hD0, hη1]
  have hcΔ0 : 0 ≤ cΔ := by linarith
  have hcoh : ∀ p ∈ Sbox, cΔ * ‖F p‖ ≤ (u * F p).re := by
    rintro ⟨w, r⟩ ⟨hw, hr⟩
    simp only [hF, hG]
    have := hcohpt w r (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))) (Real.exp_nonneg _) hw hr
    simpa only [hL] using this

  have key := K8ML.norm_integral_ge_of_phase_coherent F hInt Sbox hSm u hu cΔ η hcΔ0 hcoh htail

  rw [hIter, hIterN]
  have hcoef : 1 - ε ≤ cΔ * (1 - η) - η := by nlinarith [hcΔ_ge, hηε, hη0, hε]
  calc (1 - ε) * ∫ p, ‖F p‖ ∂μ2 ≤ (cΔ * (1 - η) - η) * ∫ p, ‖F p‖ ∂μ2 := mul_le_mul_of_nonneg_right hcoef htot0
    _ ≤ ‖∫ p, F p ∂μ2‖ := key

end S_LanglandsTunnell_exists_forall_mul_integral_norm_tiltKernel_le_norm_integral
end P2MW
export P2MW.S_LanglandsTunnell_exists_forall_mul_integral_norm_tiltKernel_le_norm_integral (solution)
