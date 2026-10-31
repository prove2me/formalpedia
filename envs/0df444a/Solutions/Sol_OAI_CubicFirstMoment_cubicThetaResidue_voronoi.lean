-- Prove2me | solution 1 for OAI.CubicFirstMoment.cubicThetaResidue_voronoi
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:18:02.372587+00:00
-- url     : https://prove2.me/submissions/21de77d1-ea2f-4209-8079-838a43a83fd0

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A026
import Theorems.Thm_OAI_CubicFirstMoment_cubicThetaProjectedCusp_identity

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed order-one-third Bessel kernel in the cubic theta expansion.
The Schläfli heat integral is used as the definition; its Mellin mass is
proved by absolute Fubini and the two ordinary Gamma integrals.
Normalization: NIST DLMF 10.32.10, specialized to nu=1/3 and positive
argument; the cubic theta expansion is DR v3 section 5.1, Eq.(5.6). -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicBesselHeat_inner_integral {σ t : ℝ} (hσ : 1/6 < σ) (ht : 0 < t) :
    (∫ x in Ioi (0:ℝ), x^(σ+1/6-1)*cubicBesselHeat x t) =
      Real.Gamma (σ+1/6)*t^(σ-1/6-1)*Real.exp (-t) := by
  have ha : 0 < σ+1/6 := by linarith
  calc
    _ = (t^(-4/3:ℝ)*Real.exp (-t))*
        (∫ x in Ioi (0:ℝ), x^(σ+1/6-1)*Real.exp (-(1/t)*x)) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only
      unfold cubicBesselHeat
      rw [show -(1/t)*x = -x/t by ring]
      ring
    _ = (t^(-4/3:ℝ)*Real.exp (-t))*(Real.Gamma (σ+1/6)*(1/t)^(-(σ+1/6))) := by
      rw [laplace_rpow ha (one_div_pos.mpr ht)]
    _ = _ := by
      have he : (1/t)^(-(σ+1/6)) = t^(σ+1/6) := by
        rw [one_div,←Real.rpow_neg_eq_inv_rpow,neg_neg]
      rw [he]
      calc
        _ = Real.Gamma (σ+1/6)*(t^(-4/3:ℝ)*t^(σ+1/6))*Real.exp (-t) := by ring
        _ = _ := by rw [←Real.rpow_add ht]; congr 2; ring_nf

lemma cubicBesselHeat_mellin_integrable {σ : ℝ} (hσ : 1/6 < σ) :
    Integrable (fun p : ℝ × ℝ => p.2^(σ+1/6-1)*cubicBesselHeat p.2 p.1)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => p.2^(σ+1/6-1)*cubicBesselHeat p.2 p.1)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicBesselHeat
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hi := (integrable_laplace_rpow (by linarith : 0 < σ+1/6)
      (one_div_pos.mpr ht)).const_mul (t^(-4/3:ℝ)*Real.exp (-t))
    apply hi.congr
    filter_upwards with x
    unfold cubicBesselHeat
    rw [show -(1/t)*x = -x/t by ring]
    ring
  · have hi := (integrable_laplace_rpow (by linarith : 0 < σ-1/6)
      (by norm_num : (0:ℝ) < 1)).const_mul (Real.Gamma (σ+1/6))
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [show (∫ x in Ioi (0:ℝ), ‖x^(σ+1/6-1)*cubicBesselHeat x t‖) =
        ∫ x in Ioi (0:ℝ), x^(σ+1/6-1)*cubicBesselHeat x t from ?_,
      cubicBesselHeat_inner_integral hσ ht]
    · simp only [neg_mul,one_mul,mul_assoc]
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _)
        (cubicBesselHeat_nonneg ht))]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact complex Mellin transform of the fixed cubic theta kernel.
Only the order one third needed in the Voronoi construction is used. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicBesselHeat_complex_inner {s : ℂ} (hs : 1/6 < s.re)
    {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(s+1/6-1)*(cubicBesselHeat x t:ℂ)) =
      Complex.Gamma (s+1/6)*(Real.exp (-t):ℂ)*(t:ℂ)^(s-1/6-1) := by
  have ha : 0 < (s+1/6).re := by norm_num; linarith
  calc
    _ = ((t^(-4/3:ℝ)*Real.exp (-t):ℝ):ℂ)*
        (∫ x in Ioi (0:ℝ), (x:ℂ)^(s+1/6-1)*Complex.exp (-(((1/t:ℝ):ℂ)*(x:ℂ)))) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      simp only [cubicBesselHeat,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,
        Complex.ofReal_div,Complex.ofReal_one]
      rw [show -(x:ℂ)/(t:ℂ) = -(1/(t:ℂ)*(x:ℂ)) by ring]
      ring
    _ = ((t^(-4/3:ℝ)*Real.exp (-t):ℝ):ℂ)*
        (((1/(1/t:ℝ):ℝ):ℂ)^(s+1/6)*Complex.Gamma (s+1/6)) := by
      rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi ha (one_div_pos.mpr ht)]
      simp only [Complex.ofReal_div,Complex.ofReal_one]
    _ = _ := by
      simp only [one_div_one_div,Complex.ofReal_mul]
      rw [Complex.ofReal_cpow ht.le]
      calc
        _ = Complex.Gamma (s+1/6)*(Real.exp (-t):ℂ)*
            ((t:ℂ)^((-4/3:ℝ):ℂ)*(t:ℂ)^(s+1/6)) := by ring
        _ = _ := by
          rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
          congr 1
          push_cast
          ring_nf

lemma cubicBesselHeat_complex_integrable {s : ℂ} (hs : 1/6 < s.re) :
    Integrable (fun p : ℝ × ℝ => (p.2:ℂ)^(s+1/6-1)*(cubicBesselHeat p.2 p.1:ℂ))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hi := cubicBesselHeat_mellin_integrable hs
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (p.2:ℂ)^(s+1/6-1)*(cubicBesselHeat p.2 p.1:ℂ))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicBesselHeat
    fun_prop
  apply hi.mono' hm
  have ha : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))),
      p.1 ∈ Ioi 0 ∧ p.2 ∈ Ioi 0 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact ⟨ht,hx⟩
  filter_upwards [ha] with p hp
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp.2,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (cubicBesselHeat_nonneg hp.1)]
  simp only [Complex.sub_re,Complex.add_re,Complex.one_re]
  norm_num

/-- The Gamma product is proved for the literal heat kernel, with its
absolute convergence supplied by the preceding positive-integral estimate. -/
theorem cubicBesselKernel_mellin {s : ℂ} (hs : 1/6 < s.re) :
    mellin (fun x => (cubicBesselKernel x:ℂ)) s =
      Complex.Gamma (s+1/6)*Complex.Gamma (s-1/6) := by
  have hi := cubicBesselHeat_complex_integrable hs
  have hm : 0 < (s-1/6).re := by
    norm_num
    exact hs
  calc
    _ = ∫ x in Ioi (0:ℝ), ∫ t in Ioi (0:ℝ),
        (x:ℂ)^(s+1/6-1)*(cubicBesselHeat x t:ℂ) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [smul_eq_mul,cubicBesselKernel,Complex.ofReal_mul]
      rw [Complex.ofReal_cpow hx.le,←mul_assoc,
        ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)),
        show s-1+(1/6:ℝ)=s+1/6-1 by push_cast; ring,
        integral_const_mul,←integral_complex_ofReal]
    _ = ∫ t in Ioi (0:ℝ), ∫ x in Ioi (0:ℝ),
        (x:ℂ)^(s+1/6-1)*(cubicBesselHeat x t:ℂ) := (integral_integral_swap hi).symm
    _ = ∫ t in Ioi (0:ℝ),
        Complex.Gamma (s+1/6)*(Real.exp (-t):ℂ)*(t:ℂ)^(s-1/6-1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact cubicBesselHeat_complex_inner hs ht
    _ = Complex.Gamma (s+1/6)*(∫ t in Ioi (0:ℝ),
        (Real.exp (-t):ℂ)*(t:ℂ)^((s-1/6)-1)) := by
      rw [←integral_const_mul]
      congr 1
      funext t
      ring
    _ = _ := by rw [Complex.Gamma_eq_integral hm]; rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact archimedean factor of the cubic theta Fourier expansion,
using the fixed Schläfli kernel and the normalization `4*pi*v`. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaWhittaker_mellin {s : ℂ} (hs : 1/6 < s.re) :
    mellin cubicThetaWhittaker (2*s-1) =
      (1/4:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2*s)*
        Complex.Gamma (s+1/6)*Complex.Gamma (s-1/6) := by
  let f : ℝ → ℂ := fun x => (cubicBesselKernel x:ℂ)
  let c : ℝ := (2*Real.pi)^2
  have hc : 0 < c := by dsimp [c]; positivity
  have hform : cubicThetaWhittaker = fun v : ℝ =>
      (1/2:ℂ) • ((v:ℂ)^((1:ℝ):ℂ) • (fun x => f (c*x)) (v^(2:ℝ))) := by
    funext v
    simp only [cubicThetaWhittaker,Complex.ofReal_one,Complex.cpow_one,
      Real.rpow_two,f,c,smul_eq_mul]
    rw [show (2*Real.pi*v)^2 = (2*Real.pi)^2*v^2 by ring]
    ring
  rw [hform,mellin_const_smul,mellin_cpow_smul]
  simp only [smul_eq_mul]
  rw [show (2*s-1)+(1:ℝ)=2*s by push_cast; ring,
    mellin_comp_rpow (fun x => f (c*x)) (2*s) 2]
  norm_num only [Complex.ofReal_ofNat,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  simp only [Complex.real_smul]
  rw [show (2*s)/(2:ℂ)=s by ring,mellin_comp_mul_left f s hc,
    cubicBesselKernel_mellin hs]
  have hpow : (c:ℂ)^(-s) = ((2*Real.pi:ℝ):ℂ)^(-2*s) := by
    have he := Complex.cpow_mul_ofReal_nonneg
      (show (0:ℝ) ≤ 2*Real.pi by positivity) 2 (-s)
    simp only [Real.rpow_two,Complex.ofReal_ofNat] at he
    calc
      _ = ((2*Real.pi:ℝ):ℂ)^((2:ℂ)*(-s)) := he.symm
      _ = _ := by congr 1; ring
  rw [hpow]
  dsimp [f]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerConvergence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Mellin convergence of the fixed cubic Whittaker kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaWhittaker_mellinConvergent {s : ℂ} (hs : 1/6 < s.re) :
    MellinConvergent cubicThetaWhittaker (2*s-1) := by
  have hbase : ((2*Real.pi:ℝ):ℂ)^(-2*s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  have h1 : Complex.Gamma (s+1/6) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using (show 0 < s.re+1/6 by linarith))
  have h2 : Complex.Gamma (s-1/6) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using (show 0 < s.re-1/6 by linarith))
  have hm : mellin cubicThetaWhittaker (2*s-1) ≠ 0 := by
    rw [cubicThetaWhittaker_mellin hs]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hbase) h1) h2
  by_contra h
  exact hm (integral_undef h)

lemma cubicThetaWhittaker_scaled_mellinConvergent {s : ℂ} (hs : 1/6 < s.re)
    {r : ℝ} (hr : 0 < r) (c : ℂ) :
    MellinConvergent (fun v : ℝ => c*cubicThetaWhittaker (r*v)) (2*s-1) := by
  exact ((MellinConvergent.comp_mul_left hr).mpr
    (cubicThetaWhittaker_mellinConvergent hs)).const_smul c

/-- The norm mass changes by the exact Mellin scaling power. -/
lemma cubicWhittaker_norm_mass_scale (σ : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ v in Ioi (0:ℝ), v^(σ-1)*‖cubicThetaWhittaker (r*v)‖) =
      r^(-σ)*(∫ v in Ioi (0:ℝ), v^(σ-1)*‖cubicThetaWhittaker v‖) := by
  have hcancel : r^(1-σ)*r^(σ-1) = 1 := by
    rw [←Real.rpow_add hr]
    simp
  have he : (∫ v in Ioi (0:ℝ), v^(σ-1)*‖cubicThetaWhittaker (r*v)‖) =
      r^(1-σ)*(∫ v in Ioi (0:ℝ), (r*v)^(σ-1)*‖cubicThetaWhittaker (r*v)‖) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [Real.mul_rpow hr.le hv.le]
    simp only [←mul_assoc,hcancel,one_mul]
  rw [he,integral_comp_mul_left_Ioi (fun v : ℝ => v^(σ-1)*‖cubicThetaWhittaker v‖) 0 hr,mul_zero]
  simp only [smul_eq_mul]
  have hp : r^(1-σ)*r⁻¹ = r^(-σ) := by
    rw [←Real.rpow_neg_one,←Real.rpow_add hr]
    congr 1
    ring
  rw [←mul_assoc,hp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour shifting for the Mellin integrals in the smooth Hecke sum.
The horizontal edges are kept explicit until a uniform decay bound is
available; no functional equation or dual-sum estimate is assumed here. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace CubicFirstMoment

lemma mellin_rectangle_identity {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (T : ℝ) :
    (∫ x in a..b, f (x - (T : ℂ) * Complex.I)) -
      (∫ x in a..b, f (x + (T : ℂ) * Complex.I)) +
      Complex.I * (∫ y in -T..T, f (b + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in -T..T, f (a + (y : ℂ) * Complex.I)) = 0 := by
  have hd := hf.mono (show
      (Set.uIcc a b ×ℂ Set.uIcc (-T) T) ⊆ closedVerticalStrip a b from by
    intro z hz
    simpa only [Set.uIcc_of_le hab, Set.mem_preimage, Set.mem_Icc,
      closedVerticalStrip, Set.mem_ofPred_eq] using hz.1)
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) - (T : ℂ) * Complex.I) ((b : ℂ) + (T : ℂ) * Complex.I)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.add_im, mul_zero,
    sub_zero, add_zero, zero_sub, mul_one, zero_add] at h
  simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.add_im, mul_zero, zero_mul,
    sub_zero, add_zero, zero_sub, mul_one, zero_add, Complex.ofReal_neg,
    neg_mul, add_neg_cancel, sub_self, smul_eq_mul, sub_eq_add_neg] using h hd

/-- Vertical Mellin integrals agree after shifting through a holomorphic
strip, once both horizontal edges vanish. -/
theorem mellin_contour_shift {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (ha : Integrable (fun y : ℝ => f (a + (y : ℂ) * Complex.I)))
    (hb : Integrable (fun y : ℝ => f (b + (y : ℂ) * Complex.I)))
    (hTop : Tendsto (fun T : ℝ => ∫ x in a..b, f (x + (T : ℂ) * Complex.I))
      atTop (𝓝 0))
    (hBot : Tendsto (fun T : ℝ => ∫ x in a..b, f (x - (T : ℂ) * Complex.I))
      atTop (𝓝 0)) :
    (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ, f (b + (y : ℂ) * Complex.I) := by
  have hia := intervalIntegral_tendsto_integral ha
    tendsto_neg_atTop_atBot tendsto_id
  have hib := intervalIntegral_tendsto_integral hb
    tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hBot.sub hTop).add (hib.const_mul Complex.I)).sub
    (hia.const_mul Complex.I)
  have hz : (0 : ℂ) + Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) = 0 := by
    have hz' : 0 - 0 + Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) = 0 := by
      apply tendsto_nhds_unique hlim
      apply tendsto_const_nhds.congr'
      exact Filter.Eventually.of_forall (fun T => (mellin_rectangle_identity hab f hf T).symm)
    simpa only [sub_self] using hz'
  have he : Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) := by
    linear_combination -hz
  exact mul_left_cancel₀ Complex.I_ne_zero he

/-- A common decaying majorant supplies both horizontal limits. This is
the form used for a rapidly decreasing Mellin transform times an
L-function of polynomial growth. -/
theorem mellin_contour_shift_of_majorant {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (H : ℝ → ℝ) (hH : Integrable H)
    (hHtop : Tendsto H atTop (𝓝 0)) (hHbot : Tendsto H atBot (𝓝 0))
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (x + (t : ℂ) * Complex.I)‖ ≤ H t) :
    (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ, f (b + (y : ℂ) * Complex.I) := by
  have hline (x : ℝ) (hx : x ∈ Icc a b) :
      Integrable (fun y : ℝ => f (x + (y : ℂ) * Complex.I)) := by
    have hc : Continuous (fun y : ℝ => f (x + (y : ℂ) * Complex.I)) :=
      hf.continuousOn.comp_continuous
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
        (by intro y; simpa [closedVerticalStrip] using hx)
    exact hH.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall (hbound x hx))
  have hedge (t : ℝ) :
      ‖∫ x in a..b, f (x + (t : ℂ) * Complex.I)‖ ≤ H t * |b-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    apply hbound x
    rw [Set.uIoc_of_le hab] at hx
    exact ⟨hx.1.le,hx.2⟩
  apply mellin_contour_shift hab f hf
    (hline a ⟨le_rfl,hab⟩) (hline b ⟨hab,le_rfl⟩)
  · exact squeeze_zero_norm hedge (by simpa using hHtop.mul_const |b-a|)
  · have he : Tendsto (fun T : ℝ => ∫ x in a..b, f (x + ((-T : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 0) :=
      squeeze_zero_norm (fun T => hedge (-T))
        (by simpa using (hHbot.comp tendsto_neg_atTop_atBot).mul_const |b-a|)
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic properties of the actual compactly supported smooth norm
weights. Passing to logarithmic coordinates realizes every vertical
Mellin line as a Schwartz Fourier transform. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

lemma mellinVerticalSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ t : ℝ) :
    mellinVerticalSchwartz W hW hpos hsm σ t = mellin W (σ + (t : ℂ)*Complex.I) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rfl

theorem smooth_mellin_vertical_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin W) σ := by
  change Integrable (fun t : ℝ => mellin W (σ + (t : ℂ)*Complex.I))
  have hi : Integrable (mellinVerticalSchwartz W hW hpos hsm σ) :=
    (mellinVerticalSchwartz W hW hpos hsm σ).integrable
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  exact (mellinVerticalSchwartz_apply W hW hpos hsm σ t).symm

theorem smooth_mellin_vertical_decay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      (1+|t|)^A * ‖mellin W (σ + (t : ℂ)*Complex.I)‖ ≤ C := by
  let F := mellinVerticalSchwartz W hW hpos hsm σ
  let C := 2^A * (Finset.Iic (A,0)).sup
    (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  refine ⟨C+1,by dsimp [C]; positivity,?_⟩
  intro t
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (A,0)) (k := A) (n := 0) le_rfl le_rfl F t
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb
  rw [← mellinVerticalSchwartz_apply W hW hpos hsm σ t]
  exact hb.trans (by dsimp [C]; linarith)

/-- The Mellin inversion used for a single norm weight, with convergence
and the vertical integral discharged from its actual smooth support. -/
theorem smooth_mellin_inversion (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ)
    {x : ℝ} (hx : 0 < x) : mellinInv σ (mellin W) x = W x :=
  mellinInv_mellin_eq σ W hx (smooth_mellin_convergent W hW hpos hsm.continuous σ)
    (smooth_mellin_vertical_integrable W hW hpos hsm σ) hsm.continuous.continuousAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute sum-integral interchange for the full norm Dirichlet series
in Mellin inversion. No smooth-duality formula is an input. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

/-- The complete smoothed series has the exact Mellin representation on
any line of absolute convergence of its norm Dirichlet series. -/
theorem smooth_mellin_series {ι : Type*} [Countable ι]
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (σ : ℝ)
    (habs : Summable (fun i => ‖a i‖*(N i)^(-σ)))
    {Z : ℝ} (hZ : 0 < Z) :
    (∑' i, a i*W (N i/Z)) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W (σ+(τ:ℂ)*Complex.I) * (Z:ℂ)^(σ+(τ:ℂ)*Complex.I) *
        normDirichletSeries a N (σ+(τ:ℂ)*Complex.I) := by
  let s (τ : ℝ) : ℂ := σ+(τ:ℂ)*Complex.I
  let F (i : ι) (τ : ℝ) : ℂ :=
    (a i*(N i:ℂ)^(-s τ))*((Z:ℂ)^(s τ)*mellin W (s τ))
  have hsre (τ : ℝ) : (s τ).re = σ := by simp [s]
  have hsnre (τ : ℝ) : (-s τ).re = -σ := by simp [hsre]
  have hnorm (i : ι) (τ : ℝ) : ‖F i τ‖ =
      (‖a i‖*(N i)^(-σ))*Z^σ*‖mellin W (s τ)‖ := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i),
      Complex.norm_cpow_eq_rpow_re_of_pos hZ,hsre,hsnre]
    ring
  have hm : Integrable (fun τ => mellin W (s τ)) :=
    smooth_mellin_vertical_integrable W hW hpos hsm σ
  have hFi (i : ι) : Integrable (F i) := by
    have hn0 : (N i:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hN i).ne'
    have hz0 : (Z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
    have : NeZero (N i:ℂ) := ⟨hn0⟩
    have : NeZero (Z:ℂ) := ⟨hz0⟩
    have hs : Continuous s := by dsimp [s]; fun_prop
    have hc : Continuous (F i) :=
      (continuous_const.mul ((differentiable_const_cpow_of_neZero _).continuous.comp hs.neg)).mul
        (((differentiable_const_cpow_of_neZero _).continuous.comp hs).mul
          ((smooth_mellin_entire W hW hpos hsm.continuous).continuous.comp hs))
    exact (hm.norm.const_mul ((‖a i‖*(N i)^(-σ))*Z^σ)).mono'
      hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun τ => (hnorm i τ).le))
  have hsum : Summable (fun i => ∫ τ : ℝ, ‖F i τ‖) := by
    have he (i : ι) : (∫ τ : ℝ, ‖F i τ‖) =
        (‖a i‖*(N i)^(-σ))*(Z^σ*(∫ τ : ℝ, ‖mellin W (s τ)‖)) := by
      simp_rw [hnorm]
      rw [integral_const_mul]
      ring
    simpa only [he] using habs.mul_right (Z^σ*(∫ τ : ℝ, ‖mellin W (s τ)‖))
  have hi := integral_tsum_of_summable_integral_norm hFi hsum
  have hsingle (i : ι) : a i*W (N i/Z) =
      ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F i τ) := by
    rw [← smooth_mellin_inversion W hW hpos hsm σ (div_pos (hN i) hZ),mellinInv]
    simp only [RCLike.real_smul_eq_coe_mul]
    rw [← mul_assoc,mul_comm (a i),mul_assoc,← integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with τ
    rw [mellin_scale_cpow (hN i) hZ]
    dsimp [F,s]
    ring
  calc
    _ = ∑' i, ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F i τ) := tsum_congr hsingle
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∑' i, ∫ τ : ℝ, F i τ) := tsum_mul_left
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, ∑' i, F i τ) := by rw [hi]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with τ
      simp only [F,normDirichletSeries]
      rw [tsum_mul_right]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinStrip
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform rapid Mellin decay on a fixed closed real strip. The bound
comes from the actual compact logarithmic support, not an additional
analytic input. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

private lemma exp_linear_deriv_bound {M R σ u : ℝ} (hM : 0 ≤ M)
    (hσ : |σ| ≤ M) (hu : |u| ≤ R) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v : ℝ => Real.exp (-σ*v)) u‖ ≤
      M^n * Real.exp (M*R) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul]
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hσ n) _ (by positivity) (by positivity)
  apply Real.exp_le_exp.mpr
  calc
    -σ*u ≤ |-σ*u| := le_abs_self _
    _ = |σ| * |u| := by rw [abs_mul,abs_neg]
    _ ≤ M*R := mul_le_mul hσ hu (abs_nonneg _) hM

private lemma mellinLogSchwartz_eq_smul (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) :
    (mellinLogSchwartz W hW hpos hsm σ : ℝ → ℂ) =
      fun u => Real.exp (-σ*u) • mellinLogSchwartz W hW hpos hsm 0 u := by
  ext u
  simp [mellinLogSchwartz_apply]

theorem mellinLogSchwartz_seminorm_uniform (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ)
    (k n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n (mellinLogSchwartz W hW hpos hsm σ) ≤ C := by
  let G := mellinLogSchwartz W hW hpos hsm 0
  obtain ⟨R₀,hR₀⟩ := (logPullback_compact W hW hpos).isCompact.isBounded.exists_norm_le
  let R := max R₀ 1
  let M' := max M 0
  let B := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    (M'^i * Real.exp (M'*R)) * SchwartzMap.seminorm ℝ 0 (n-i) G
  have hR : 0 ≤ R := le_trans zero_le_one (le_max_right _ _)
  have hM : 0 ≤ M' := le_max_right _ _
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => by positivity)
  refine ⟨R^k*B, by positivity, ?_⟩
  intro σ hσ
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ R
  · have he : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (-σ*v)) := by fun_prop
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) he (G.smooth ⊤) u
      (n := n) (mod_cast le_top)
    have hg (i : ℕ) : ‖iteratedFDeriv ℝ i G u‖ ≤ SchwartzMap.seminorm ℝ 0 i G := by
      simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm ℝ 0 i G u
    have hb : ‖iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u‖ ≤ B := by
      rw [mellinLogSchwartz_eq_smul W hW hpos hsm σ]
      apply hd.trans
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (exp_linear_deriv_bound hM (hσ.trans (le_max_left _ _)) hu i) (by positivity)
      · exact hg (n-i)
      · positivity
      · positivity
    simpa only [Real.norm_eq_abs] using
      mul_le_mul (pow_le_pow_left₀ (by positivity : 0 ≤ |u|) hu k) hb
        (by positivity) (by positivity)
  · have hz : iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u = 0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
        (f := mellinLogSchwartz W hW hpos hsm σ) n hn
      have hs' : u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))) :=
        tsupport_smul_subset_right (fun v : ℝ => Real.exp (-σ*v))
          (fun v : ℝ => W (Real.exp (-v))) hs
      have hb : |u| ≤ R₀ := by simpa only [Real.norm_eq_abs] using hR₀ u hs'
      exact hu (hb.trans (le_max_left _ _))
    rw [hz,norm_zero,mul_zero]
    positivity

theorem mellinVertical_family_bounded (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ) :
    Bornology.IsVonNBounded ℝ
      ((fun σ => mellinVerticalSchwartz W hW hpos hsm σ) '' {σ | |σ| ≤ M}) := by
  let f : ℝ → 𝓢(ℝ,ℂ) := fun σ => mellinLogSchwartz W hW hpos hsm σ
  have hb : Bornology.IsVonNBounded ℝ (f '' {σ | |σ| ≤ M}) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C,hC,h⟩ := mellinLogSchwartz_seminorm_uniform W hW hpos hsm M i.1 i.2
    exact ⟨C+1,by linarith,fun σ hσ => (h σ hσ).trans_lt (by linarith)⟩
  let L : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.compCLM ℝ (by
      simp only [div_eq_mul_inv]
      fun_prop : (fun t : ℝ => t/(2*Real.pi)).HasTemperateGrowth)
      mellin_frequency_growth).comp (SchwartzMap.fourierTransformCLM ℝ)
  convert hb.image L using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Set.image_comp]
  rfl

theorem smooth_mellin_strip_decay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, |σ| ≤ M → ∀ t : ℝ,
      (1+|t|)^A * ‖mellin W (σ + (t : ℂ)*Complex.I)‖ ≤ C := by
  have hb := mellinVertical_family_bounded W hW hpos hsm M
  obtain ⟨C,hC,h⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_finset_seminorm_bounded
      (fun σ => mellinVerticalSchwartz W hW hpos hsm σ) |>.mp hb (Finset.Iic (A,0))
  refine ⟨2^A*C,by positivity,?_⟩
  intro σ hσ t
  have hp := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (A,0)) (k := A) (n := 0) le_rfl le_rfl
      (mellinVerticalSchwartz W hW hpos hsm σ) t
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,mellinVerticalSchwartz_apply] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (h σ hσ).le (by positivity))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinHeckeContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contour step for the full smooth character sum. Polynomial
vertical growth is an analytic property of the L-function; the decay,
integrability and vanishing edges are derived for the actual weight. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma mellinEdgeMajorant_integrable (C : ℝ) : Integrable (mellinEdgeMajorant C) := by
  have hi : Integrable (fun t : ℝ => (1+‖t‖)^(-(2:ℝ))) :=
    integrable_one_add_norm (by norm_num)
  convert hi.const_mul C using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  rw [mellinEdgeMajorant, Real.rpow_neg (by positivity), Real.rpow_ofNat,
    Real.norm_eq_abs, div_eq_mul_inv]

lemma mellinEdgeMajorant_tendsto (C : ℝ) :
    Tendsto (mellinEdgeMajorant C) atTop (𝓝 0) ∧
      Tendsto (mellinEdgeMajorant C) atBot (𝓝 0) := by
  have h (l : Filter ℝ) (hl : Tendsto (fun t : ℝ => |t|) l atTop) :
      Tendsto (mellinEdgeMajorant C) l (𝓝 0) := by
    change Tendsto (fun t : ℝ => C/(1+|t|)^2) l (𝓝 0)
    have hp : Tendsto (fun t : ℝ => (1+|t|)⁻¹) l (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun t => by linarith) hl)
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0),
      mul_zero] using (hp.pow 2).const_mul C
  exact ⟨h atTop tendsto_abs_atTop_atTop,h atBot tendsto_abs_atBot_atTop⟩

lemma norm_mellinHecke_integrand_le (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {a b Z : ℝ} (hZ : 1 ≤ Z) (t : ℝ)
    (L : ℂ → ℂ) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hL : ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖L (σ + ((τ-t : ℝ) : ℂ)*Complex.I)‖ ≤ C*(1+|τ-t|)^N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖mellin W (σ+(τ:ℂ)*Complex.I) * (Z:ℂ)^(σ+(τ:ℂ)*Complex.I) *
          L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤ mellinEdgeMajorant K τ := by
  obtain ⟨Cw,hCw,hdecay⟩ := smooth_mellin_strip_decay W hW hpos hsm (|a|+|b|) (N+2)
  let B := Z^b*C*(1+|t|)^N
  have hB : 0 ≤ B := by positivity
  refine ⟨B*Cw,by positivity,?_⟩
  intro σ hσ τ
  have hσabs : |σ| ≤ |a|+|b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le a,abs_nonneg b,hσ.1]
    · linarith [le_abs_self b,abs_nonneg a,hσ.2]
  have hscale : ‖(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)‖ ≤ Z^b := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < Z)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    exact Real.rpow_le_rpow_of_exponent_le hZ hσ.2
  have hshift : (1+|τ-t|)^N ≤ (1+|t|)^N*(1+|τ|)^N := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hd := abs_sub_le τ 0 t
    simp only [sub_zero,zero_sub,abs_neg] at hd
    nlinarith [mul_nonneg (abs_nonneg τ) (abs_nonneg t)]
  have hL' : ‖L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤
      C*((1+|t|)^N*(1+|τ|)^N) :=
    (hL σ hσ τ).trans (mul_le_mul_of_nonneg_left hshift hC)
  unfold mellinEdgeMajorant
  apply (le_div_iff₀ (by positivity : 0 < (1+|τ|)^2)).mpr
  calc
    _ ≤ (‖mellin W (σ+(τ:ℂ)*Complex.I)‖ * Z^b *
        (C*((1+|t|)^N*(1+|τ|)^N)))*(1+|τ|)^2 := by
      rw [norm_mul,norm_mul]
      gcongr
    _ = B*((1+|τ|)^(N+2)*‖mellin W (σ+(τ:ℂ)*Complex.I)‖) := by
      rw [pow_add]
      dsimp [B]
      ring
    _ ≤ B*Cw := mul_le_mul_of_nonneg_left (hdecay σ hσabs τ) hB

/-- Shifting the full Mellin integrand crosses no pole when the
nonprincipal L-function is entire. The weight supplies every required
decay and convergence assertion. -/
theorem mellinHecke_contour_shift (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {a b Z : ℝ} (hab : a ≤ b) (hZ : 1 ≤ Z) (t : ℝ)
    (L : ℂ → ℂ) (hLd : Differentiable ℂ L) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hL : ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤ C*(1+|τ-t|)^N) :
    (∫ τ : ℝ, mellin W (a+(τ:ℂ)*Complex.I) * (Z:ℂ)^(a+(τ:ℂ)*Complex.I) *
      L (a+((τ-t : ℝ):ℂ)*Complex.I)) =
    ∫ τ : ℝ, mellin W (b+(τ:ℂ)*Complex.I) * (Z:ℂ)^(b+(τ:ℂ)*Complex.I) *
      L (b+((τ-t : ℝ):ℂ)*Complex.I) := by
  let f : ℂ → ℂ := fun s => mellin W s*(Z:ℂ)^s*L (s-(t:ℂ)*Complex.I)
  have hZn : (Z:ℂ) ≠ 0 := by exact_mod_cast (show Z ≠ 0 by linarith)
  have : NeZero (Z:ℂ) := ⟨hZn⟩
  have hf : Differentiable ℂ f :=
    ((smooth_mellin_entire W hW hpos hsm.continuous).mul
      (differentiable_const_cpow_of_neZero _)).mul
      (hLd.comp (differentiable_id.sub_const _))
  obtain ⟨K,_,hbound⟩ := norm_mellinHecke_integrand_le W hW hpos hsm hZ t L hC N hL
  have heq (σ τ : ℝ) : f (σ+(τ:ℂ)*Complex.I) =
      mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
        L (σ+((τ-t : ℝ):ℂ)*Complex.I) := by
    dsimp [f]
    congr 2
    push_cast
    ring
  have hshift := mellin_contour_shift_of_majorant hab f hf.differentiableOn
    (mellinEdgeMajorant K) (mellinEdgeMajorant_integrable K)
    (mellinEdgeMajorant_tendsto K).1 (mellinEdgeMajorant_tendsto K).2
    (by intro σ hσ τ; rw [heq]; exact hbound σ hσ τ)
  simpa only [heq] using hshift

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialStrip
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial strip growth from finite order and polynomial boundary
bounds. The finite-order hypothesis is much weaker than the conclusion;
the proof uses the Phragmén–Lindelöf theorem in mathlib. -/

noncomputable section
open Set Filter Asymptotics
namespace CubicFirstMoment

lemma finiteVerticalOrder_double_exp {f : ℂ → ℂ} {a b c : ℝ}
    (hf : FiniteVerticalOrder f a b) (hc : 0 < c) :
    f =O[comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b)]
      (fun z : ℂ => Real.exp (Real.exp (c*|z.im|))) := by
  obtain ⟨C,k,hC,hf⟩ := hf
  have he := ((isLittleO_pow_exp_pos_mul_atTop k hc).const_mul_left (C*2^k)).bound
    (by norm_num : (0:ℝ) < 1)
  have hlarge : ∀ᶠ u : ℝ in atTop,
      C*(1+u)^k ≤ Real.exp (c*u) := by
    filter_upwards [he,eventually_ge_atTop (1:ℝ)] with u hu hu1
    have hu0 : 0 ≤ u := le_trans zero_le_one hu1
    have hpow : (1+u)^k ≤ (2*u)^k := pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      C*(1+u)^k ≤ C*(2*u)^k := mul_le_mul_of_nonneg_left hpow hC
      _ = (C*2^k)*u^k := by rw [mul_pow]; ring
      _ ≤ Real.exp (c*u) := by
        exact (le_abs_self _).trans (by
          simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul] using hu)
  apply IsBigO.of_bound' 
  have hlarge' := ((tendsto_comap : Tendsto (abs ∘ Complex.im) (comap (abs ∘ Complex.im) atTop) atTop).eventually hlarge).filter_mono (inf_le_left :
    comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b) ≤
      comap (abs ∘ Complex.im) atTop)
  have hs : ∀ᶠ z : ℂ in comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Ioo a b), z.re ∈ Ioo a b :=
    Filter.Eventually.filter_mono inf_le_right (by simp)
  filter_upwards [hlarge',hs] with z hz hzstrip
  exact (hf z ⟨hzstrip.1.le,hzstrip.2.le⟩).trans <| by
    simpa using Real.exp_le_exp.mpr hz

private lemma strip_shift_norm_lower {a : ℝ} {z : ℂ} (hz : a ≤ z.re) :
    1 ≤ ‖z+((1-a:ℝ):ℂ)‖ := by
  have hr := Complex.re_le_norm (z+((1-a:ℝ):ℂ))
  simp only [Complex.add_re,Complex.ofReal_re] at hr
  linarith

private lemma strip_shift_norm_upper {a b : ℝ} {z : ℂ}
    (hz : z.re ∈ Icc a b) :
    ‖z+((1-a:ℝ):ℂ)‖ ≤ (b-a+1)*(1+|z.im|) := by
  have hn := Complex.norm_le_abs_re_add_abs_im (z+((1-a:ℝ):ℂ))
  simp only [Complex.add_re,Complex.ofReal_re,Complex.add_im,Complex.ofReal_im,add_zero] at hn
  rw [abs_of_nonneg (by linarith [hz.1] : 0 ≤ z.re+(1-a))] at hn
  nlinarith [abs_nonneg z.im,hz.1,hz.2]

/-- A finite-order holomorphic function with polynomial bounds on both
vertical edges has polynomial growth throughout the strip. -/
theorem polynomial_strip_of_finite_order {f : ℂ → ℂ} {a b C : ℝ}
    (hab : a < b) (hfd : Differentiable ℂ f) (hf : FiniteVerticalOrder f a b)
    (hC : 0 ≤ C) (n : ℕ)
    (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C*(1+|z.im|)^n)
    (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C*(1+|z.im|)^n) :
    ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ (C*2^n*(b-a+1)^n)*(1+|z.im|)^n := by
  let g (z : ℂ) := f z/(z+((1-a:ℝ):ℂ))^n
  have hcl : closure (Complex.re ⁻¹' Ioo a b) ⊆ Complex.re ⁻¹' Icc a b := by
    apply closure_minimal
    · intro z hz
      exact ⟨hz.1.le,hz.2.le⟩
    · exact isClosed_Icc.preimage Complex.continuous_re
  have hne {z : ℂ} (hz : a ≤ z.re) : z+((1-a:ℝ):ℂ) ≠ 0 := by
    have hn := strip_shift_norm_lower hz
    intro he
    rw [he,norm_zero] at hn
    norm_num at hn
  have hgd : DiffContOnCl ℂ g (Complex.re ⁻¹' Ioo a b) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    exact (hfd z).differentiableWithinAt.div
      (((differentiable_id.add_const ((1-a:ℝ):ℂ)).pow n) z).differentiableWithinAt
      (pow_ne_zero _ (hne (hcl hz).1))
  have hgnorm {z : ℂ} (hz : a ≤ z.re) : ‖g z‖ ≤ ‖f z‖ := by
    dsimp [g]
    rw [norm_div,norm_pow]
    exact div_le_self (_root_.norm_nonneg _) (one_le_pow₀ (strip_shift_norm_lower hz))
  have hgf : FiniteVerticalOrder g a b := by
    obtain ⟨D,k,hD,hf⟩ := hf
    exact ⟨D,k,hD,fun z hz => (hgnorm hz.1).trans (hf z hz)⟩
  have hboundary {z : ℂ} (hz : z.re ∈ Icc a b)
      (hfz : ‖f z‖ ≤ C*(1+|z.im|)^n) : ‖g z‖ ≤ C*2^n := by
    have hn := strip_shift_norm_lower hz.1
    have hi : |z.im| ≤ ‖z+((1-a:ℝ):ℂ)‖ := by
      simpa using Complex.abs_im_le_norm (z+((1-a:ℝ):ℂ))
    have hpow : (1+|z.im|)^n ≤ (2*‖z+((1-a:ℝ):ℂ)‖)^n :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    dsimp [g]
    rw [norm_div,norm_pow]
    apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hn) _)).mpr
    calc
      ‖f z‖ ≤ C*(1+|z.im|)^n := hfz
      _ ≤ C*(2*‖z+((1-a:ℝ):ℂ)‖)^n := mul_le_mul_of_nonneg_left hpow hC
      _ = _ := by rw [mul_pow]; ring
  have hc : 0 < Real.pi/(2*(b-a)) := div_pos Real.pi_pos (by linarith)
  have hcb : Real.pi/(2*(b-a)) < Real.pi/(b-a) := by
    apply div_lt_div_of_pos_left Real.pi_pos (by linarith) (by linarith)
  intro z hz
  have hg : ‖g z‖ ≤ C*2^n := PhragmenLindelof.vertical_strip hgd
    ⟨Real.pi/(2*(b-a)),hcb,1,by
      simpa only [one_mul] using finiteVerticalOrder_double_exp hgf hc⟩
    (fun w hw => hboundary ⟨hw.ge,hw ▸ hab.le⟩ (ha w hw))
    (fun w hw => hboundary ⟨hw ▸ hab.le,hw.le⟩ (hb w hw)) hz.1 hz.2
  have hfeq : ‖f z‖ = ‖g z‖*‖z+((1-a:ℝ):ℂ)‖^n := by
    dsimp [g]
    rw [norm_div,norm_pow,div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr (hne hz.1)))]
  rw [hfeq]
  calc
    _ ≤ (C*2^n)*((b-a+1)*(1+|z.im|))^n :=
      mul_le_mul hg (pow_le_pow_left₀ (_root_.norm_nonneg _) (strip_shift_norm_upper hz) n)
        (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaElementaryGrowth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary bounds used to discharge reciprocal Gamma growth. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma gamma_norm_le_real {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma gamma_norm_le_add_nat {s : ℂ} (hs : 1 ≤ |s.im|) (n : ℕ) :
    ‖Complex.Gamma s‖ ≤ ‖Complex.Gamma (s+n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have him : (s+(n:ℂ)).im = s.im := by simp
    have hn : 1 ≤ ‖s+(n:ℂ)‖ := hs.trans (by simpa using Complex.abs_im_le_norm (s+(n:ℂ)))
    have hne : s+(n:ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hn)
    calc
      _ ≤ ‖Complex.Gamma (s+n)‖ := ih
      _ ≤ ‖s+(n:ℂ)‖*‖Complex.Gamma (s+n)‖ :=
        le_mul_of_one_le_left (_root_.norm_nonneg _) hn
      _ = ‖Complex.Gamma (s+(n+1:ℕ))‖ := by
        rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hne, norm_mul]

lemma complex_sin_norm_le_exp_im (s : ℂ) :
    ‖Complex.sin s‖ ≤ Real.exp |s.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have hp : ‖Complex.exp (-s*Complex.I)‖ ≤ Real.exp |s.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using le_abs_self s.im
  have hm : ‖Complex.exp (s*Complex.I)‖ ≤ Real.exp |s.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using neg_le_abs s.im
  have hd := (norm_sub_le (Complex.exp (-s*Complex.I)) (Complex.exp (s*Complex.I))).trans
    (add_le_add hp hm)
  norm_num
  simp only [neg_mul] at hd
  linarith

lemma gamma_real_interval_bound {a b : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Icc a b, Real.Gamma x ≤ M := by
  have hc : ContinuousOn (fun x : ℝ => Complex.Gamma (x:ℂ)) (Icc a b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply (Complex.continuousAt_Gamma (x:ℂ) ?_).comp Complex.continuous_ofReal.continuousAt
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.ofReal_re,Complex.neg_re,Complex.natCast_re] at hr
    have : (0:ℝ) ≤ n := by positivity
    linarith [hx.1]
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x hx
  exact (Complex.re_le_norm (Complex.Gamma (x:ℂ))).trans ((hM x hx).trans (le_max_left _ _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaBetaComparison
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Beta-integral comparison for the Gamma quotient. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

private lemma beta_real_integral_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ in (0:ℝ)..1, t^(x-1)*(1-t)^(y-1)) =
      Real.Gamma x*Real.Gamma y/Real.Gamma (x+y) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (∫ t : ℝ in (0:ℝ)..1, ((t^(x-1)*(1-t)^(y-1):ℝ):ℂ)) =
      Complex.betaIntegral (x:ℂ) (y:ℂ) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    simp only [Complex.ofReal_mul,Complex.ofReal_cpow ht.1,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2),Complex.ofReal_sub,Complex.ofReal_one]
  rw [he,Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hx) (by simpa using hy)]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,← Complex.ofReal_add,Complex.Gamma_ofReal]

lemma beta_norm_le_real (s : ℂ) {d : ℝ} (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.betaIntegral s (d:ℂ)‖ ≤
      Real.Gamma s.re*Real.Gamma d/Real.Gamma (s.re+d) := by
  rw [← beta_real_integral_eq s.re d hs hd]
  unfold Complex.betaIntegral
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)).trans_eq
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  have hp : 0 < 1-t := sub_pos.mpr ht.2
  rw [show (1:ℂ)-(t:ℂ) = ((1-t:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp

lemma gamma_real_shift_ratio_bound (s : ℂ) {d : ℝ} (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.Gamma s‖/‖Complex.Gamma (s+(d:ℂ))‖ ≤
      Real.Gamma s.re/Real.Gamma (s.re+d) := by
  have h := beta_norm_le_real s hs hd
  have hg : 0 < Real.Gamma d := Real.Gamma_pos_of_pos hd
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hs (by simpa using hd),
    norm_div,norm_mul,Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hg] at h
  apply (mul_le_mul_iff_right₀ hg).mp
  first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

lemma gamma_shift_ratio_bound (x y t : ℝ) (n : ℕ) (hx : 0 < x)
    (hgap : 0 < y+(n:ℝ)-x) :
    ‖Complex.Gamma ((x:ℂ)+(t:ℂ)*Complex.I) /
      Complex.Gamma ((y:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (Real.Gamma x/Real.Gamma (y+n))*
        ‖(ascPochhammer ℂ n).eval ((y:ℂ)+(t:ℂ)*Complex.I)‖ := by
  let z : ℂ := (y:ℂ)+(t:ℂ)*Complex.I
  let w : ℂ := (x:ℂ)+(t:ℂ)*Complex.I
  have hyn : 0 < y+(n:ℝ) := by linarith
  have hGn : Complex.Gamma (z+n) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa [z] using hyn)
  by_cases hG : Complex.Gamma z = 0
  · change ‖Complex.Gamma w/Complex.Gamma z‖ ≤ _
    rw [hG,div_zero,norm_zero]
    exact mul_nonneg (div_nonneg (Real.Gamma_pos_of_pos hx).le
      (Real.Gamma_pos_of_pos hyn).le) (_root_.norm_nonneg _)
  have hreg : ∀ k : ℕ, z ≠ -(k:ℂ) := by
    intro k hk
    exact hG (by rw [hk,Complex.Gamma_neg_nat_eq_zero])
  have hp := congrArg (fun u : ℂ => ‖u‖) (Complex.Gamma_add_nat_div_Gamma_eq (n := n) z hreg)
  rw [norm_div] at hp
  have hshift : w+((y+(n:ℝ)-x:ℝ):ℂ) = z+n := by dsimp [w,z]; push_cast; ring
  have hb := gamma_real_shift_ratio_bound w (by simpa [w] using hx) hgap
  rw [hshift,show w.re=x by simp [w],show x+(y+(n:ℝ)-x)=y+n by ring] at hb
  change ‖Complex.Gamma w/Complex.Gamma z‖ ≤ _
  rw [norm_div]
  calc
    _ = (‖Complex.Gamma w‖/‖Complex.Gamma (z+n)‖)*
        ‖(ascPochhammer ℂ n).eval z‖ := by
      rw [← hp]
      field_simp [norm_ne_zero_iff.mpr hG,norm_ne_zero_iff.mpr hGn]
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (_root_.norm_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaInverseGrowth
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal Gamma has the coarse strip growth needed for the completed
Hecke functions. This uses Euler's integral, reflection and recurrence. -/
noncomputable section
open Set
namespace CubicFirstMoment

private lemma gamma_inverse_reflection {s : ℂ} (hs : 1 ≤ |s.im|) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1-s)*Complex.sin (Real.pi*s)/Real.pi := by
  have hi : s.im ≠ 0 := by intro h; simp only [h,abs_zero] at hs; linarith
  have hreg : ∀ n : ℕ, s ≠ -(n:ℂ) := by
    intro n hn
    apply hi
    simpa using congrArg Complex.im hn
  have hreg' : ∀ n : ℕ, 1-s ≠ -(n:ℂ) := by
    intro n hn
    apply hi
    have hh := congrArg Complex.im hn
    simpa using hh
  have hG := Complex.Gamma_ne_zero hreg
  have hG' := Complex.Gamma_ne_zero hreg'
  have hr := Complex.Gamma_mul_Gamma_one_sub s
  have hsin : Complex.sin (Real.pi*s) ≠ 0 := by
    intro hz
    rw [hz,div_zero] at hr
    exact mul_ne_zero hG hG' hr
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr' := (eq_div_iff hsin).mp hr
  apply (eq_div_iff hp).mpr
  calc
    _ = (Complex.Gamma s)⁻¹*(Complex.Gamma s*Complex.Gamma (1-s)*
        Complex.sin (Real.pi*s)) := congrArg (fun z : ℂ => (Complex.Gamma s)⁻¹*z) hr'.symm
    _ = _ := by field_simp [hG]

private lemma gamma_inverse_large_height_bound (a b : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℂ, s.re ∈ Icc a b → 1 ≤ |s.im| →
      ‖(Complex.Gamma s)⁻¹‖ ≤ D*Real.exp (Real.pi*|s.im|) := by
  obtain ⟨n,hn⟩ := exists_nat_gt b
  have hlo : 0 < 1-b+(n:ℝ) := by linarith
  obtain ⟨M,hM,hbound⟩ := gamma_real_interval_bound (b := 1-a+(n:ℝ)) hlo
  refine ⟨M/Real.pi,div_pos hM Real.pi_pos,?_⟩
  intro s hs ht
  have hz : 0 < (1-s+(n:ℂ)).re := by
    simp only [Complex.add_re,Complex.sub_re,Complex.one_re,Complex.natCast_re]
    linarith [hs.2]
  have hΓ : ‖Complex.Gamma (1-s)‖ ≤ M := by
    calc
      _ ≤ ‖Complex.Gamma (1-s+(n:ℂ))‖ := gamma_norm_le_add_nat (by simpa using ht) n
      _ ≤ Real.Gamma (1-s+(n:ℂ)).re := gamma_norm_le_real hz
      _ ≤ M := hbound _ (by
        simp only [mem_Icc,Complex.add_re,Complex.sub_re,Complex.one_re,Complex.natCast_re]
        constructor <;> linarith [hs.1,hs.2])
  have hsin : ‖Complex.sin (Real.pi*s)‖ ≤ Real.exp (Real.pi*|s.im|) := by
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      abs_mul,abs_of_pos Real.pi_pos] using complex_sin_norm_le_exp_im (Real.pi*s)
  rw [gamma_inverse_reflection ht,norm_div,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  exact (div_le_div_of_nonneg_right (mul_le_mul hΓ hsin (_root_.norm_nonneg _) hM.le)
    Real.pi_pos.le).trans_eq (by ring)

/-- The exact reciprocal-Gamma strip input is an elementary theorem. -/
theorem gammaInverseFiniteOrder (a b : ℝ) : GammaInverseFiniteOrder a b := by
  obtain ⟨D,hD,hlarge⟩ := gamma_inverse_large_height_bound a b
  let F : ℝ × ℝ → ℂ := fun p => (Complex.Gamma ((p.1:ℂ)+(p.2:ℂ)*Complex.I))⁻¹
  have hF : Continuous F := by
    simpa only [F,one_div,Function.comp_def] using Complex.differentiable_one_div_Gamma.continuous.comp
      (show Continuous (fun p : ℝ × ℝ => (p.1:ℂ)+(p.2:ℂ)*Complex.I) by fun_prop)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := (Icc a b) ×ˢ (Icc (-1:ℝ) 1)) hF.continuousOn
  let E := max (max C 1) D
  have hE1 : 1 ≤ E := (le_max_right C 1).trans (le_max_left _ _)
  have hE : 0 < E := zero_lt_one.trans_le hE1
  have hlog : 0 ≤ Real.log E := Real.log_nonneg hE1
  refine ⟨Real.log E+Real.pi,add_nonneg hlog Real.pi_pos.le,?_⟩
  intro s hs
  have hb : ‖(Complex.Gamma s)⁻¹‖ ≤ E*Real.exp (Real.pi*|s.im|) := by
    by_cases ht : |s.im| ≤ 1
    · have hc := hC (s.re,s.im) ⟨hs,abs_le.mp ht⟩
      have hc' : ‖(Complex.Gamma s)⁻¹‖ ≤ C := by
        simpa only [F,Complex.re_add_im] using hc
      exact (hc'.trans ((le_max_left C 1).trans (le_max_left _ _))).trans
        (le_mul_of_one_le_right hE.le (Real.one_le_exp (mul_nonneg Real.pi_pos.le (abs_nonneg _))))
    · exact (hlarge s hs (le_of_not_ge ht)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  have hquad1 : 1 ≤ (1+|s.im|)^2 := by nlinarith [abs_nonneg s.im,sq_nonneg |s.im|]
  have hquad2 : |s.im| ≤ (1+|s.im|)^2 := by nlinarith [abs_nonneg s.im,sq_nonneg |s.im|]
  calc
    _ ≤ E*Real.exp (Real.pi*|s.im|) := hb
    _ = Real.exp (Real.log E+Real.pi*|s.im|) := by rw [Real.exp_add,Real.exp_log hE]
    _ ≤ Real.exp ((Real.log E+Real.pi)*(1+|s.im|)^2) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ Real.log E*(1+|s.im|)^2+Real.pi*(1+|s.im|)^2 :=
          add_le_add (by simpa using mul_le_mul_of_nonneg_left hquad1 hlog)
            (mul_le_mul_of_nonneg_left hquad2 Real.pi_pos.le)
        _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaQuotientGrowth
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded-strip Gamma quotient follows from the Beta integral and
integer recurrence, with the fixed angular shift retained. -/
noncomputable section
open Set
namespace CubicFirstMoment

private lemma pochhammer_norm_bound (n : ℕ) (z : ℂ) :
    ‖(ascPochhammer ℂ n).eval z‖ ≤ (‖z‖+(n:ℝ))^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,norm_mul]
    have hn : ‖z+(n:ℂ)‖ ≤ ‖z‖+(n:ℝ) := by simpa using norm_add_le z (n:ℂ)
    calc
      _ ≤ (‖z‖+(n:ℝ))^n*(‖z‖+(n:ℝ)) :=
        mul_le_mul ih hn (_root_.norm_nonneg _) (by positivity)
      _ = (‖z‖+(n:ℝ))^(n+1) := (pow_succ _ _).symm
      _ ≤ (‖z‖+((n+1:ℕ):ℝ))^(n+1) := by
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        linarith

private lemma gamma_positive_ratio_compact {a k : ℝ} (hk : -(1/2:ℝ) < k)
    (n : ℕ) (hn : 1-2*a < (n:ℝ)) :
    ∃ M : ℝ, 0 < M ∧ ∀ σ ∈ Icc a (1/2:ℝ),
      Real.Gamma (1-σ+k)/Real.Gamma (σ+k+n) ≤ M := by
  let F : ℝ → ℂ := fun σ => Complex.Gamma ((1-σ+k:ℝ):ℂ)/
    Complex.Gamma ((σ+k+n:ℝ):ℂ)
  have hx {σ : ℝ} (hσ : σ ∈ Icc a (1/2:ℝ)) : 0 < 1-σ+k := by linarith [hσ.2]
  have hy {σ : ℝ} (hσ : σ ∈ Icc a (1/2:ℝ)) : 0 < σ+k+n := by linarith [hσ.1,hσ.2]
  have hc : ContinuousOn F (Icc a (1/2:ℝ)) := by
    intro σ hσ
    have hreg {x : ℝ} (hp : 0 < x) : ∀ m : ℕ, (x:ℂ) ≠ -(m:ℂ) := by
      intro m hm
      have hr := congrArg Complex.re hm
      simp only [Complex.ofReal_re,Complex.neg_re,Complex.natCast_re] at hr
      have : (0:ℝ) ≤ m := by positivity
      linarith
    apply ContinuousAt.continuousWithinAt
    have ht : ContinuousAt (fun τ : ℝ => Complex.Gamma ((1-τ+k:ℝ):ℂ)) σ :=
      (Complex.continuousAt_Gamma _ (hreg (hx hσ))).comp
        (f := fun τ : ℝ => ((1-τ+k:ℝ):ℂ)) (by fun_prop)
    have hb : ContinuousAt (fun τ : ℝ => Complex.Gamma ((τ+k+n:ℝ):ℂ)) σ :=
      (Complex.continuousAt_Gamma _ (hreg (hy hσ))).comp
        (f := fun τ : ℝ => ((τ+k+n:ℝ):ℂ)) (by fun_prop)
    exact ht.div hb
      (Complex.Gamma_ne_zero_of_re_pos (s := ((σ+k+n:ℝ):ℂ)) (by simpa using hy hσ))
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro σ hσ
  have he : ‖F σ‖ = Real.Gamma (1-σ+k)/Real.Gamma (σ+k+n) := by
    dsimp [F]
    rw [norm_div,Complex.Gamma_ofReal,Complex.Gamma_ofReal,Complex.norm_real,
      Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos (hx hσ)),abs_of_pos (Real.Gamma_pos_of_pos (hy hσ))]
  rw [← he]
  exact (hM σ hσ).trans (le_max_left _ _)

/-- The exact fixed-angular quotient input used by the conditional proof. -/
theorem angularGammaQuotientStripBound_proved (k a : ℝ) (hk : -(1/2:ℝ) < k) :
    AngularGammaQuotientStripBound k a := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1-2*a)
  obtain ⟨M,hM,hbound⟩ := gamma_positive_ratio_compact hk n hn
  let D := |a+k|+|(1/2:ℝ)+k|+(n:ℝ)+1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨M*D^n,n,mul_nonneg hM.le (pow_nonneg hD.le _),?_⟩
  intro σ hσ t
  have hx : 0 < 1-σ+k := by linarith [hσ.2]
  have hgap : 0 < (σ+k)+(n:ℝ)-(1-σ+k) := by linarith [hσ.1]
  have hb := gamma_shift_ratio_bound (1-σ+k) (σ+k) t n hx hgap
  have hnum : 1-((σ:ℂ)+(t:ℂ)*Complex.I)+(k:ℂ) =
      starRingEnd ℂ (((1-σ+k:ℝ):ℂ)+(t:ℂ)*Complex.I) := by
    apply Complex.ext <;> simp
  have hden : (σ:ℂ)+(t:ℂ)*Complex.I+(k:ℂ) =
      ((σ+k:ℝ):ℂ)+(t:ℂ)*Complex.I := by push_cast; ring
  have ha : |σ+k| ≤ |a+k|+|(1/2:ℝ)+k| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (a+k),abs_nonneg ((1/2:ℝ)+k),hσ.1]
    · linarith [le_abs_self ((1/2:ℝ)+k),abs_nonneg (a+k),hσ.2]
  have hz : ‖((σ+k:ℝ):ℂ)+(t:ℂ)*Complex.I‖ ≤ |σ+k|+|t| := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,norm_mul,Complex.norm_I,mul_one]
      using norm_add_le (((σ+k:ℝ):ℂ)) ((t:ℂ)*Complex.I)
  have hpoly : ‖(ascPochhammer ℂ n).eval (((σ+k:ℝ):ℂ)+(t:ℂ)*Complex.I)‖ ≤
      D^n*(1+|t|)^n := by
    apply (pochhammer_norm_bound _ _).trans
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hD1 : 1 ≤ D := by
      dsimp [D]
      linarith [abs_nonneg (a+k),abs_nonneg ((1/2:ℝ)+k),show (0:ℝ) ≤ n by positivity]
    dsimp [D] at *
    nlinarith [abs_nonneg t,abs_nonneg (a+k),abs_nonneg ((1/2:ℝ)+k),
      show (0:ℝ) ≤ n by positivity]
  unfold angularGammaFEQuotient
  rw [hnum,hden,Complex.Gamma_conj,norm_div,Complex.norm_conj]
  rw [norm_div] at hb
  apply hb.trans
  calc
    _ ≤ M*(D^n*(1+|t|)^n) :=
      mul_le_mul (hbound σ hσ) hpoly (_root_.norm_nonneg _) hM.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaMellinSplitAngular
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The even-weight Mellin split for the actual angular derivatives. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment

lemma theta_mellin_split_angular (k : ℕ) {f g : ℝ → ℂ} {ε : ℂ}
    (hFE : ∀ t : ℝ,0<t → f (1/t)=ε*(t:ℂ)^(2*k)*g t)
    {s : ℂ} (hf : MellinConvergent (thetaUpper f) s)
    (hg : MellinConvergent (thetaUpper g) (((2*k:ℕ):ℂ)-s)) :
    MellinConvergent f s ∧
      mellin f s=mellin (thetaUpper f) s+ε*mellin (thetaUpper g) (((2*k:ℕ):ℂ)-s) := by
  let v : ℝ → ℂ := fun t => ε • ((t:ℂ)^(-((2*k:ℕ):ℂ)) • thetaUpper g t⁻¹)
  have hginv : MellinConvergent (fun t : ℝ => thetaUpper g t⁻¹) (s-((2*k:ℕ):ℂ)) := by
    have he : (s-((2*k:ℕ):ℂ))/(-1:ℝ)=((2*k:ℕ):ℂ)-s := by push_cast; ring
    rw [←he] at hg
    simpa only [Real.rpow_neg_one] using
      (MellinConvergent.comp_rpow (by norm_num : (-1:ℝ)≠0)).mpr hg
  have hv : MellinConvergent v s :=
    (MellinConvergent.cpow_smul.mpr (by simpa only [sub_eq_add_neg] using hginv)).const_smul ε
  have hid : f=ᵐ[volume.restrict (Ioi 0)] (fun t => thetaUpper f t+v t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      (volume.restrict (Ioi 0)).ae_ne 1] with t ht ht1
    change 0<t at ht
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · have hinv : 1<t⁻¹ := (one_lt_inv₀ ht).mpr hlt
      have ht' := hFE t⁻¹ (inv_pos.mpr ht)
      simp only [one_div,inv_inv,Complex.ofReal_inv] at ht'
      rw [thetaUpper,indicator_of_notMem (show t∉Ioi (1:ℝ) from not_lt.mpr hlt.le),zero_add]
      dsimp only [v]
      rw [thetaUpper,indicator_of_mem (show t⁻¹∈Ioi (1:ℝ) from hinv),smul_eq_mul,smul_eq_mul]
      rw [Complex.cpow_neg,Complex.cpow_natCast]
      simpa only [inv_pow,mul_assoc] using ht'
    · have hinv : t⁻¹<1 := (inv_lt_one₀ ht).mpr hgt
      rw [thetaUpper,indicator_of_mem (show t∈Ioi (1:ℝ) from hgt)]
      dsimp only [v]
      rw [thetaUpper,indicator_of_notMem (show t⁻¹∉Ioi (1:ℝ) from not_lt.mpr hinv.le)]
      simp
  have hsum := hasMellin_add hf hv
  constructor
  · apply hsum.1.congr
    filter_upwards [hid] with t ht
    rw [ht]
  · calc
      mellin f s=mellin (fun t => thetaUpper f t+v t) s := by
        apply integral_congr_ae
        filter_upwards [hid] with t ht
        rw [ht]
      _ = mellin (thetaUpper f) s+mellin v s := hsum.2
      _ = _ := by
        dsimp only [v]
        rw [mellin_const_smul,mellin_cpow_smul,mellin_comp_inv]
        simp only [smul_eq_mul,show -(s+(-((2*k:ℕ):ℂ)))=((2*k:ℕ):ℂ)-s by ring]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaMellinAngularFunctional
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Mellin change of variables for an even-weight reciprocal identity. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma theta_mellin_functional_angular (k : ℕ) {f g : ℝ→ℂ} {ε : ℂ}
    (hFE : ∀ t : ℝ,0<t → f (1/t)=ε*(t:ℂ)^(2*k)*g t) (s : ℂ) :
    mellin f s=ε*mellin g (((2*k:ℕ):ℂ)-s) := by
  calc
    _ = mellin (fun t : ℝ => f t⁻¹) (-s) := by rw [mellin_comp_inv,neg_neg]
    _ = mellin (fun t : ℝ => ε • ((t:ℂ)^((2*k:ℕ):ℂ) • g t)) (-s) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [←one_div, hFE t ht, Complex.cpow_natCast]
      simp only [smul_eq_mul]
      ring
    _ = _ := by
      rw [mellin_const_smul,mellin_cpow_smul]
      simp only [smul_eq_mul,show -s+((2*k:ℕ):ℂ)=((2*k:ℕ):ℂ)-s by ring]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaUpperVerticalBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform vertical bounds for upper Mellin integrals from one real moment. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma thetaUpperNormMass_nonneg (f : ℝ→ℂ) (b : ℝ) : 0≤thetaUpperNormMass f b :=
  integral_nonneg (fun _ => _root_.norm_nonneg _)

theorem thetaUpper_vertical_bound {f : ℝ→ℂ} {b : ℝ}
    (hf : MellinConvergent (thetaUpper f) (b:ℂ)) {s : ℂ} (hs : s.re≤b) :
    ‖mellin (thetaUpper f) s‖≤thetaUpperNormMass f b := by
  unfold mellin thetaUpperNormMass
  apply norm_integral_le_of_norm_le hf.norm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0<t at ht
  by_cases ht1 : 1<t
  · rw [norm_smul,norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp only [Complex.sub_re,Complex.one_re,Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le ht1.le (sub_le_sub_right hs 1)) (_root_.norm_nonneg _)
  · simp only [thetaUpper,indicator_of_notMem (show t∉Ioi (1:ℝ) from ht1),smul_zero,norm_zero,le_refl]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEven
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The evenness of the cubic theta coefficients, derived directly from
all cases of the arithmetic formula, and the resulting horizontal symmetry. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaArithmetic_term_reflection (z : ℂ) (v : ℝ) (n : Eisenstein) :
    cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v (-n) =
      cubicThetaSeriesTerm cubicThetaArithmeticCoefficient (-z) v n := by
  by_cases hn : n = 0
  · simp [cubicThetaSeriesTerm,hn]
  · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
    simp only [cubicThetaSeriesTerm,hn,hneg,ite_false, if_false,cubicThetaArithmeticCoefficient_even]
    have hf : cubicThetaFrequency (-n) = -cubicThetaFrequency n := by
      simp only [cubicThetaFrequency,Subalgebra.coe_neg,neg_div]
    have hpair : tracePair (-cubicThetaFrequency n) z = tracePair (cubicThetaFrequency n) (-z) := by
      unfold tracePair
      rw [neg_mul,mul_neg]
    rw [hf,norm_neg,hpair]

/-- The series, as well as its arithmetic coefficients, is even. -/
theorem cubicThetaArithmetic_even (z : ℂ) (v : ℝ) :
    cubicThetaNonconstant cubicThetaArithmeticCoefficient (-z,v) =
      cubicThetaNonconstant cubicThetaArithmeticCoefficient (z,v) := by
  unfold cubicThetaNonconstant
  rw [←(Equiv.neg Eisenstein).tsum_eq (fun n =>
    cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v n)]
  apply tsum_congr
  intro n
  exact (cubicThetaArithmetic_term_reflection z v n).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact primary cube coefficients isolated in DR v3 (5.17).
This connects the constructed theta expansion to the completed Gauss sum. -/
noncomputable section
namespace CubicFirstMoment

/-- Conjugating the primary coefficient gives the original Gauss sum,
with the exact real normalization retained. -/
lemma cubicThetaArithmeticCoefficient_primary_conj {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    star (cubicThetaArithmeticCoefficient (lambdaE*c*d^3)) =
      ((81/(Real.sqrt (norm c)*norm d):ℝ):ℂ)*gauss c := by
  rw [cubicThetaArithmeticCoefficient_primary hc hd hs,star_mul,star_star]
  simp only [Complex.star_def,Complex.conj_ofReal]
  ring

lemma cubicThetaFrequency_primary_norm (c d : Eisenstein) :
    ‖cubicThetaFrequency (lambdaE*c*d^3)‖ =
      Real.sqrt 3*Real.sqrt (norm c)*(Real.sqrt (norm d))^3/9 := by
  have hcN := norm_nonneg c
  have hdN := norm_nonneg d
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (by positivity)).mp
  rw [cubicThetaFrequency_sq]
  have he : norm (lambdaE*c*d^3) = 3*norm c*norm d^3 := by
    change Complex.normSq (((lambdaE*c*d^3:Eisenstein):ℂ)) = _
    simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,Complex.normSq_mul,
      map_pow,lambdaE_coe,traceLambda_normSq]
    rfl
  rw [he]
  calc
    _ = (Real.sqrt 3)^2*(Real.sqrt (norm c))^2*
        ((Real.sqrt (norm d))^2)^3/81 := by
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sq_sqrt hcN,Real.sq_sqrt hdN]
    _ = _ := by ring

/-- DR v3 (5.17), with the unnormalized theta coefficient restored. -/
theorem cubicThetaTau_primary_conj {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    star (cubicThetaTau (lambdaE*c*d^3)) =
      ((3^(5/2:ℝ)*Real.sqrt (norm d):ℝ):ℂ)*gauss c := by
  have hcN : 0 < Real.sqrt (norm c) := Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hc))
  have hdN : 0 < norm d := norm_pos_of_ne_zero (primary_ne_zero hd)
  have hp : (3:ℝ)^(5/2:ℝ) = 9*Real.sqrt 3 := by
    rw [show (5/2:ℝ) = 2+1/2 by norm_num,Real.rpow_add (by norm_num : (0:ℝ) < 3),
      Real.rpow_two,←Real.sqrt_eq_rpow]
    norm_num
  have ha : ‖cubicThetaFrequency (lambdaE*c*d^3)‖*
      (81/(Real.sqrt (norm c)*norm d)) = 3^(5/2:ℝ)*Real.sqrt (norm d) := by
    rw [cubicThetaFrequency_primary_norm c d,hp]
    field_simp
    have hdS := Real.sq_sqrt hdN.le
    nlinarith [sq_nonneg (Real.sqrt (norm d))]
  rw [cubicThetaTau,star_mul,cubicThetaArithmeticCoefficient_primary_conj hc hd hs]
  simp only [Complex.star_def,Complex.conj_ofReal]
  calc
    _ = ((‖cubicThetaFrequency (lambdaE*c*d^3)‖*
        (81/(Real.sqrt (norm c)*norm d)):ℝ):ℂ)*gauss c := by push_cast; ring
    _ = _ := by rw [ha]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSievePhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The additive character that detects the primary cubic theta support.
It is computed from the actual lambda^-4 frequency lattice. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaSievePhase_add (m n : Eisenstein) :
    cubicThetaSievePhase (m+n) = cubicThetaSievePhase m*cubicThetaSievePhase n := by
  have he : tracePair (cubicThetaFrequency (m+n)) omega =
      tracePair (cubicThetaFrequency m) omega+tracePair (cubicThetaFrequency n) omega := by
    simp only [tracePair,cubicThetaFrequency,Subalgebra.coe_add,add_div,add_mul,Complex.add_re]
    ring
  simp only [cubicThetaSievePhase,he,AddChar.map_add_eq_mul,Circle.coe_mul]

lemma cubicThetaSievePhase_neg (n : Eisenstein) :
    cubicThetaSievePhase (-n) = star (cubicThetaSievePhase n) := by
  have he : tracePair (cubicThetaFrequency (-n)) omega =
      -tracePair (cubicThetaFrequency n) omega := by
    simp only [tracePair,cubicThetaFrequency,Subalgebra.coe_neg,neg_div,neg_mul,Complex.neg_re]
    ring
  simp only [cubicThetaSievePhase,he,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj,Complex.star_def]

lemma cubicThetaSievePhase_ramified (n : Eisenstein) :
    cubicThetaSievePhase (lambdaE^3*n) = 1 := by
  have he : tracePair (cubicThetaFrequency (lambdaE^3*n)) omega =
      tracePair ((n*omegaE:Eisenstein):ℂ) (1/traceLambda) := by
    unfold tracePair cubicThetaFrequency
    congr 2
    push_cast
    rw [lambdaE_coe]
    field_simp
    rfl
  unfold cubicThetaSievePhase
  rw [he,tracePhase_div_lambda_one]

lemma cubicThetaSievePhase_lambda : cubicThetaSievePhase lambdaE = omega^2 := by
  have h4 : traceLambda^4 = 9 := by
    have h2 : traceLambda^2 = -3 := by
      have h := congrArg (fun x : Eisenstein => (x:ℂ)) lambdaE_sq
      push_cast at h
      exact h
    calc
      _ = (traceLambda^2)^2 := by ring
      _ = 9 := by rw [h2]; norm_num
  have ht : tracePair (cubicThetaFrequency lambdaE) omega = -(1/3:ℝ) := by
    unfold tracePair cubicThetaFrequency
    rw [lambdaE_coe,h4,traceLambda_eq]
    norm_num [Complex.mul_re,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im,
      omega_re,omega_im]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hw : (Real.fourierChar (1/3:ℝ):ℂ) = omega := by
    rw [Real.fourierChar_apply]
    unfold omega
    congr 1
    push_cast
    ring
  simp only [cubicThetaSievePhase,ht,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj,hw]
  exact star_omega

lemma cubicThetaSievePhase_primary {a : Eisenstein} (ha : primary a) :
    cubicThetaSievePhase (lambdaE*a) = omega^2 := by
  obtain ⟨k,hk⟩ := ha
  have hn : lambdaE*a = lambdaE+lambdaE^3*(-k) := by
    linear_combination lambdaE*hk + k*lambdaE*lambdaE_sq
  rw [hn,cubicThetaSievePhase_add,cubicThetaSievePhase_ramified,mul_one,
    cubicThetaSievePhase_lambda]

lemma cubicThetaSievePhase_negative_primary {a : Eisenstein} (ha : primary a) :
    cubicThetaSievePhase (-(lambdaE*a)) = omega := by
  rw [cubicThetaSievePhase_neg,cubicThetaSievePhase_primary ha,star_pow,star_omega]
  calc
    _ = omega^3*omega := by ring
    _ = omega := by rw [omega_cube,one_mul]

/-- Every supported coefficient of ramified order at least three has the
trivial detector phase. -/
lemma cubicThetaSievePhase_high {n : Eisenstein} (R : CubicThetaCoordinates n)
    (hk : 3 ≤ R.order) : cubicThetaSievePhase n = 1 := by
  have hn : n = lambdaE^3*((R.unit:Eisenstein)*lambdaE^(R.order-3)*
      (R.squarefreePart*R.cubePart^3)) := by
    calc
      n = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
      _ = _ := by
        have he : R.order = 3+(R.order-3) := by omega
        conv_lhs => rw [he,pow_add]
        ring
  rw [hn,cubicThetaSievePhase_ramified]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSieveSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact primary coefficient selector of DR v3 (5.17)--(5.18). -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimarySupport_coordinates {n : Eisenstein} (R : CubicThetaCoordinates n) :
    cubicThetaPrimarySupport n ↔ R.order = 1 ∧ (R.unit:Eisenstein) = 1 := by
  constructor
  · rintro ⟨S,hS⟩
    cases S.unique R
    exact hS
  · exact fun h => ⟨R,h⟩

lemma cubicThetaRootProjector_one : cubicThetaRootProjector 1 = 0 := by
  unfold cubicThetaRootProjector
  linear_combination (1/3:ℂ)*omega_quadratic

lemma cubicThetaRootProjector_omega : cubicThetaRootProjector omega = 0 := by
  unfold cubicThetaRootProjector
  have h4 : omega^4 = omega := by
    calc
      _ = omega^3*omega := by ring
      _ = _ := by rw [omega_cube,one_mul]
  have he : omega^2*omega^2 = omega^4 := by ring
  rw [he,h4]
  linear_combination (1/3:ℂ)*omega_quadratic

lemma cubicThetaRootProjector_omega_sq : cubicThetaRootProjector (omega^2) = 1 := by
  unfold cubicThetaRootProjector
  have h3 : omega*(omega^2) = 1 := by rw [←pow_succ',omega_cube]
  have h6 : omega^2*(omega^2)^2 = 1 := by
    calc
      _ = (omega^3)^2 := by ring
      _ = _ := by rw [omega_cube]; norm_num
  rw [h3,h6]
  norm_num

lemma CubicThetaCoordinates.primary_product {n : Eisenstein} (R : CubicThetaCoordinates n) :
    primary (R.squarefreePart*R.cubePart^3) := by
  have hp : primary (R.cubePart^3) := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
      primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary)
  exact primary_mul R.squarefree_primary hp

lemma cubicThetaRootProjector_coefficient {n : Eisenstein} (R : CubicThetaCoordinates n) :
    cubicThetaRootProjector (cubicThetaSievePhase n)*star R.coefficient =
      if cubicThetaPrimarySupport n then star R.coefficient else 0 := by
  rw [cubicThetaPrimarySupport_coordinates R]
  by_cases hA : R.order % 3 = 0 ∧ 3 ≤ R.order
  · have hn : ¬(R.order = 1 ∧ (R.unit:Eisenstein) = 1) := by omega
    rw [ite_eq_right hn,cubicThetaSievePhase_high R hA.2,cubicThetaRootProjector_one,zero_mul]
  · by_cases hB : R.order % 3 = 1 ∧ ((R.unit:Eisenstein) = 1 ∨ (R.unit:Eisenstein) = -1)
    · by_cases hk : R.order = 1
      · rcases hB.2 with hu | hu
        · have hn : n = lambdaE*(R.squarefreePart*R.cubePart^3) := by
            calc
              n = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
              _ = _ := by rw [hk,hu,pow_one,one_mul]
          have hp : cubicThetaSievePhase n = omega^2 := by
            rw [hn]
            exact cubicThetaSievePhase_primary R.primary_product
          rw [ite_eq_left ⟨hk,hu⟩,hp,cubicThetaRootProjector_omega_sq,one_mul]
        · have hu' : (R.unit:Eisenstein) ≠ 1 := by
            intro he
            have hc : (1:Eisenstein) ≠ -1 := by norm_num
            exact hc (he.symm.trans hu)
          have hn : n = -(lambdaE*(R.squarefreePart*R.cubePart^3)) := by
            calc
              n = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
              _ = _ := by rw [hk,hu,pow_one]; ring
          have hp : cubicThetaSievePhase n = omega := by
            rw [hn]
            exact cubicThetaSievePhase_negative_primary R.primary_product
          rw [ite_eq_right (by simp [hu']),hp,cubicThetaRootProjector_omega,zero_mul]
      · have hh : 3 ≤ R.order := by omega
        rw [ite_eq_right (by simp [hk]),cubicThetaSievePhase_high R hh,
          cubicThetaRootProjector_one,zero_mul]
    · have he : R.coefficient = 0 := by
        simp only [CubicThetaCoordinates.coefficient,ite_eq_right hA,ite_eq_right hB]
      rw [he,star_zero,mul_zero]
      split_ifs <;> rfl

/-- Multiplying the actual conjugate theta coefficient by the finite
third-root projector cuts it down to precisely the source set S. -/
theorem cubicThetaRootProjector_arithmetic (n : Eisenstein) :
    cubicThetaRootProjector (cubicThetaSievePhase n)*star (cubicThetaArithmeticCoefficient n) =
      if cubicThetaPrimarySupport n then star (cubicThetaArithmeticCoefficient n) else 0 := by
  by_cases h : Nonempty (CubicThetaCoordinates n)
  · let R := Classical.choice h
    rw [cubicThetaArithmeticCoefficient_formula R]
    exact cubicThetaRootProjector_coefficient R
  · have he : cubicThetaArithmeticCoefficient n = 0 := by
      simp only [cubicThetaArithmeticCoefficient,dite_eq_right h]
    rw [he,star_zero,mul_zero]
    split_ifs <;> rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSieveProjection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The primary cubic Gauss coefficients are the exact finite additive
projection of the conjugate cubic theta expansion. No transformation under
inversion is used in this arithmetic sieving step. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaConjugateCoefficient_norm (n : Eisenstein) :
    ‖cubicThetaConjugateCoefficient n‖ ≤ 81 := by
  simpa only [cubicThetaConjugateCoefficient,norm_star] using cubicThetaArithmeticCoefficient_norm_le n

lemma cubicThetaSelectedCoefficient_norm (n : Eisenstein) :
    ‖cubicThetaSelectedCoefficient n‖ ≤ 81 := by
  unfold cubicThetaSelectedCoefficient
  split_ifs
  · exact cubicThetaConjugateCoefficient_norm n
  · norm_num

lemma cubicThetaSeriesTerm_translate (a : Eisenstein → ℂ) (n : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm a (z+omega) v n =
      cubicThetaSievePhase n*cubicThetaSeriesTerm a z v n := by
  by_cases hn : n = 0
  · simp [cubicThetaSeriesTerm,hn]
  · have he : tracePair (cubicThetaFrequency n) (z+omega) =
        tracePair (cubicThetaFrequency n) z+tracePair (cubicThetaFrequency n) omega := by
      simp only [tracePair,mul_add,Complex.add_re]
    simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,he,
      AddChar.map_add_eq_mul,Circle.coe_mul,cubicThetaSievePhase]
    ring

lemma cubicThetaSeriesTerm_translate_twice (a : Eisenstein → ℂ) (n : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm a (z+2*omega) v n =
      cubicThetaSievePhase n^2*cubicThetaSeriesTerm a z v n := by
  rw [show z+2*omega = (z+omega)+omega by ring,
    cubicThetaSeriesTerm_translate,cubicThetaSeriesTerm_translate]
  ring

lemma cubicThetaSelected_term (n : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm cubicThetaSelectedCoefficient z v n =
      (cubicThetaSeriesTerm cubicThetaConjugateCoefficient z v n+
        omega*cubicThetaSeriesTerm cubicThetaConjugateCoefficient (z+omega) v n+
        omega^2*cubicThetaSeriesTerm cubicThetaConjugateCoefficient (z+2*omega) v n)/3 := by
  rw [cubicThetaSeriesTerm_translate,cubicThetaSeriesTerm_translate_twice]
  by_cases hn : n = 0
  · simp [cubicThetaSeriesTerm,hn]
  · have he : cubicThetaSelectedCoefficient n =
        cubicThetaRootProjector (cubicThetaSievePhase n)*cubicThetaConjugateCoefficient n :=
      (cubicThetaRootProjector_arithmetic n).symm
    simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,he,cubicThetaRootProjector]
    ring

/-- The exact finite translate formula for the series supported on S. -/
theorem cubicThetaSelected_projection (z : ℂ) {v : ℝ} (hv : 0 < v) :
    cubicThetaNonconstant cubicThetaSelectedCoefficient (z,v) =
      (cubicThetaNonconstant cubicThetaConjugateCoefficient (z,v)+
        omega*cubicThetaNonconstant cubicThetaConjugateCoefficient (z+omega,v)+
        omega^2*cubicThetaNonconstant cubicThetaConjugateCoefficient (z+2*omega,v))/3 := by
  have hs (w : ℂ) : Summable (cubicThetaSeriesTerm cubicThetaConjugateCoefficient w v) :=
    cubicThetaSeries_summable (by norm_num : (0:ℝ) ≤ 81)
      (fun n hn => (cubicThetaConjugateCoefficient_norm n).trans
        (le_mul_of_one_le_right (by norm_num) (one_le_norm hn))) hv w
  unfold cubicThetaNonconstant
  calc
    _ = ∑' n : Eisenstein,
        (cubicThetaSeriesTerm cubicThetaConjugateCoefficient z v n+
          omega*cubicThetaSeriesTerm cubicThetaConjugateCoefficient (z+omega) v n+
          omega^2*cubicThetaSeriesTerm cubicThetaConjugateCoefficient (z+2*omega) v n)/3 :=
      tsum_congr (fun n => cubicThetaSelected_term n z v)
    _ = _ := by
      rw [tsum_div_const,((hs z).add ((hs (z+omega)).mul_left omega)).tsum_add
        ((hs (z+2*omega)).mul_left (omega^2)),
        (hs z).tsum_add ((hs (z+omega)).mul_left omega),tsum_mul_left,tsum_mul_left]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConjugateProjection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite projection expressed in the original conjugate theta
function, including cancellation of its constant term. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaWhittaker_star (v : ℝ) : star (cubicThetaWhittaker v) = cubicThetaWhittaker v := by
  have he : cubicThetaWhittaker v = ((v/2*cubicBesselKernel ((2*Real.pi*v)^2):ℝ):ℂ) := by
    simp only [cubicThetaWhittaker,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  rw [he]
  exact Complex.conj_ofReal _

lemma cubicThetaSeriesTerm_star_reflect (a : Eisenstein → ℂ) (n : Eisenstein) (z : ℂ) (v : ℝ) :
    star (cubicThetaSeriesTerm a (-z) v n) =
      cubicThetaSeriesTerm (fun n => star (a n)) z v n := by
  by_cases hn : n = 0
  · simp [cubicThetaSeriesTerm,hn]
  · have he : tracePair (cubicThetaFrequency n) (-z) =
        -tracePair (cubicThetaFrequency n) z := by
      simp only [tracePair,mul_neg,Complex.neg_re,mul_neg]
    simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,star_mul,cubicThetaWhittaker_star,he,
      AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
    change _ = _
    simp only [←Complex.star_def,star_star]
    ring

lemma cubicThetaNonconstant_star_reflect (a : Eisenstein → ℂ) (z : ℂ) (v : ℝ) :
    star (cubicThetaNonconstant a (-z,v)) =
      cubicThetaNonconstant (fun n => star (a n)) (z,v) := by
  unfold cubicThetaNonconstant
  rw [tsum_star]
  exact tsum_congr (fun n => cubicThetaSeriesTerm_star_reflect a n z v)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusSlices
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier coefficients of L2 cusp slices. The finite Bessel bounds and
Parseval identity justify the square-summable family of radial L2 modes. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CubicFirstMoment

local instance instCountableSubtypeComplexMemSubalgebraIntEisenstein : Countable Eisenstein := cubicThetaFourierIndex.injective.countable

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBaseScalarNonzero
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual common nonconstant coefficient is nonzero. Otherwise
global automorphy would force a pure height power to be invariant. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaArithmeticBaseScalar_ne_zero : cubicThetaArithmeticBaseScalar≠0 := by
  intro hB
  let p : CubicThetaPoint := ⟨(0,1),by norm_num⟩
  let g₀ : SL(2,Eisenstein) := ⟨!![1,0;3,1],by simp [Matrix.det_fin_two]⟩
  have hg : g₀∈cubicThetaPrincipalGroup :=
    (cubicThetaPrincipalGroup_mem_iff g₀).mpr
      ⟨primary_one,dvd_zero _,dvd_refl _,primary_one⟩
  let g : cubicThetaPrincipalGroup := ⟨g₀,hg⟩
  have hp : (g • p).val.2=(1/10:ℝ) := by
    change (cubicThetaMobius (cubicThetaPrincipalComplex g) (0,1)).2=(1/10:ℝ)
    norm_num [cubicThetaMobius,cubicThetaMobiusDenominator,
      cubicThetaPrincipalComplex_apply,g,g₀]
    change (1+Complex.normSq (3:ℂ))⁻¹=(1/10:ℝ)
    norm_num [Complex.normSq_apply]
  have hC : 0 < cubicThetaConstant := by unfold cubicThetaConstant; positivity
  have hnorm (q : CubicThetaPoint) :
      ‖cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar q.val‖=
        cubicThetaConstant*q.val.2^(2/3:ℝ) := by
    rw [cubicThetaArithmeticModel,hB,zero_mul,add_zero,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (mul_pos hC (Real.rpow_pos_of_pos q.property _))]
  have he := congrArg (fun z : ℂ => ‖z‖) (cubicThetaArithmeticModel_automorphy g p)
  rw [norm_mul,cubicThetaKubotaValue_norm,one_mul,hnorm,hnorm,hp] at he
  change cubicThetaConstant*(1/10:ℝ)^(2/3:ℝ)=cubicThetaConstant*1^(2/3:ℝ) at he
  have hlt : (1/10:ℝ)^(2/3:ℝ)<1 := by
    simpa using Real.rpow_lt_rpow (by norm_num : (0:ℝ)≤1/10)
      (by norm_num : (1/10:ℝ)<1) (by norm_num : (0:ℝ)<2/3)
  rw [Real.one_rpow] at he
  have he' := (mul_left_cancel₀ hC.ne' he)
  exact (ne_of_lt hlt) he'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNormalizedSeries
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the actual automorphic function by its nonzero Fourier
coefficient. Its constant coefficient is retained explicitly. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaNormalizedSeriesSection_apply (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val p=
      cubicThetaSeriesConstant*((p.val.2^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaArithmeticCoefficient p.val := by
  change cubicThetaArithmeticBaseScalar⁻¹*
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val=_
  unfold cubicThetaArithmeticModel cubicThetaSeriesConstant
  push_cast
  field_simp [cubicThetaArithmeticBaseScalar_ne_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute lattice and kernel masses for exchanging the theta sum with
its Mellin integral on the initial right half-plane. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicWhittaker_norm_integral_scale (u c : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ v in Ioi (0:ℝ), ‖(v:ℂ)^(u-1)*(c*cubicThetaWhittaker (r*v))‖) =
      ‖c‖*r^(-u.re)*cubicWhittakerNormMass u.re := by
  calc
    _ = ‖c‖*(∫ v in Ioi (0:ℝ), v^(u.re-1)*‖cubicThetaWhittaker (r*v)‖) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
      simp only [Complex.sub_re,Complex.one_re]
      ring
    _ = _ := by rw [cubicWhittaker_norm_mass_scale u.re hr]; unfold cubicWhittakerNormMass; ring

/-- Bounded normalized coefficients give an absolutely convergent initial
Dirichlet series for Re u > 2. -/
lemma cubicTheta_mellin_weight_summable {a : Eisenstein → ℂ} {C σ : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C) (hσ : 2 < σ) :
    Summable (fun n : Eisenstein => if n = 0 then (0:ℝ) else
      ‖a n‖*‖cubicThetaFrequency n‖^(-σ)) := by
  have hs : Summable (fun n : Eisenstein =>
      (C*81^(σ/2))*norm n^(-(σ/2))) :=
    (summable_eisenstein_norm_rpow (by linarith : 1 < σ/2)).mul_left _
  apply hs.of_nonneg_of_le
  · intro n
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (_root_.norm_nonneg _) (Real.rpow_nonneg (_root_.norm_nonneg _) _)
  · intro n
    by_cases hn : n = 0
    · rw [ite_eq_left hn]
      exact mul_nonneg (mul_nonneg hC (by positivity)) (Real.rpow_nonneg (norm_nonneg _) _)
    · rw [ite_eq_right hn,cubicThetaFrequency_rpow hn]
      have he1 : -(-σ)/2 = σ/2 := by ring
      have he2 : -σ/2 = -(σ/2) := by ring
      rw [he1,he2]
      calc
        _ ≤ C*(81^(σ/2)*norm n^(-(σ/2))) :=
          mul_le_mul_of_nonneg_right (ha n) (by positivity [norm_nonneg n])
        _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact frequency powers in the fixed-angular theta Mellin transform. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAngularCoefficient_norm {a : Eisenstein → ℂ} (ℓ : ℤ)
    {n : Eisenstein} (hn : n ≠ 0) :
    ‖cubicThetaAngularCoefficient a ℓ n‖ = ‖cubicThetaFrequency n‖^ℓ.natAbs*‖a n‖ := by
  simp only [cubicThetaAngularCoefficient,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _),norm_theta hn,mul_one]

lemma cubicThetaAngular_real_power {r : ℝ} (hr : 0 < r) (k : ℕ) (s : ℂ) :
    r^k*r^(-(2*s+(k:ℂ)-1).re) = r^(-(2*s-1).re) := by
  rw [←Real.rpow_natCast,←Real.rpow_add hr]
  congr 1
  simp only [Complex.add_re,Complex.sub_re,Complex.natCast_re]
  ring

lemma cubicThetaAngular_complex_power {r : ℝ} (hr : 0 < r) (k : ℕ) (s : ℂ) :
    (r:ℂ)^k*(r:ℂ)^(-(2*s+(k:ℂ)-1)) = (r:ℂ)^(-(2*s-1)) := by
  have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  rw [←Complex.cpow_natCast,←Complex.cpow_add _ _ hrC]
  congr 1
  ring

/-- The growing derivative factor exactly cancels the shifted Mellin
exponent; the remaining coefficient mass is the original bounded one. -/
lemma cubicThetaAngular_weight {a : Eisenstein → ℂ} (ℓ : ℤ)
    {n : Eisenstein} (hn : n ≠ 0) (s : ℂ) :
    ‖cubicThetaAngularCoefficient a ℓ n‖*
      ‖cubicThetaFrequency n‖^(-(2*s+(ℓ.natAbs:ℂ)-1).re) =
        ‖a n‖*‖cubicThetaFrequency n‖^(-(2*s-1).re) := by
  rw [cubicThetaAngularCoefficient_norm ℓ hn]
  calc
    _ = ‖a n‖*(‖cubicThetaFrequency n‖^ℓ.natAbs*
        ‖cubicThetaFrequency n‖^(-(2*s+(ℓ.natAbs:ℂ)-1).re)) := by ring
    _ = _ := by rw [cubicThetaAngular_real_power (cubicThetaFrequency_pos hn)]

lemma cubicThetaAngular_dirichlet_term {a : Eisenstein → ℂ} (ℓ : ℤ)
    {n : Eisenstein} (hn : n ≠ 0) (s : ℂ) :
    cubicThetaAngularCoefficient a ℓ n*
      (‖cubicThetaFrequency n‖:ℂ)^(-(2*s+(ℓ.natAbs:ℂ)-1)) =
        theta ℓ n*a n*(‖cubicThetaFrequency n‖:ℂ)^(-(2*s-1)) := by
  unfold cubicThetaAngularCoefficient
  calc
    _ = (theta ℓ n*a n)*((‖cubicThetaFrequency n‖:ℂ)^ℓ.natAbs*
        (‖cubicThetaFrequency n‖:ℂ)^(-(2*s+(ℓ.natAbs:ℂ)-1))) := by ring
    _ = _ := by rw [cubicThetaAngular_complex_power (cubicThetaFrequency_pos hn)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed angular multipliers are precisely powers of the actual
complex Fourier frequency and its conjugate. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_div_nine (n : Eisenstein) :
    cubicThetaFrequency n=(n:ℂ)/9 := by
  have hs : traceLambda^2=(-3:ℂ) := by
    have he := congrArg (fun n : Eisenstein => (n:ℂ)) lambdaE_sq
    push_cast at he
    rw [lambdaE_coe] at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
  have h4 : traceLambda^4=(9:ℂ) := by
    calc
      _ = (traceLambda^2)^2 := by ring
      _ = _ := by rw [hs]; norm_num
  simp only [cubicThetaFrequency,h4]

lemma cubicThetaFrequency_phase (n : Eisenstein) :
    (‖cubicThetaFrequency n‖:ℂ)*((n:ℂ)/(‖(n:ℂ)‖:ℂ))=cubicThetaFrequency n := by
  simp only [cubicThetaFrequency_div_nine]
  by_cases hn : (n:ℂ)=0
  · simp [hn]
  · have hnorm : (‖(n:ℂ)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hn)
    simp only [norm_div,Complex.norm_ofNat]
    push_cast
    field_simp [hnorm]

lemma cubicThetaFrequency_conj_phase (n : Eisenstein) :
    (‖cubicThetaFrequency n‖:ℂ)*((n:ℂ)/(‖(n:ℂ)‖:ℂ))⁻¹=
      star (cubicThetaFrequency n) := by
  by_cases hn : (n:ℂ)=0
  · simp [cubicThetaFrequency_div_nine,hn]
  have hnorm : (‖(n:ℂ)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hn)
  have hs : (n:ℂ)*star (n:ℂ)=(‖(n:ℂ)‖:ℂ)^2 := by
    simpa only [Complex.star_def] using Complex.mul_conj' (n:ℂ)
  simp only [cubicThetaFrequency_div_nine,norm_div,Complex.norm_ofNat,
    star_div₀,star_ofNat,inv_div]
  push_cast
  field_simp
  exact hs.symm

lemma cubicThetaAngularCoefficient_nat (a : Eisenstein → ℂ) (k : ℕ) (n : Eisenstein) :
    cubicThetaAngularCoefficient a (k:ℤ) n=cubicThetaFrequency n^k*a n := by
  simp only [cubicThetaAngularCoefficient,Int.natAbs_natCast,theta,zpow_natCast]
  rw [←mul_pow,cubicThetaFrequency_phase]

lemma cubicThetaAngularCoefficient_neg_nat (a : Eisenstein → ℂ) (k : ℕ) (n : Eisenstein) :
    cubicThetaAngularCoefficient a (-(k:ℤ)) n=star (cubicThetaFrequency n)^k*a n := by
  simp only [cubicThetaAngularCoefficient,Int.natAbs_neg,Int.natAbs_natCast,theta,
    zpow_neg,zpow_natCast,←inv_pow]
  rw [←mul_pow,cubicThetaFrequency_conj_phase]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedLattice
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the translated-cusp coefficients on the common lambda^-4 lattice.
The congruence restriction forces the apparent larger lattice to collapse. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShiftedLatticeCoefficient_bound (n : ℤ) (k : Eisenstein) :
    ‖cubicThetaShiftedLatticeCoefficient n k‖≤243 := by
  unfold cubicThetaShiftedLatticeCoefficient
  split_ifs
  · rw [norm_mul,Complex.norm_ofNat]
    calc
      _ ≤ 3*81 := mul_le_mul_of_nonneg_left (cubicThetaArithmeticCoefficient_norm_le _) (by norm_num)
      _ = _ := by norm_num
  · norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaActualCuspCoefficients
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal constant and nonconstant coefficients of the three actual
cusp types, and their conjugates on the common frequency lattice. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaCuspExpansion_coefficients (n : ℤ) (p : ℂ×ℝ) :
    cubicThetaCuspExpansion n p=cubicThetaActualCuspConstant n*((p.2^(2/3:ℝ):ℝ):ℂ)+
      cubicThetaNonconstant (cubicThetaActualCuspCoefficient n) p := by
  by_cases hn : (3:ℤ) ∣ n <;>
    simp [cubicThetaCuspExpansion,cubicThetaActualCuspConstant,cubicThetaActualCuspCoefficient,hn]

lemma cubicThetaActualCuspCoefficient_bound (n : ℤ) (k : Eisenstein) :
    ‖cubicThetaActualCuspCoefficient n k‖≤243 := by
  unfold cubicThetaActualCuspCoefficient
  split_ifs
  · exact (cubicThetaArithmeticCoefficient_norm_le k).trans (by norm_num)
  · exact cubicThetaShiftedLatticeCoefficient_bound n k

lemma cubicThetaSeriesTerm_reflect (a : Eisenstein→ℂ) (n : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm a (-z) v (-n)=
      cubicThetaSeriesTerm (fun k => a (-k)) z v n := by
  by_cases hn : n=0
  · simp [cubicThetaSeriesTerm,hn]
  · have hf : cubicThetaFrequency (-n)= -cubicThetaFrequency n := by
      simp only [cubicThetaFrequency,Subalgebra.coe_neg,neg_div]
    have ht : tracePair (-cubicThetaFrequency n) (-z)=tracePair (cubicThetaFrequency n) z := by
      simp only [tracePair,neg_mul_neg]
    simp only [cubicThetaSeriesTerm,ite_eq_right hn,ite_eq_right (neg_ne_zero.mpr hn),hf,
      norm_neg,ht]

lemma cubicThetaNonconstant_reflect (a : Eisenstein→ℂ) (z : ℂ) (v : ℝ) :
    cubicThetaNonconstant a (-z,v)=cubicThetaNonconstant (fun k => a (-k)) (z,v) := by
  unfold cubicThetaNonconstant
  rw [←(Equiv.neg Eisenstein).tsum_eq (fun k => cubicThetaSeriesTerm a (-z) v k)]
  exact tsum_congr (fun k => cubicThetaSeriesTerm_reflect a k z v)

lemma cubicThetaNonconstant_star (a : Eisenstein→ℂ) (z : ℂ) (v : ℝ) :
    star (cubicThetaNonconstant a (z,v))=
      cubicThetaNonconstant (fun k => star (a (-k))) (z,v) := by
  have he := cubicThetaNonconstant_star_reflect a (-z) v
  rw [neg_neg] at he
  exact he.trans (cubicThetaNonconstant_reflect (fun k => star (a k)) z v)

lemma cubicThetaNormalizedSeries_conjugate (p : CubicThetaPoint) :
    star (cubicThetaNormalizedSeriesSection.val p)=
      star cubicThetaSeriesConstant*((p.val.2^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaConjugateCoefficient p.val := by
  rw [cubicThetaNormalizedSeriesSection_apply,star_add,star_mul]
  have he := cubicThetaNonconstant_star_reflect cubicThetaArithmeticCoefficient p.val.1 p.val.2
  rw [cubicThetaArithmetic_even] at he
  rw [he]
  simp only [Complex.star_def,Complex.conj_ofReal,mul_comm]
  rfl

lemma cubicThetaCuspExpansion_conjugate (n : ℤ) (p : ℂ×ℝ) :
    star (cubicThetaCuspExpansion n p)=
      star (cubicThetaActualCuspConstant n)*((p.2^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant (fun k => star (cubicThetaActualCuspCoefficient n (-k))) p := by
  rcases p with ⟨z,v⟩
  rw [cubicThetaCuspExpansion_coefficients,star_add,star_mul,cubicThetaNonconstant_star]
  simp only [Complex.star_def,Complex.conj_ofReal,mul_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaActualProjection
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual primary projector and its finite transformed cusp family. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaNormalizedSeries_translation_conjugate (b : Eisenstein) (p : CubicThetaPoint) :
    star (cubicThetaNormalizedSeriesSection.val (cubicThetaFullTranslation b • p))=
      star cubicThetaSeriesConstant*((p.val.2^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaConjugateCoefficient (p.val.1+(b:ℂ),p.val.2) := by
  rw [cubicThetaNormalizedSeries_conjugate]
  have he : (cubicThetaFullTranslation b • p).val=(p.val.1+(b:ℂ),p.val.2) := by
    rw [cubicThetaFullPointAction_apply,cubicThetaFullTranslation_complex,cubicThetaMobius_translation]
  rw [he]

lemma cubicThetaNormalizedPrimaryProjection_series (p : CubicThetaPoint) :
    cubicThetaNormalizedPrimaryProjection p=
      cubicThetaNonconstant cubicThetaSelectedCoefficient p.val := by
  unfold cubicThetaNormalizedPrimaryProjection
  rw [cubicThetaNormalizedSeries_conjugate,
    cubicThetaNormalizedSeries_translation_conjugate,
    cubicThetaNormalizedSeries_translation_conjugate]
  have he := cubicThetaSelected_projection p.val.1 p.property
  change _=cubicThetaNonconstant cubicThetaSelectedCoefficient (p.val.1,p.val.2)
  rw [he]
  have htwo : ((2*omegaE:Eisenstein):ℂ)=2*omega := by push_cast; rfl
  rw [htwo,show (omegaE:ℂ)=omega from rfl]
  change _=((cubicThetaNonconstant cubicThetaConjugateCoefficient (p.val.1,p.val.2)+
    omega*cubicThetaNonconstant cubicThetaConjugateCoefficient (p.val.1+omega,p.val.2)+
    omega^2*cubicThetaNonconstant cubicThetaConjugateCoefficient (p.val.1+2*omega,p.val.2))/3)
  linear_combination star cubicThetaSeriesConstant*((p.val.2^(2/3:ℝ):ℝ):ℂ)/3*omega_quadratic

theorem cubicThetaNormalizedPrimaryProjection_cusps (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (p : CubicThetaPoint) :
    cubicThetaNonconstant cubicThetaSelectedCoefficient (g • p).val=
      (∑ j : Fin 3, omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j*
        cubicThetaCuspExpansion (cubicThetaProjectedCuspType g j)
          (cubicThetaFullTranslation (g 1 1) • p).val))/3 := by
  rw [←cubicThetaNormalizedPrimaryProjection_series]
  have hs : (∑ j : Fin 3, omega^j.val*star (cubicThetaNormalizedSeriesSection.val
      (cubicThetaFullTranslation ((j.val:Eisenstein)*omegaE) • (g • p))))/3=
      cubicThetaNormalizedPrimaryProjection (g • p) := by
    rw [Fin.sum_univ_three]
    have hz : cubicThetaFullTranslation 0=1 := by
      apply Subtype.ext
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> rfl
    simp only [Fin.val_zero,Fin.val_one,Fin.val_two,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,
      zero_mul,one_mul,pow_zero,pow_one,hz,one_smul,cubicThetaNormalizedPrimaryProjection]
  rw [←hs]
  simp_rw [cubicThetaProjectedCusp_identity g hc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularConvergence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence of the fixed-angular frequency derivatives.
An explicit summable lattice majorant absorbs every fixed derivative order. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_inverse_pow {n : Eisenstein} (hn : n ≠ 0) (k : ℕ) :
    ‖cubicThetaFrequency n‖^(-(k:ℝ)) ≤ (9:ℝ)^k := by
  calc
    _ ≤ (1/9:ℝ)^(-(k:ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num)
      (cubicThetaFrequency_lower hn) (neg_nonpos.mpr (Nat.cast_nonneg k))
    _ = (9:ℝ)^k := by
      rw [Real.rpow_neg_eq_inv_rpow]
      norm_num only [one_div,inv_inv]
      rw [Real.rpow_natCast]

lemma cubicThetaAngular_kernel_bound (k : ℕ) {n : Eisenstein} (hn : n ≠ 0)
    {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaFrequency n‖^k*‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖ ≤
      (cubicWhittakerPowerConstant (k+3)*(9:ℝ)^k*81^(7/3:ℝ))*
        v^(4/3-2*((k:ℝ)+3))*norm n^(-7/3:ℝ) := by
  have hr := cubicThetaFrequency_pos hn
  have hK := (cubicWhittakerPowerConstant_pos (by omega : 1 ≤ k+3)).le
  have hw := cubicThetaWhittaker_power_bound (k+3) (by omega) (mul_pos hr hv)
  simp only [Nat.cast_add,Nat.cast_ofNat] at hw
  rw [Real.mul_rpow hr.le hv.le] at hw
  have hp : ‖cubicThetaFrequency n‖^k*‖cubicThetaFrequency n‖^(4/3-2*((k:ℝ)+3)) =
      ‖cubicThetaFrequency n‖^(-(k:ℝ))*‖cubicThetaFrequency n‖^(-14/3:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hr,←Real.rpow_add hr]
    congr 1
    ring
  calc
    _ ≤ ‖cubicThetaFrequency n‖^k*(cubicWhittakerPowerConstant (k+3)*
        (‖cubicThetaFrequency n‖^(4/3-2*((k:ℝ)+3))*v^(4/3-2*((k:ℝ)+3)))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = cubicWhittakerPowerConstant (k+3)*v^(4/3-2*((k:ℝ)+3))*
        (‖cubicThetaFrequency n‖^(-(k:ℝ))*‖cubicThetaFrequency n‖^(-14/3:ℝ)) := by
      calc
        _ = cubicWhittakerPowerConstant (k+3)*v^(4/3-2*((k:ℝ)+3))*
            (‖cubicThetaFrequency n‖^k*‖cubicThetaFrequency n‖^(4/3-2*((k:ℝ)+3))) := by ring
        _ = _ := by rw [hp]
    _ ≤ cubicWhittakerPowerConstant (k+3)*v^(4/3-2*((k:ℝ)+3))*
        ((9:ℝ)^k*‖cubicThetaFrequency n‖^(-14/3:ℝ)) := by
      gcongr
      exact cubicThetaFrequency_inverse_pow hn k
    _ = _ := by rw [cubicThetaFrequency_power hn]; ring

lemma cubicThetaAngular_term_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (hv : 0 < v) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v n‖ ≤
      (C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*
        v^(4/3-2*((ℓ.natAbs:ℝ)+3)))*norm n^(-4/3:ℝ) := by
  have hK := (cubicWhittakerPowerConstant_pos (by omega : 1 ≤ ℓ.natAbs+3)).le
  by_cases hn : n = 0
  · simp only [cubicThetaSeriesTerm,hn,ite_true, if_true,norm_zero]
    norm_num [norm]
  · have hN := norm_pos_of_ne_zero hn
    simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,norm_mul,Circle.norm_coe,mul_one,
      cubicThetaAngularCoefficient_norm ℓ hn]
    have hp : norm n*norm n^(-7/3:ℝ) = norm n^(-4/3:ℝ) := by
      calc
        _ = norm n^(1:ℝ)*norm n^(-7/3:ℝ) := by rw [Real.rpow_one]
        _ = norm n^(1+(-7/3:ℝ)) := (Real.rpow_add hN _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = ‖a n‖*(‖cubicThetaFrequency n‖^ℓ.natAbs*
          ‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖) := by ring
      _ ≤ (C*norm n)*((cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ))*
          v^(4/3-2*((ℓ.natAbs:ℝ)+3))*norm n^(-7/3:ℝ)) :=
        mul_le_mul (ha n hn) (cubicThetaAngular_kernel_bound ℓ.natAbs hn hv)
          (mul_nonneg (by positivity) (_root_.norm_nonneg _)) (mul_nonneg hC hN.le)
      _ = _ := by
        calc
          _ = (C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*
              v^(4/3-2*((ℓ.natAbs:ℝ)+3)))*(norm n*norm n^(-7/3:ℝ)) := by ring
          _ = _ := by rw [hp]

/-- Every fixed signed angular derivative is an absolutely convergent
Fourier series at each positive height. -/
theorem cubicThetaAngular_summable {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (hv : 0 < v) (z : ℂ) :
    Summable (cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v) := by
  apply ((summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 4/3)).mul_left
    (C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*
      v^(4/3-2*((ℓ.natAbs:ℝ)+3)))).of_norm_bounded
  intro n
  simpa only [neg_div] using cubicThetaAngular_term_bound hC ha ℓ hv z n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locally uniform convergence for the fixed-angular theta expansion. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAngular_continuousOn_strip {a : Eisenstein → ℂ} {C b : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (hb : 0 < b) :
    ContinuousOn (cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ))
      {p : ℂ × ℝ | b < p.2} := by
  let K := C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC
      (cubicWhittakerPowerConstant_pos (by omega : 1 ≤ ℓ.natAbs+3)).le) (by positivity))
      (by positivity)
  have hp : (4/3:ℝ)-2*((ℓ.natAbs:ℝ)+3) ≤ 0 := by
    have hk : (0:ℝ) ≤ ℓ.natAbs := Nat.cast_nonneg _
    linarith
  have hs := (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 4/3)).mul_left
    (K*b^(4/3-2*((ℓ.natAbs:ℝ)+3)))
  apply continuousOn_tsum
    (fun n p h => (cubicThetaSeriesTerm_continuousAt _ n (hb.trans h)).continuousWithinAt) hs
  intro n p h
  change b < p.2 at h
  have hpower : p.2^(4/3-2*((ℓ.natAbs:ℝ)+3)) ≤ b^(4/3-2*((ℓ.natAbs:ℝ)+3)) :=
    Real.rpow_le_rpow_of_nonpos hb h.le hp
  calc
    _ ≤ (K*p.2^(4/3-2*((ℓ.natAbs:ℝ)+3)))*norm n^(-4/3:ℝ) :=
      cubicThetaAngular_term_bound hC ha ℓ (hb.trans h) p.1 n
    _ ≤ _ := by
      simpa only [neg_div] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hK)
          (Real.rpow_nonneg (norm_nonneg n) (-4/3:ℝ))

/-- The fixed signed angular Fourier expansion is a continuous function
at every point of the upper half-space. -/
theorem cubicThetaAngular_continuousAt {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) {p : ℂ × ℝ} (hp : 0 < p.2) :
    ContinuousAt (cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ)) p := by
  have hs := cubicThetaAngular_continuousOn_strip hC ha ℓ
    (show 0 < p.2/2 by positivity)
  have ho : IsOpen {q : ℂ × ℝ | p.2/2 < q.2} := isOpen_lt continuous_const continuous_snd
  exact hs.continuousAt (ho.mem_nhds (by change p.2/2 < p.2; linarith))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularExponential
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential cusp decay survives every fixed angular frequency power. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAngularAbsorption_pos (k : ℕ) : 0 < cubicThetaAngularAbsorption k := by
  unfold cubicThetaAngularAbsorption
  positivity

lemma cubicTheta_frequency_power_exp (k : ℕ) {r v : ℝ} (hr : 1/9 ≤ r) (hv : 1 ≤ v) :
    r^k*Real.exp (-Real.pi*r*v) ≤
      cubicThetaAngularAbsorption k*Real.exp (-(Real.pi/18)*v) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hf := pow_mul_exp_neg_le_factorial k (show 0 ≤ (Real.pi/2)*r by positivity)
  have hfac : r^k*Real.exp (-(Real.pi/2)*r) ≤ cubicThetaAngularAbsorption k := by
    apply (le_div_iff₀ (show 0 < (Real.pi/2)^k by positivity)).mpr
    calc
      _ = ((Real.pi/2)*r)^k*Real.exp (-((Real.pi/2)*r)) := by
        rw [show -(Real.pi/2)*r = -((Real.pi/2)*r) by ring,mul_pow]
        ring
      _ ≤ _ := hf
  have he1 : Real.exp (-(Real.pi/2)*r*v) ≤ Real.exp (-(Real.pi/2)*r) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_left hv (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (le_of_lt (half_pos Real.pi_pos))) hr0.le)
    simpa only [mul_one] using h
  have he2 : Real.exp (-(Real.pi/2)*r*v) ≤ Real.exp (-(Real.pi/18)*v) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hr (show 0 ≤ Real.pi/2*v by positivity)
    first | (convert neg_le_neg h using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((neg_le_neg h).trans (le_of_eq (by ring)))
  calc
    _ = (r^k*Real.exp (-(Real.pi/2)*r*v))*Real.exp (-(Real.pi/2)*r*v) := by
      conv_rhs => rw [mul_assoc,←Real.exp_add]
      congr 2
      ring
    _ ≤ (r^k*Real.exp (-(Real.pi/2)*r))*Real.exp (-(Real.pi/2)*r*v) := by
      gcongr
    _ ≤ cubicThetaAngularAbsorption k*Real.exp (-(Real.pi/18)*v) :=
      mul_le_mul hfac he2 (Real.exp_pos _).le (cubicThetaAngularAbsorption_pos k).le

lemma cubicThetaAngular_kernel_exp_bound (k : ℕ) {n : Eisenstein} (hn : n ≠ 0)
    {v : ℝ} (hv : 1 ≤ v) :
    ‖cubicThetaFrequency n‖^k*‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖ ≤
      (cubicWhittakerMixedConstant*cubicThetaAngularAbsorption k*81^(8/3:ℝ))*
        norm n^(-8/3:ℝ)*Real.exp (-(Real.pi/18)*v) := by
  have hr := cubicThetaFrequency_pos hn
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hD := cubicWhittakerMixedConstant_pos.le
  have hw := cubicThetaWhittaker_mixed_bound (mul_pos hr hv0)
  rw [Real.mul_rpow hr.le hv0.le] at hw
  have hb := cubicTheta_frequency_power_exp k (cubicThetaFrequency_lower hn) hv
  have hvp : v^(-16/3:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv (by norm_num)
  calc
    _ ≤ ‖cubicThetaFrequency n‖^k*(cubicWhittakerMixedConstant*
        (‖cubicThetaFrequency n‖^(-16/3:ℝ)*v^(-16/3:ℝ))*
          Real.exp (-Real.pi*(‖cubicThetaFrequency n‖*v))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = (cubicWhittakerMixedConstant*‖cubicThetaFrequency n‖^(-16/3:ℝ))*v^(-16/3:ℝ)*
        (‖cubicThetaFrequency n‖^k*Real.exp (-Real.pi*‖cubicThetaFrequency n‖*v)) := by
      rw [show -Real.pi*(‖cubicThetaFrequency n‖*v) =
        -Real.pi*‖cubicThetaFrequency n‖*v by ring]
      ring
    _ ≤ (cubicWhittakerMixedConstant*‖cubicThetaFrequency n‖^(-16/3:ℝ))*1*
        (cubicThetaAngularAbsorption k*Real.exp (-(Real.pi/18)*v)) := by
      gcongr
    _ = _ := by
      rw [cubicThetaFrequency_rpow hn]
      norm_num only
      ring

lemma cubicThetaAngular_term_exp_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (hv : 1 ≤ v) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v n‖ ≤
      (C*cubicWhittakerMixedConstant*cubicThetaAngularAbsorption ℓ.natAbs*81^(8/3:ℝ)*
        Real.exp (-(Real.pi/18)*v))*norm n^(-5/3:ℝ) := by
  by_cases hn : n = 0
  · simp [cubicThetaSeriesTerm,hn,norm]
  · have hN := norm_pos_of_ne_zero hn
    simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,norm_mul,Circle.norm_coe,mul_one,
      cubicThetaAngularCoefficient_norm ℓ hn]
    have hp : norm n*norm n^(-8/3:ℝ) = norm n^(-5/3:ℝ) := by
      calc
        _ = norm n^(1:ℝ)*norm n^(-8/3:ℝ) := by rw [Real.rpow_one]
        _ = norm n^(1+(-8/3:ℝ)) := (Real.rpow_add hN _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = ‖a n‖*(‖cubicThetaFrequency n‖^ℓ.natAbs*
          ‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖) := by ring
      _ ≤ (C*norm n)*((cubicWhittakerMixedConstant*cubicThetaAngularAbsorption ℓ.natAbs*81^(8/3:ℝ))*
          norm n^(-8/3:ℝ)*Real.exp (-(Real.pi/18)*v)) :=
        mul_le_mul (ha n hn) (cubicThetaAngular_kernel_exp_bound ℓ.natAbs hn hv)
          (mul_nonneg (by positivity) (_root_.norm_nonneg _)) (mul_nonneg hC hN.le)
      _ = _ := by
        calc
          _ = (C*cubicWhittakerMixedConstant*cubicThetaAngularAbsorption ℓ.natAbs*81^(8/3:ℝ)*
              Real.exp (-(Real.pi/18)*v))*(norm n*norm n^(-8/3:ℝ)) := by ring
          _ = _ := by rw [hp]

/-- Uniform exponential decrease of each fixed angular theta series. -/
theorem cubicThetaAngular_exponential_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (hv : 1 ≤ v) (z : ℂ) :
    ‖cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,v)‖ ≤
      cubicThetaAngularExpConstant C ℓ*Real.exp (-(Real.pi/18)*v) := by
  have hs := cubicThetaAngular_summable hC ha ℓ (zero_lt_one.trans_le hv) z
  have hm := (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 5/3)).mul_left
    (C*cubicWhittakerMixedConstant*cubicThetaAngularAbsorption ℓ.natAbs*81^(8/3:ℝ)*
      Real.exp (-(Real.pi/18)*v))
  calc
    _ ≤ ∑' n : Eisenstein, ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v n‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : Eisenstein, (C*cubicWhittakerMixedConstant*cubicThetaAngularAbsorption ℓ.natAbs*81^(8/3:ℝ)*
        Real.exp (-(Real.pi/18)*v))*norm n^(-5/3:ℝ) :=
      Summable.tsum_le_tsum (cubicThetaAngular_term_exp_bound hC ha ℓ hv z) hs.norm (by
        simpa only [neg_div] using hm)
    _ = _ := by rw [tsum_mul_left]; unfold cubicThetaAngularExpConstant; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLevelReciprocity
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the genuine primary-level theta transformation on a symmetric
height scale, before Mellin integration. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaLevelScale_pos {q : Eisenstein} (hq : primary q) :
    0 < cubicThetaLevelScale q :=
  inv_pos.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hq)))

lemma cubicThetaLevelScale_reciprocal {q : Eisenstein} (hq : primary q)
    {t : ℝ} (ht : 0<t) :
    (norm q*(cubicThetaLevelScale q*t))⁻¹=cubicThetaLevelScale q*t⁻¹ := by
  have hN := norm_pos_of_ne_zero (primary_ne_zero hq)
  have hs := Real.sqrt_pos.mpr hN
  have hs2 := Real.sq_sqrt hN.le
  unfold cubicThetaLevelScale
  field_simp
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact shifted Mellin identity for every fixed angular mode.
Absolute integration is proved using the original bounded coefficient mass. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The frequency derivative and the shifted Mellin exponent cancel before
summation. This is the analytic origin of the shifted Gamma factors. -/
theorem cubicThetaAngular_mellin {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C)
    (ℓ : ℤ) {s : ℂ} (hs : 3/2 < s.re) :
    mellin (fun v : ℝ => cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (0,v))
      (2*s+(ℓ.natAbs:ℂ)-1) =
      mellin cubicThetaWhittaker (2*s+(ℓ.natAbs:ℂ)-1)*
        cubicThetaDirichlet (fun n => theta ℓ n*a n) (2*s-1) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  let u : ℂ := 2*s+(ℓ.natAbs:ℂ)-1
  let F (n : Eisenstein) (v : ℝ) : ℂ :=
    (v:ℂ)^(u-1)*cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) 0 v n
  have hhalf : (1/6:ℝ) < (s+(ℓ.natAbs:ℂ)/2).re := by
    simp only [Complex.add_re,Complex.div_ofNat_re,Complex.natCast_re]
    have hk : (0:ℝ) ≤ ℓ.natAbs := Nat.cast_nonneg _
    linarith
  have heu : 2*(s+(ℓ.natAbs:ℂ)/2)-1 = u := by dsimp [u]; ring
  have hu0 : 2 < (2*s-1).re := by norm_num [Complex.mul_re,Complex.sub_re]; linarith
  have hFi (n : Eisenstein) : IntegrableOn (F n) (Ioi 0) := by
    by_cases hn : n = 0
    · simp [F,cubicThetaSeriesTerm,hn]
    · have h := cubicThetaWhittaker_scaled_mellinConvergent hhalf
        (cubicThetaFrequency_pos hn) (cubicThetaAngularCoefficient a ℓ n)
      rw [heu] at h
      simpa [F,MellinConvergent,cubicThetaSeriesTerm,hn,tracePair] using h
  have hmass (n : Eisenstein) : (∫ v in Ioi (0:ℝ), ‖F n v‖) =
      (if n = 0 then (0:ℝ) else ‖a n‖*‖cubicThetaFrequency n‖^(-(2*s-1).re))*
        cubicWhittakerNormMass u.re := by
    by_cases hn : n = 0
    · simp [F,cubicThetaSeriesTerm,hn]
    · have h := cubicWhittaker_norm_integral_scale u (cubicThetaAngularCoefficient a ℓ n)
        (cubicThetaFrequency_pos hn)
      have h' : (∫ v in Ioi (0:ℝ), ‖F n v‖) =
          ‖cubicThetaAngularCoefficient a ℓ n‖*‖cubicThetaFrequency n‖^(-u.re)*
            cubicWhittakerNormMass u.re := by
        simpa [F,cubicThetaSeriesTerm,hn,tracePair,mul_assoc] using h
      rw [h',ite_eq_right hn]
      dsimp only [u]
      rw [cubicThetaAngular_weight ℓ hn]
  have hsum : Summable (fun n : Eisenstein => ∫ v in Ioi (0:ℝ), ‖F n v‖) := by
    simp_rw [hmass]
    exact (cubicTheta_mellin_weight_summable hC ha hu0).mul_right _
  have hinter := integral_tsum_of_summable_integral_norm hFi hsum
  have hsingle (n : Eisenstein) : (∫ v in Ioi (0:ℝ), F n v) =
      mellin cubicThetaWhittaker u*(if n = 0 then 0 else
        theta ℓ n*a n*(‖cubicThetaFrequency n‖:ℂ)^(-(2*s-1))) := by
    by_cases hn : n = 0
    · simp [F,cubicThetaSeriesTerm,hn]
    · have he : (∫ v in Ioi (0:ℝ), F n v) =
          mellin (fun v : ℝ => cubicThetaAngularCoefficient a ℓ n •
            cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)) u := by
        unfold mellin
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v _
        simp [F,cubicThetaSeriesTerm,hn,tracePair]
      rw [he,mellin_const_smul,mellin_comp_mul_left _ _ (cubicThetaFrequency_pos hn)]
      simp only [hn,ite_false, if_false,smul_eq_mul]
      calc
        _ = mellin cubicThetaWhittaker u*(cubicThetaAngularCoefficient a ℓ n*
            (‖cubicThetaFrequency n‖:ℂ)^(-u)) := by ring
        _ = _ := by dsimp only [u]; rw [cubicThetaAngular_dirichlet_term ℓ hn]
  calc
    _ = ∫ v in Ioi (0:ℝ), ∑' n : Eisenstein, F n v := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      dsimp [F,cubicThetaNonconstant]
      rw [tsum_mul_left]
    _ = ∑' n : Eisenstein, ∫ v in Ioi (0:ℝ), F n v := hinter.symm
    _ = _ := by simp_rw [hsingle]; rw [tsum_mul_left]; rfl

/-- The literal shifted Gamma product for fixed signed angular frequency. -/
theorem cubicThetaAngular_completed {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C)
    (ℓ : ℤ) {s : ℂ} (hs : 3/2 < s.re) :
    mellin (fun v : ℝ => cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (0,v))
      (2*s+(ℓ.natAbs:ℂ)-1) =
      (1/4:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2*(s+(ℓ.natAbs:ℂ)/2))*
        Complex.Gamma (s+(ℓ.natAbs:ℂ)/2+1/6)*Complex.Gamma (s+(ℓ.natAbs:ℂ)/2-1/6)*
        cubicThetaDirichlet (fun n => theta ℓ n*a n) (2*s-1) := by
  rw [cubicThetaAngular_mellin hC ha ℓ hs]
  have hhalf : (1/6:ℝ) < (s+(ℓ.natAbs:ℂ)/2).re := by
    simp only [Complex.add_re,Complex.div_ofNat_re,Complex.natCast_re]
    have hk : (0:ℝ) ≤ ℓ.natAbs := Nat.cast_nonneg _
    linarith
  have he : 2*s+(ℓ.natAbs:ℂ)-1 = 2*(s+(ℓ.natAbs:ℂ)/2)-1 := by ring
  rw [he,cubicThetaWhittaker_mellin hhalf]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCirclePolynomial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Fourier polynomial underlying higher angular extraction.
Its highest Fourier mode is a pure power of the complex frequency. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaCircle_fourier_pow (j : ℤ) (m : ℕ) (t : AddCircle (1:ℝ)) :
    (fourier j t)^m=fourier ((m:ℤ)*j) t := by
  induction m with
  | zero => simp
  | succ m hm =>
      rw [pow_succ,hm,show ((m+1:ℕ):ℤ)*j=(m:ℤ)*j+j by push_cast; ring,fourier_add]

lemma cubicThetaCirclePower_expansion (w : ℂ) (m : ℕ) (t : AddCircle (1:ℝ)) :
    cubicThetaCirclePower w m t=
      ∑ j∈Finset.range (m+1),
        ((m.choose j:ℕ):ℂ)*w^j*(star w)^(m-j)*fourier (2*(j:ℤ)-(m:ℤ)) t := by
  unfold cubicThetaCirclePower
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
  rw [mul_pow,mul_pow,cubicThetaCircle_fourier_pow,cubicThetaCircle_fourier_pow]
  simp only [mul_one,mul_neg_one]
  have he : (j:ℤ)+(-((m-j:ℕ):ℤ))=2*(j:ℤ)-(m:ℤ) := by omega
  calc
    _ = (((m.choose j:ℕ):ℂ)*w^j*(star w)^(m-j))*
        (fourier (j:ℤ) t*fourier (-((m-j:ℕ):ℤ)) t) := by ring
    _ = _ := by rw [←fourier_add,he]

attribute [local instance] OAI.CubicFirstMoment.instFactLtRealOfNat_solutions
lemma cubicThetaCirclePower_coefficient (w : ℂ) (m : ℕ) (k : ℤ) :
    fourierCoeff (cubicThetaCirclePower w m) k=
      ∑ j∈Finset.range (m+1),
        ((m.choose j:ℕ):ℂ)*w^j*(star w)^(m-j)*
          (if k=2*(j:ℤ)-(m:ℤ) then 1 else 0) := by
  have he : cubicThetaCirclePower w m=
      ∑ j∈Finset.range (m+1),fun t : AddCircle (1:ℝ) =>
        (((m.choose j:ℕ):ℂ)*w^j*(star w)^(m-j))*fourier (2*(j:ℤ)-(m:ℤ)) t := by
    funext t
    simpa only [Finset.sum_apply] using cubicThetaCirclePower_expansion w m t
  rw [he]
  have hi (j : ℕ) (_ : j∈Finset.range (m+1)) : Integrable
      (fun t : AddCircle (1:ℝ) => (((m.choose j:ℕ):ℂ)*w^j*(star w)^(m-j))*
        fourier (2*(j:ℤ)-(m:ℤ)) t) AddCircle.haarAddCircle :=
    (continuous_const.mul (fourier _).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [fourierCoeff.sum _ _ hi]
  simp only [Finset.sum_apply,fourierCoeff.const_mul,fourierCoeff_fourier,Pi.single_apply]

lemma cubicThetaCirclePower_coefficient_above (w : ℂ) {m k : ℕ} (hmk : m<k) :
    fourierCoeff (cubicThetaCirclePower w m) (k:ℤ)=0 := by
  rw [cubicThetaCirclePower_coefficient]
  apply Finset.sum_eq_zero
  intro j hj
  have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
  have he : (k:ℤ)≠2*(j:ℤ)-(m:ℤ) := by omega
  simp only [he,ite_false, if_false,mul_zero]

lemma cubicThetaCirclePower_coefficient_top (w : ℂ) (m : ℕ) :
    fourierCoeff (cubicThetaCirclePower w m) (m:ℤ)=w^m := by
  rw [cubicThetaCirclePower_coefficient]
  rw [Finset.sum_eq_single m]
  · have he : (m:ℤ)=2*(m:ℤ)-(m:ℤ) := by ring
    rw [ite_eq_left he]
    simp
  · intro j hj hjm
    have he : (m:ℤ)≠2*(j:ℤ)-(m:ℤ) := by omega
    simp only [he,ite_false, if_false,mul_zero]
  · simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaImaginaryTaylor
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial remainder bound for a purely imaginary exponential.
The bound has no exponential loss in the frequency. -/
noncomputable section
open Set
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicTheta_exp_real_iteratedDeriv (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Complex.exp (c*(t:ℂ)))=
      fun t : ℝ => c^n*Complex.exp (c*(t:ℂ)) := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [iteratedDeriv_succ,hn]
      funext t
      have he : HasDerivAt (fun u : ℝ => Complex.exp (c*(u:ℂ)))
          (c*Complex.exp (c*(t:ℂ))) t := by
        simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one,mul_comm] using
          ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).cexp
      rw [(he.const_mul (c^n)).deriv,pow_succ]
      ring

theorem cubicTheta_exp_imaginary_taylor (c : ℂ) (hc : c.re=0) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖Complex.exp (c*(r:ℂ))-
      ∑ j∈Finset.range (n+1), (c*(r:ℂ))^j/(j.factorial:ℂ)‖≤
        ‖c‖^(n+1)*r^(n+1)/(n.factorial:ℝ) := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp [Finset.sum_range_succ']
  let f : ℝ→ℂ := fun t => Complex.exp (c*(t:ℂ))
  have hf (k : ℕ) : ContDiff ℝ k f := by
    dsimp [f]
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  have hi (k : ℕ) (t : ℝ) (ht : t∈Icc 0 r) :
      iteratedDerivWithin k f (Icc 0 r) t=c^k*Complex.exp (c*(t:ℂ)) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hr) (hf k).contDiffAt ht]
    exact congrFun (cubicTheta_exp_real_iteratedDeriv c k) t
  have ht := taylor_mean_remainder_bound hr.le (hf (n+1)).contDiffOn
    (right_mem_Icc.mpr hr.le) (C := ‖c‖^(n+1)) (fun t ht => by
      rw [hi (n+1) t ht,norm_mul,norm_pow,Complex.norm_exp]
      simp [Complex.mul_re,hc])
  have hp : taylorWithinEval f n (Icc 0 r) 0 r=
      ∑ j∈Finset.range (n+1), (c*(r:ℂ))^j/(j.factorial:ℂ) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hi j 0 (left_mem_Icc.mpr hr.le)]
    simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one,sub_zero,
      Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,
      Complex.ofReal_natCast,mul_pow,div_eq_mul_inv]
    ring
  simpa only [hp,sub_zero,f] using ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleTaylor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform angular Taylor extraction for one Fourier character. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaCircleLinear_real (w : ℂ) (t : AddCircle (1:ℝ)) :
    cubicThetaCircleLinear w t= (2*(w*fourier 1 t).re:ℝ) := by
  unfold cubicThetaCircleLinear
  rw [fourier_neg]
  simpa only [map_mul,Complex.star_def] using Complex.add_conj (w*fourier 1 t)

lemma cubicThetaCircleLinear_norm (w : ℂ) (t : AddCircle (1:ℝ)) :
    ‖cubicThetaCircleLinear w t‖≤2*‖w‖ := by
  calc
    _ ≤ ‖w*fourier 1 t‖+‖star w*fourier (-1) t‖ := norm_add_le _ _
    _ = _ := by simp only [norm_mul,fourier_apply,Circle.norm_coe,norm_star,mul_one]; ring

attribute [local instance] OAI.CubicFirstMoment.instFactLtRealOfNat_solutions_1
lemma cubicThetaCircleTaylor_coefficient (w : ℂ) (r : ℝ) (k : ℕ) :
    fourierCoeff (cubicThetaCircleTaylor w r k) (k:ℤ)=
      ((2*Real.pi*Complex.I*(r:ℂ))^k/(k.factorial:ℂ))*w^k := by
  classical
  have hi (j : ℕ) (_ : j∈Finset.range (k+1)) : Integrable
      (fun t : AddCircle (1:ℝ) => ((2*Real.pi*Complex.I*(r:ℂ))^j/(j.factorial:ℂ))*
        cubicThetaCirclePower w j t) AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_const.mul (((continuous_const.mul (fourier 1).continuous).add
      (continuous_const.mul (fourier (-1)).continuous)).pow j)
  have he : cubicThetaCircleTaylor w r k=
      ∑ j∈Finset.range (k+1),fun t : AddCircle (1:ℝ) =>
        ((2*Real.pi*Complex.I*(r:ℂ))^j/(j.factorial:ℂ))*cubicThetaCirclePower w j t := by
    funext t
    simp only [cubicThetaCircleTaylor,Finset.sum_apply]
  rw [he,fourierCoeff.sum _ _ hi]
  simp only [Finset.sum_apply,fourierCoeff.const_mul]
  rw [Finset.sum_eq_single k]
  · rw [cubicThetaCirclePower_coefficient_top]
  · intro j hj hjk
    rw [cubicThetaCirclePower_coefficient_above w (by have := Finset.mem_range.mp hj; omega),mul_zero]
  · simp

theorem cubicThetaCirclePhase_remainder (w : ℂ) (k : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (t : AddCircle (1:ℝ)) :
    ‖cubicThetaCirclePhase w r t-cubicThetaCircleTaylor w r k t‖≤
      (4*Real.pi*‖w‖)^(k+1)*r^(k+1)/(k.factorial:ℝ) := by
  let c := (2*Real.pi*Complex.I)*cubicThetaCircleLinear w t
  have hc : c.re=0 := by
    dsimp [c]
    rw [cubicThetaCircleLinear_real]
    simp [Complex.mul_re,Complex.mul_im]
  have hn : ‖c‖≤4*Real.pi*‖w‖ := by
    calc
      _ = (2*Real.pi)*‖cubicThetaCircleLinear w t‖ := by
        dsimp [c]
        simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg Real.pi_pos.le,Complex.norm_ofNat]
      _ ≤ (2*Real.pi)*(2*‖w‖) :=
        mul_le_mul_of_nonneg_left (cubicThetaCircleLinear_norm w t) (by positivity)
      _ = _ := by ring
  have he : ∑ j∈Finset.range (k+1), (c*(r:ℂ))^j/(j.factorial:ℂ)=
      cubicThetaCircleTaylor w r k t := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [c,cubicThetaCirclePower,cubicThetaCircleLinear]
    rw [mul_pow,mul_pow,mul_pow]
    ring
  have H := cubicTheta_exp_imaginary_taylor c hc k hr
  rw [he] at H
  change ‖Complex.exp (c*(r:ℂ))-cubicThetaCircleTaylor w r k t‖≤_ at H
  have hphase : Complex.exp (c*(r:ℂ))=cubicThetaCirclePhase w r t := by
    unfold cubicThetaCirclePhase c
    congr 1
    ring
  rw [hphase] at H
  exact H.trans (by gcongr)

lemma cubicThetaCircle_coefficient_error {f g : AddCircle (1:ℝ)→ℂ}
    (hf : Integrable f AddCircle.haarAddCircle)
    (hg : Integrable g AddCircle.haarAddCircle) {B : ℝ}
    (hB : ∀ t, ‖f t-g t‖≤B) (k : ℤ) :
    ‖fourierCoeff f k-fourierCoeff g k‖≤B := by
  rw [fourierCoeff,fourierCoeff,←integral_sub (hf.fourier_smul _) (hg.fourier_smul _)]
  have H := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (f := fun t : AddCircle (1:ℝ) => fourier (-k) t • f t-fourier (-k) t • g t)
    (ae_of_all _ (fun t => by
      rw [←smul_sub,norm_smul,fourier_apply,Circle.norm_coe,one_mul]
      exact hB t))
  simpa using H

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier coefficient estimates for the small-circle character expansion. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCirclePhase_continuous (w : ℂ) (r : ℝ) :
    Continuous (cubicThetaCirclePhase w r) := by
  unfold cubicThetaCirclePhase cubicThetaCircleLinear
  exact (continuous_const.mul ((continuous_const.mul (fourier 1).continuous).add
    (continuous_const.mul (fourier (-1)).continuous))).cexp

lemma cubicThetaCirclePhase_norm (w : ℂ) (r : ℝ) (t : AddCircle (1:ℝ)) :
    ‖cubicThetaCirclePhase w r t‖=1 := by
  unfold cubicThetaCirclePhase
  rw [Complex.norm_exp,cubicThetaCircleLinear_real]
  simp [Complex.mul_re,Complex.mul_im]

attribute [local instance] OAI.CubicFirstMoment.instFactLtRealOfNat_solutions_2
lemma cubicThetaCirclePhase_integrable (w : ℂ) (r : ℝ) :
    Integrable (cubicThetaCirclePhase w r) AddCircle.haarAddCircle :=
  (cubicThetaCirclePhase_continuous w r).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma cubicThetaCircleTaylor_continuous (w : ℂ) (r : ℝ) (k : ℕ) :
    Continuous (cubicThetaCircleTaylor w r k) := by
  unfold cubicThetaCircleTaylor cubicThetaCirclePower
  exact continuous_finsetSum _ (fun j _ => continuous_const.mul
    (((continuous_const.mul (fourier 1).continuous).add
      (continuous_const.mul (fourier (-1)).continuous)).pow j))

theorem cubicThetaCirclePhase_coefficient_remainder (w : ℂ) (k : ℕ)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖fourierCoeff (cubicThetaCirclePhase w r) (k:ℤ)-
      ((2*Real.pi*Complex.I*(r:ℂ))^k/(k.factorial:ℂ))*w^k‖≤
        (4*Real.pi*‖w‖)^(k+1)*r^(k+1)/(k.factorial:ℝ) := by
  rw [←cubicThetaCircleTaylor_coefficient]
  exact cubicThetaCircle_coefficient_error (cubicThetaCirclePhase_integrable w r)
    ((cubicThetaCircleTaylor_continuous w r k).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (cubicThetaCirclePhase_remainder w k hr) (k:ℤ)

lemma cubicThetaCirclePhase_coefficient_norm (w : ℂ) (r : ℝ) (k : ℤ) :
    ‖fourierCoeff (cubicThetaCirclePhase w r) k‖≤1 := by
  unfold fourierCoeff
  have H := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (f := fun t : AddCircle (1:ℝ) => fourier (-k) t • cubicThetaCirclePhase w r t)
    (C := 1) (ae_of_all _ (fun t => by
      simp only [norm_smul,fourier_apply,Circle.norm_coe,cubicThetaCirclePhase_norm,mul_one,le_refl]))
  simpa using H

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-circle coefficient extraction for an absolutely convergent Fourier series.
Only the zeroth, selected and next absolute frequency moments are used. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

variable {ι : Type*}

lemma cubicThetaCircleSeries_continuous {a w : ι→ℂ}
    (ha : Summable (fun n => ‖a n‖)) (r : ℝ) :
    Continuous (cubicThetaCircleSeries a w r) := by
  exact continuous_tsum
    (fun n => continuous_const.mul (cubicThetaCirclePhase_continuous (w n) r)) ha
    (fun n t => by simp only [norm_mul,cubicThetaCirclePhase_norm,mul_one,le_refl])

variable [Countable ι]

attribute [local instance] OAI.CubicFirstMoment.instFactLtRealOfNat_solutions_3
lemma cubicThetaCircleSeries_coefficient {a w : ι→ℂ}
    (ha : Summable (fun n => ‖a n‖)) (r : ℝ) (k : ℤ) :
    fourierCoeff (cubicThetaCircleSeries a w r) k=
      ∑' n, a n*fourierCoeff (cubicThetaCirclePhase (w n) r) k := by
  let f := fun n t => a n*(fourier (-k) t*cubicThetaCirclePhase (w n) r t)
  have hi (n : ι) : Integrable (f n) AddCircle.haarAddCircle :=
    ((cubicThetaCirclePhase_integrable (w n) r).fourier_smul (-k)).const_mul (a n)
  have hn (n : ι) : (∫ t, ‖f n t‖ ∂AddCircle.haarAddCircle)=‖a n‖ := by
    simp only [f,norm_mul,fourier_apply,Circle.norm_coe,cubicThetaCirclePhase_norm,mul_one]
    simp
  have hs : Summable (fun n => ∫ t, ‖f n t‖ ∂AddCircle.haarAddCircle) := by
    simpa only [hn] using ha
  calc
    _ = ∫ t, ∑' n, f n t ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      change fourier (-k) t*(∑' n, a n*cubicThetaCirclePhase (w n) r t)=
        ∑' n, a n*(fourier (-k) t*cubicThetaCirclePhase (w n) r t)
      rw [←tsum_mul_left]
      apply tsum_congr
      intro n
      ring
    _ = ∑' n, ∫ t, f n t ∂AddCircle.haarAddCircle :=
      (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = _ := by
      apply tsum_congr
      intro n
      exact integral_const_mul _ _

theorem cubicThetaCircleSeries_remainder {a w : ι→ℂ}
    (ha : Summable (fun n => ‖a n‖)) (k : ℕ)
    (hk : Summable (fun n => a n*w n^k))
    (hk1 : Summable (fun n => ‖a n‖*‖w n‖^(k+1))) {r : ℝ} (hr : 0 ≤ r) :
    ‖fourierCoeff (cubicThetaCircleSeries a w r) (k:ℤ)-
      ((2*Real.pi*Complex.I*(r:ℂ))^k/(k.factorial:ℂ))*(∑' n, a n*w n^k)‖≤
        ((4*Real.pi)^(k+1)*r^(k+1)/(k.factorial:ℝ))*
          (∑' n, ‖a n‖*‖w n‖^(k+1)) := by
  let D : ℂ := (2*Real.pi*Complex.I*(r:ℂ))^k/(k.factorial:ℂ)
  let K : ℝ := (4*Real.pi)^(k+1)*r^(k+1)/(k.factorial:ℝ)
  have hK : 0≤K := by dsimp [K]; positivity
  have hsF : Summable (fun n => a n*fourierCoeff (cubicThetaCirclePhase (w n) r) (k:ℤ)) :=
    ha.of_norm_bounded (fun n => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (cubicThetaCirclePhase_coefficient_norm (w n) r (k:ℤ))
        (_root_.norm_nonneg _)).trans_eq (mul_one _))
  have hsM : Summable (fun n => D*(a n*w n^k)) := hk.mul_left D
  have hB (n : ι) :
      ‖a n*fourierCoeff (cubicThetaCirclePhase (w n) r) (k:ℤ)-D*(a n*w n^k)‖≤
        K*(‖a n‖*‖w n‖^(k+1)) := by
    calc
      _ = ‖a n‖*‖fourierCoeff (cubicThetaCirclePhase (w n) r) (k:ℤ)-D*w n^k‖ := by
        rw [←norm_mul]
        congr 1
        ring
      _ ≤ ‖a n‖*((4*Real.pi*‖w n‖)^(k+1)*r^(k+1)/(k.factorial:ℝ)) :=
        mul_le_mul_of_nonneg_left (cubicThetaCirclePhase_coefficient_remainder (w n) k hr)
          (_root_.norm_nonneg _)
      _ = _ := by dsimp [K]; rw [mul_pow]; ring
  rw [cubicThetaCircleSeries_coefficient ha]
  change ‖(∑' n, a n*fourierCoeff (cubicThetaCirclePhase (w n) r) (k:ℤ))-
    D*(∑' n, a n*w n^k)‖≤_
  rw [←tsum_mul_left,←hsF.tsum_sub hsM]
  calc
    _ ≤ ∑' n, ‖a n*fourierCoeff (cubicThetaCirclePhase (w n) r) (k:ℤ)-D*(a n*w n^k)‖ :=
      norm_tsum_le_tsum_norm (hsF.sub hsM).norm
    _ ≤ ∑' n, K*(‖a n‖*‖w n‖^(k+1)) :=
      Summable.tsum_le_tsum hB (hsF.sub hsM).norm (hk1.mul_left K)
    _ = _ := tsum_mul_left

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleNormalized
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radius-normalized coefficient extraction, with a linear error in the radius. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

variable {ι : Type*} [Countable ι]

attribute [local instance] OAI.CubicFirstMoment.instFactLtRealOfNat_solutions_4
theorem cubicThetaCircleSeries_normalized_remainder {a w : ι→ℂ}
    (ha : Summable (fun n => ‖a n‖)) (k : ℕ)
    (hk : Summable (fun n => a n*w n^k))
    (hk1 : Summable (fun n => ‖a n‖*‖w n‖^(k+1))) {r : ℝ} (hr : 0 < r) :
    ‖fourierCoeff (cubicThetaCircleSeries a w r) (k:ℤ)/(r:ℂ)^k-
      ((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(∑' n, a n*w n^k)‖≤
        (((4*Real.pi)^(k+1)/(k.factorial:ℝ))*
          (∑' n, ‖a n‖*‖w n‖^(k+1)))*r := by
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have he : fourierCoeff (cubicThetaCircleSeries a w r) (k:ℤ)/(r:ℂ)^k-
      ((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(∑' n, a n*w n^k)=
    (fourierCoeff (cubicThetaCircleSeries a w r) (k:ℤ)-
      ((2*Real.pi*Complex.I*(r:ℂ))^k/(k.factorial:ℂ))*(∑' n, a n*w n^k))/(r:ℂ)^k := by
    rw [mul_pow]
    field_simp [hrC]
    simp only [mul_pow]
    ring
  rw [he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  apply (div_le_iff₀ (pow_pos hr k)).mpr
  convert cubicThetaCircleSeries_remainder ha k hk hk1 hr.le using 1
  all_goals try with_reducible_and_instances rfl
  rw [pow_succ]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleTrace
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual trace character on a small horizontal circle, with both orientations. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCirclePhase_trace (w : ℂ) (r : ℝ) (t : AddCircle (1:ℝ)) :
    cubicThetaCirclePhase w r t=
      (Real.fourierChar (tracePair w ((r:ℂ)*fourier 1 t)):ℂ) := by
  rw [Real.fourierChar_apply]
  unfold cubicThetaCirclePhase
  rw [cubicThetaCircleLinear_real]
  congr 1
  simp only [tracePair,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  push_cast
  ring

lemma cubicThetaCirclePhase_trace_reverse (w : ℂ) (r : ℝ) (t : AddCircle (1:ℝ)) :
    cubicThetaCirclePhase (star w) r t=
      (Real.fourierChar (tracePair w ((r:ℂ)*fourier (-1) t)):ℂ) := by
  rw [cubicThetaCirclePhase_trace,fourier_neg]
  congr 2
  simp only [tracePair,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma cubicThetaSeriesTerm_add (a : Eisenstein→ℂ) (z u : ℂ) (v : ℝ) (n : Eisenstein) :
    cubicThetaSeriesTerm a (z+u) v n=cubicThetaSeriesTerm a z v n*
      (Real.fourierChar (tracePair (cubicThetaFrequency n) u):ℂ) := by
  by_cases hn : n=0
  · simp [cubicThetaSeriesTerm,hn]
  have ht : tracePair (cubicThetaFrequency n) (z+u)=
      tracePair (cubicThetaFrequency n) z+tracePair (cubicThetaFrequency n) u := by
    simp only [tracePair,mul_add,Complex.add_re]
  simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,ht,AddChar.map_add_eq_mul,Circle.coe_mul]
  ring

lemma cubicThetaSeriesTerm_circle (a : Eisenstein→ℂ) (z d : ℂ) (r v : ℝ)
    (n : Eisenstein) (t : AddCircle (1:ℝ)) :
    cubicThetaSeriesTerm a (z+(r:ℂ)*d*fourier 1 t) v n=
      cubicThetaSeriesTerm a z v n*cubicThetaCirclePhase (cubicThetaFrequency n*d) r t := by
  rw [cubicThetaSeriesTerm_add,cubicThetaCirclePhase_trace]
  congr 2
  simp only [tracePair,mul_assoc,mul_comm,mul_left_comm]
  rfl

lemma cubicThetaSeriesTerm_circle_reverse (a : Eisenstein→ℂ) (z d : ℂ) (r v : ℝ)
    (n : Eisenstein) (t : AddCircle (1:ℝ)) :
    cubicThetaSeriesTerm a (z+(r:ℂ)*d*fourier (-1) t) v n=
      cubicThetaSeriesTerm a z v n*cubicThetaCirclePhase (star (cubicThetaFrequency n*d)) r t := by
  rw [cubicThetaSeriesTerm_add,cubicThetaCirclePhase_trace_reverse]
  congr 2
  simp only [tracePair,mul_assoc,mul_comm,mul_left_comm]
  rfl

lemma cubicThetaSeriesTerm_frequency_power (a : Eisenstein→ℂ) (z : ℂ) (v : ℝ)
    (n : Eisenstein) (k : ℕ) :
    cubicThetaSeriesTerm a z v n*cubicThetaFrequency n^k=
      cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (k:ℤ)) z v n := by
  by_cases hn : n=0
  · simp [cubicThetaSeriesTerm,hn]
  simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,cubicThetaAngularCoefficient_nat]
  ring

lemma cubicThetaSeriesTerm_conj_frequency_power (a : Eisenstein→ℂ) (z : ℂ) (v : ℝ)
    (n : Eisenstein) (k : ℕ) :
    cubicThetaSeriesTerm a z v n*star (cubicThetaFrequency n)^k=
      cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (-(k:ℤ))) z v n := by
  by_cases hn : n=0
  · simp [cubicThetaSeriesTerm,hn]
  simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,cubicThetaAngularCoefficient_neg_nat]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaJointMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable bounds for the actual full differential on positive strips. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAngular_uniform_terms {a : Eisenstein → ℂ} {C b : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hb : 0<b) :
    ∃ u : Eisenstein → ℝ, Summable u ∧ ∀ (n : Eisenstein) (p : ℂ × ℝ), b<p.2 →
      ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) p.1 p.2 n‖≤u n := by
  let K := C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)
  let e : ℝ := 4/3-2*((ℓ.natAbs:ℝ)+3)
  have hK : 0≤K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC
      (cubicWhittakerPowerConstant_pos (by omega : 1≤ℓ.natAbs+3)).le)
      (by positivity)) (by positivity)
  have he : e≤0 := by
    dsimp [e]
    have h : (0:ℝ)≤ℓ.natAbs := Nat.cast_nonneg _
    linarith
  refine ⟨fun n => (K*b^e)*norm n^(-4/3:ℝ),?_,?_⟩
  · simpa only [neg_div] using
      (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ)<4/3)).mul_left (K*b^e)
  · intro n p hp
    exact (cubicThetaAngular_term_bound hC ha ℓ (hb.trans hp) p.1 n).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hb hp.le he) hK)
        (Real.rpow_nonneg (norm_nonneg n) _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleActual
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-circle coefficients of the actual fixed-height theta series.
Both orientations retain their precise signed angular coefficients. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCircleActual_series (a : Eisenstein→ℂ) (z d : ℂ) (r v : ℝ) (rev : Bool) :
    (fun t => cubicThetaNonconstant a (z+cubicThetaSignedCircle rev d r t,v))=
      cubicThetaCircleSeries (cubicThetaSeriesTerm a z v) (cubicThetaCircleFrequency rev d) r := by
  funext t
  apply tsum_congr
  intro n
  cases rev
  · exact cubicThetaSeriesTerm_circle a z d r v n t
  · exact cubicThetaSeriesTerm_circle_reverse a z d r v n t

lemma cubicThetaCircleActual_power (a : Eisenstein→ℂ) (z d : ℂ) (v : ℝ)
    (rev : Bool) (n : Eisenstein) (k : ℕ) :
    cubicThetaSeriesTerm a z v n*(cubicThetaCircleFrequency rev d n)^k=
      (cubicThetaCircleMultiplier rev d)^k*
        cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) z v n := by
  cases rev
  · change cubicThetaSeriesTerm a z v n*(cubicThetaFrequency n*d)^k=
      d^k*cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (k:ℤ)) z v n
    rw [mul_pow,←cubicThetaSeriesTerm_frequency_power]
    ring
  · change cubicThetaSeriesTerm a z v n*(star (cubicThetaFrequency n*d))^k=
      (star d)^k*cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (-(k:ℤ))) z v n
    rw [star_mul,mul_pow,←cubicThetaSeriesTerm_conj_frequency_power]
    ring

lemma cubicThetaCircleActual_power_norm (a : Eisenstein→ℂ) (z d : ℂ) (v : ℝ)
    (rev : Bool) (n : Eisenstein) (k : ℕ) :
    ‖cubicThetaSeriesTerm a z v n‖*‖cubicThetaCircleFrequency rev d n‖^k=
      ‖d‖^k*‖cubicThetaSeriesTerm
        (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) z v n‖ := by
  have h := congrArg (fun x : ℂ => ‖x‖) (cubicThetaCircleActual_power a z d v rev n k)
  simp only [norm_mul,norm_pow] at h
  cases rev <;> simpa [cubicThetaCircleMultiplier] using h

lemma cubicThetaCircleActual_summable {a : Eisenstein→ℂ} {C : ℝ} (hC : 0≤C)
    (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n) (z d : ℂ) {v : ℝ} (hv : 0<v)
    (rev : Bool) (k : ℕ) :
    Summable (fun n => cubicThetaSeriesTerm a z v n*(cubicThetaCircleFrequency rev d n)^k) := by
  have h := (cubicThetaAngular_summable hC ha (cubicThetaCircleOrder rev k) hv z).mul_left
    ((cubicThetaCircleMultiplier rev d)^k)
  exact h.congr (fun n => (cubicThetaCircleActual_power a z d v rev n k).symm)

attribute [local instance] OAI.CubicFirstMoment.instFactLtRealOfNat_solutions_5
local instance localInst_r494f04_1 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
theorem cubicThetaCircleActual_remainder {a : Eisenstein→ℂ} {C : ℝ} (hC : 0≤C)
    (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n) (z d : ℂ) {v : ℝ} (hv : 0<v)
    (rev : Bool) (k : ℕ) {r : ℝ} (hr : 0 < r) :
    ‖fourierCoeff (fun t => cubicThetaNonconstant a (z+cubicThetaSignedCircle rev d r t,v))
        (k:ℤ)/(r:ℂ)^k-
      ((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(cubicThetaCircleMultiplier rev d)^k*
        cubicThetaNonconstant (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) (z,v)‖≤
      (((4*Real.pi)^(k+1)/(k.factorial:ℝ))*‖d‖^(k+1)*
        ∑' n, ‖cubicThetaSeriesTerm
          (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev (k+1))) z v n‖)*r := by
  have hzero := cubicThetaAngular_summable hC ha 0 hv z
  have ha0 : cubicThetaAngularCoefficient a 0=a := by
    funext n
    simp [cubicThetaAngularCoefficient,theta]
  rw [ha0] at hzero
  have hk := cubicThetaCircleActual_summable hC ha z d hv rev k
  have hk1 := (cubicThetaCircleActual_summable hC ha z d hv rev (k+1)).norm
  simp only [norm_mul,norm_pow] at hk1
  have H := cubicThetaCircleSeries_normalized_remainder hzero.norm k hk hk1 hr
  rw [←cubicThetaCircleActual_series a z d r v rev] at H
  have he : (∑' n, cubicThetaSeriesTerm a z v n*(cubicThetaCircleFrequency rev d n)^k)=
      (cubicThetaCircleMultiplier rev d)^k*
        cubicThetaNonconstant (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) (z,v) := by
    simp_rw [cubicThetaCircleActual_power,tsum_mul_left]
    rfl
  have hm : (∑' n, ‖cubicThetaSeriesTerm a z v n‖*‖cubicThetaCircleFrequency rev d n‖^(k+1))=
      ‖d‖^(k+1)*∑' n, ‖cubicThetaSeriesTerm
        (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev (k+1))) z v n‖ := by
    simp_rw [cubicThetaCircleActual_power_norm,tsum_mul_left]
  rw [he,hm] at H
  simpa only [mul_assoc] using H

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleInversion
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inversion takes every horizontal circle to a reversed horizontal circle.
Its transformed height depends only on the radius. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaSignedCircle_radius (rev : Bool) (r v : ℝ) (t : AddCircle (1:ℝ)) :
    cubicThetaRadius (cubicThetaSignedCircle rev 1 r t,v)=r^2+v^2 := by
  have hn : Complex.normSq (fourier (if rev then -1 else 1) t)=1 := by
    rw [Complex.normSq_eq_norm_sq,fourier_apply,Circle.norm_coe,one_pow]
  simp only [cubicThetaRadius,cubicThetaSignedCircle,mul_one,Complex.normSq_mul,
    Complex.normSq_ofReal,hn,mul_one]
  ring

theorem cubicThetaInversion_circle (q : ℂ) (rev : Bool) (r v : ℝ) (t : AddCircle (1:ℝ)) :
    cubicThetaInversion q (cubicThetaSignedCircle rev 1 r t,v)=
      (cubicThetaSignedCircle (!rev) (cubicThetaCircleDualDirection q v r) r t,
        cubicThetaCircleDualHeight q v r) := by
  apply Prod.ext
  · change -star (cubicThetaSignedCircle rev 1 r t)/
      (q^2*(cubicThetaRadius (cubicThetaSignedCircle rev 1 r t,v):ℂ))=_
    rw [cubicThetaSignedCircle_radius]
    cases rev <;>
      simp only [cubicThetaSignedCircle,cubicThetaCircleDualDirection,Bool.not_false,
        Bool.not_true,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,mul_one,star_mul,
        Complex.star_def,Complex.conj_ofReal,fourier_neg,starRingEnd_self_apply]
    all_goals ring
  · change v/(Complex.normSq q*cubicThetaRadius (cubicThetaSignedCircle rev 1 r t,v))=_
    rw [cubicThetaSignedCircle_radius]
    rfl

lemma cubicThetaCircleDualDirection_limit {q : ℂ} (hq : q≠0) {v : ℝ} (hv : 0<v) :
    Tendsto (cubicThetaCircleDualDirection q v) (𝓝[Set.Ioi 0] 0)
      (𝓝 (-1/(q^2*(v:ℂ)^2))) := by
  have hn : q^2*((0^2+v^2:ℝ):ℂ)≠0 := by
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),zero_add,Complex.ofReal_pow]
    exact mul_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hv.ne'))
  have hc : ContinuousAt (cubicThetaCircleDualDirection q v) 0 := by
    exact continuousAt_const.div (continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_id.pow 2).add_const (v^2)))) hn
  simpa [cubicThetaCircleDualDirection] using hc.tendsto.mono_left nhdsWithin_le_nhds

lemma cubicThetaCircleDualHeight_limit {q : ℂ} (hq : q≠0) {v : ℝ} (hv : 0<v) :
    Tendsto (cubicThetaCircleDualHeight q v) (𝓝[Set.Ioi 0] 0)
      (𝓝 ((Complex.normSq q*v)⁻¹)) := by
  have hn : Complex.normSq q*(0^2+v^2)≠0 := by
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),zero_add]
    exact mul_ne_zero (Complex.normSq_pos.mpr hq).ne' (pow_ne_zero _ hv.ne')
  have hc : ContinuousAt (cubicThetaCircleDualHeight q v) 0 :=
    continuousAt_const.div (continuousAt_const.mul ((continuousAt_id.pow 2).add_const (v^2))) hn
  have he : cubicThetaCircleDualHeight q v 0=(Complex.normSq q*v)⁻¹ := by
    dsimp [cubicThetaCircleDualHeight]
    norm_num only [zero_pow,zero_add]
    field_simp
  rw [←he]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleUniform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform small-circle extraction above a fixed positive height. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.instFactLtRealOfNat_solutions_6
theorem cubicThetaCircleActual_uniform {a : Eisenstein→ℂ} {C b M : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (hb : 0<b) (hM : 0≤M) (rev : Bool) (k : ℕ) :
    ∃ K : ℝ, 0≤K ∧ ∀ (z d : ℂ) (v r : ℝ), b<v → ‖d‖≤M → 0 < r →
      ‖fourierCoeff (fun t => cubicThetaNonconstant a (z+cubicThetaSignedCircle rev d r t,v))
          (k:ℤ)/(r:ℂ)^k-
        ((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(cubicThetaCircleMultiplier rev d)^k*
          cubicThetaNonconstant (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) (z,v)‖≤K*r := by
  obtain ⟨u,hu,hbu⟩ := cubicThetaAngular_uniform_terms hC ha (cubicThetaCircleOrder rev (k+1)) hb
  have hu0 (n : Eisenstein) : 0≤u n := (_root_.norm_nonneg
    (cubicThetaSeriesTerm (cubicThetaAngularCoefficient a
      (cubicThetaCircleOrder rev (k+1))) 0 (b+1) n)).trans (hbu n (0,b+1) (by linarith))
  let B : ℝ := (4*Real.pi)^(k+1)/(k.factorial:ℝ)
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨B*M^(k+1)*(∑' n, u n),
    mul_nonneg (mul_nonneg hB (pow_nonneg hM _)) (tsum_nonneg hu0),?_⟩
  intro z d v r hv hd hr
  have hv0 := hb.trans hv
  have hs := (cubicThetaAngular_summable hC ha (cubicThetaCircleOrder rev (k+1)) hv0 z).norm
  have hsum : (∑' n, ‖cubicThetaSeriesTerm
      (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev (k+1))) z v n‖)≤∑' n, u n :=
    Summable.tsum_le_tsum (fun n => hbu n (z,v) hv) hs hu
  calc
    _ ≤ (B*‖d‖^(k+1)*∑' n, ‖cubicThetaSeriesTerm
        (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev (k+1))) z v n‖)*r :=
      cubicThetaCircleActual_remainder hC ha z d hv0 rev k hr
    _ ≤ _ := by gcongr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleLimit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular extraction survives continuous changes of height and direction. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.instFactLtRealOfNat_solutions_7
theorem cubicThetaCircleActual_limit {a : Eisenstein→ℂ} {C : ℝ} (hC : 0≤C)
    (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n) (z : ℂ) (rev : Bool) (k : ℕ)
    {d : ℝ→ℂ} {v : ℝ→ℝ} {d₀ : ℂ} {v₀ : ℝ}
    (hd : Tendsto d (𝓝[Set.Ioi 0] 0) (𝓝 d₀))
    (hv : Tendsto v (𝓝[Set.Ioi 0] 0) (𝓝 v₀)) (hv₀ : 0<v₀) :
    Tendsto (fun r : ℝ => fourierCoeff
      (fun t => cubicThetaNonconstant a (z+cubicThetaSignedCircle rev (d r) r t,v r))
        (k:ℤ)/(r:ℂ)^k) (𝓝[Set.Ioi 0] 0)
      (𝓝 (((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(cubicThetaCircleMultiplier rev d₀)^k*
        cubicThetaNonconstant (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) (z,v₀))) := by
  let g := fun r : ℝ => ((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*
    (cubicThetaCircleMultiplier rev (d r))^k*
      cubicThetaNonconstant (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) (z,v r)
  have hdM : Tendsto (fun r => cubicThetaCircleMultiplier rev (d r))
      (𝓝[Set.Ioi 0] 0) (𝓝 (cubicThetaCircleMultiplier rev d₀)) := by
    cases rev
    · exact hd
    · exact hd.star
  have hF := (cubicThetaAngular_continuousAt hC ha (cubicThetaCircleOrder rev k)
    (p := (z,v₀)) hv₀).tendsto.comp (tendsto_const_nhds.prodMk_nhds hv)
  have hg : Tendsto g (𝓝[Set.Ioi 0] 0)
      (𝓝 (((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(cubicThetaCircleMultiplier rev d₀)^k*
        cubicThetaNonconstant (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) (z,v₀))) :=
    (tendsto_const_nhds.mul (hdM.pow k)).mul hF
  obtain ⟨K,hK,hbound⟩ := cubicThetaCircleActual_uniform hC ha
    (show 0<v₀/2 by positivity) (show 0≤‖d₀‖+1 by positivity) rev k
  have hb : ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0,
      ‖fourierCoeff
        (fun t => cubicThetaNonconstant a (z+cubicThetaSignedCircle rev (d r) r t,v r))
          (k:ℤ)/(r:ℂ)^k-g r‖≤K*r := by
    filter_upwards [hv.eventually (lt_mem_nhds (by linarith : v₀/2<v₀)),
      hd.norm.eventually (gt_mem_nhds (lt_add_one ‖d₀‖)),self_mem_nhdsWithin] with r hvr hdr hr
    exact hbound z (d r) (v r) r hvr hdr.le hr
  have he : Tendsto (fun r : ℝ => fourierCoeff
      (fun t => cubicThetaNonconstant a (z+cubicThetaSignedCircle rev (d r) r t,v r))
        (k:ℤ)/(r:ℂ)^k-g r) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
    apply squeeze_zero_norm' hb
    simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun r : ℝ => K*r) (𝓝[Set.Ioi 0] 0) (𝓝 (K*0)))
  simpa only [zero_add,sub_add_cancel] using he.add hg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCirclePlane
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constant mode disappears from every positive small-circle coefficient. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.instFactLtRealOfNat_solutions_8
lemma cubicThetaCircle_coefficient_const_add (c : ℂ) {f : AddCircle (1:ℝ)→ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) {k : ℤ} (hk : k≠0) :
    fourierCoeff (fun t => c+f t) k=fourierCoeff f k := by
  have he : (fun _ : AddCircle (1:ℝ) => c)=fun t => c*fourier 0 t := by
    funext t
    simp
  have hz : fourierCoeff (fun _ : AddCircle (1:ℝ) => c) k=0 := by
    rw [he,fourierCoeff.const_mul]
    simp [fourierCoeff_fourier,hk]
  have h := congrFun (fourierCoeff.add (integrable_const c) hf) k
  have ha : (fun t => c+f t)=(fun _ : AddCircle (1:ℝ) => c)+f := by
    funext t
    rfl
  rw [ha]
  simpa only [Pi.add_apply,hz,zero_add] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLevelAngularReciprocity
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put every genuine signed angular transformation on the symmetric height scale. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaLevelScale_square (q : Eisenstein) :
    cubicThetaLevelScale q^2=(norm q)⁻¹ := by
  unfold cubicThetaLevelScale
  rw [inv_pow,Real.sq_sqrt (norm_nonneg q)]

lemma cubicThetaLevelAngular_scaled_direction {q : Eisenstein} (hq : primary q)
    {t : ℝ} (ht : 0<t) :
    -1/((q:ℂ)^2*((cubicThetaLevelScale q*t⁻¹:ℝ):ℂ)^2)=
      (-(norm q:ℂ)/(q:ℂ)^2)*(t:ℂ)^2 := by
  have hqC : (q:ℂ)≠0 := fun he => primary_ne_zero hq (Subtype.ext he)
  have hN : (norm q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero (primary_ne_zero hq)).ne'
  have htC : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hs : (cubicThetaLevelScale q:ℂ)^2=(norm q:ℂ)⁻¹ := by
    exact_mod_cast cubicThetaLevelScale_square q
  simp only [Complex.ofReal_mul,Complex.ofReal_inv,mul_pow,hs]
  field_simp [hqC,hN,htC]

lemma cubicThetaCircleMultiplier_real_mul (rev : Bool) (d : ℂ) (t : ℝ) :
    cubicThetaCircleMultiplier rev (d*(t:ℂ)^2)=
      cubicThetaCircleMultiplier rev d*(t:ℂ)^2 := by
  cases rev <;> simp [cubicThetaCircleMultiplier,star_mul,mul_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularFunctionalEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The functional equation for the actual continued additive angular Dirichlet series.
Gamma cancellation is required only on the dual side. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAngular_completion_cancel {q : Eisenstein} (hq : primary q)
    (k : ℕ) (s : ℂ)
    (hG₁ : Complex.Gamma (s+(k:ℂ)/2+1/6)≠0)
    (hG₂ : Complex.Gamma (s+(k:ℂ)/2-1/6)≠0) :
    cubicThetaAngularCompletion q k s*cubicThetaAngularUncompletion q k s=1 := by
  have hρ : (cubicThetaLevelScale q:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaLevelScale_pos hq).ne'
  have hπ : ((2*Real.pi:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hρp : (cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1)≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hρ)
  have hπp : ((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ))≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
  unfold cubicThetaAngularCompletion cubicThetaAngularUncompletion
  rw [Complex.cpow_neg,Complex.cpow_neg]
  calc
    _ = (((cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1))⁻¹*
          (cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1))*
        ((((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ)))⁻¹*((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ)))*
        (Complex.Gamma (s+(k:ℂ)/2+1/6)*(Complex.Gamma (s+(k:ℂ)/2+1/6))⁻¹)*
        (Complex.Gamma (s+(k:ℂ)/2-1/6)*(Complex.Gamma (s+(k:ℂ)/2-1/6))⁻¹) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hρp,inv_mul_cancel₀ hπp,mul_inv_cancel₀ hG₁,mul_inv_cancel₀ hG₂]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularGammaEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual angular functional equation has the Gamma quotient occurring
in the published Voronoi transform. No Voronoi identity is used here. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAngular_archimedean_ratio {q : Eisenstein} (hq : primary q)
    (rev : Bool) (k : ℕ) (s : ℂ) :
    cubicThetaAngularUncompletion q k s*cubicThetaAngularCompletion q k (1-s)=
      (cubicThetaLevelScale q:ℂ)^(4*s-2)*((2*Real.pi:ℝ):ℂ)^(4*s-2)*
        metaplecticGammaQuotient (cubicThetaCircleOrder rev k) s := by
  have hρ : (cubicThetaLevelScale q:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaLevelScale_pos hq).ne'
  have hπ : ((2*Real.pi:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hkabs : ((|cubicThetaCircleOrder rev k|:ℤ):ℂ)=(k:ℂ) := by
    cases rev <;> simp [cubicThetaCircleOrder]
  have hρp : (cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1)*
      (cubicThetaLevelScale q:ℂ)^(-(2*(1-s)+(k:ℂ)-1))=
        (cubicThetaLevelScale q:ℂ)^(4*s-2) := by
    rw [←Complex.cpow_add _ _ hρ]
    congr 1
    ring
  have hπp : ((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ))*
      ((2*Real.pi:ℝ):ℂ)^(-(2*(1-s)+(k:ℂ)))=((2*Real.pi:ℝ):ℂ)^(4*s-2) := by
    rw [←Complex.cpow_add _ _ hπ]
    congr 1
    ring
  have hplus : 1-s+(k:ℂ)/2+1/6=7/6+(k:ℂ)/2-s := by ring
  have hminus : 1-s+(k:ℂ)/2-1/6=5/6+(k:ℂ)/2-s := by ring
  unfold cubicThetaAngularUncompletion cubicThetaAngularCompletion
  rw [hplus,hminus]
  calc
    _ = ((cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1)*
          (cubicThetaLevelScale q:ℂ)^(-(2*(1-s)+(k:ℂ)-1)))*
        (((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ))*((2*Real.pi:ℝ):ℂ)^(-(2*(1-s)+(k:ℂ))))*
          metaplecticGammaQuotient (cubicThetaCircleOrder rev k) s := by
      simp only [metaplecticGammaQuotient,hkabs,div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [hρp,hπp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique indexing of the primary theta frequencies by the original
squarefree and cube variables. There is no multiplicity factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Reindex a theta sum over S with exactly one term for each primary
squarefree-times-cube pair. -/
theorem cubicThetaPrimary_tsum (f : Eisenstein → ℂ) :
    (∑' n : Eisenstein, if cubicThetaPrimarySupport n then f n else 0) =
      ∑' cd : CubicThetaPrimaryPair, f (cubicThetaPrimaryNumerator cd) := by
  calc
    _ = ∑' n : {n // cubicThetaPrimarySupport n}, f n := by
      exact (tsum_subtype {n | cubicThetaPrimarySupport n} f).symm
    _ = _ := (cubicThetaPrimaryIndexEquiv.tsum_eq (fun n => f n)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGaussMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin transform of the literal primary Gauss expansion. All terms
are identified before applying the already proved absolute interchange. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimaryFrequency_sq (cd : CubicThetaPrimaryPair) :
    ‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖^2 =
      norm cd.val.1*norm cd.val.2^3/27 := by
  rw [cubicThetaFrequency_sq]
  unfold cubicThetaPrimaryNumerator norm
  simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,Complex.normSq_mul,map_pow,
    lambdaE_coe,traceLambda_normSq]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDirichletBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence gives uniform bounds on each initial vertical line. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaDirichletNormMass_nonneg (σ : ℝ) : 0 ≤ cubicThetaDirichletNormMass σ := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (_root_.norm_nonneg _) _

lemma cubicThetaDirichletNormMass_summable {σ : ℝ} (hσ : 2<σ) :
    Summable (fun n : Eisenstein => if n=0 then 0 else ‖cubicThetaFrequency n‖^(-σ)) := by
  simpa only [norm_one,one_mul] using cubicTheta_mellin_weight_summable
    (a := fun _ : Eisenstein => (1:ℂ)) (by norm_num : (0:ℝ)≤1)
      (fun _ => by norm_num) hσ

theorem cubicThetaDirichlet_norm_le {a : Eisenstein→ℂ} {C σ : ℝ}
    (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C) (hσ : 2<σ)
    (s : ℂ) (hs : s.re=σ) :
    ‖cubicThetaDirichlet a s‖≤C*cubicThetaDirichletNormMass σ := by
  let w := fun n : Eisenstein => if n=0 then 0 else ‖cubicThetaFrequency n‖^(-σ)
  have hw := cubicThetaDirichletNormMass_summable hσ
  have hb (n : Eisenstein) : ‖if n=0 then (0:ℂ) else a n*(‖cubicThetaFrequency n‖:ℂ)^(-s)‖≤C*w n := by
    by_cases hn : n=0
    · simp [hn,w]
    · simp only [hn,ite_false, if_false,w,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos
        (cubicThetaFrequency_pos hn),Complex.neg_re,hs]
      exact mul_le_mul_of_nonneg_right (ha n hn) (Real.rpow_nonneg (_root_.norm_nonneg _) _)
  have hsum : Summable (fun n : Eisenstein => if n=0 then (0:ℂ) else
      a n*(‖cubicThetaFrequency n‖:ℂ)^(-s)) := (hw.mul_left C).of_norm_bounded hb
  calc
    _ ≤ ∑' n, ‖if n=0 then (0:ℂ) else a n*(‖cubicThetaFrequency n‖:ℂ)^(-s)‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n, C*w n := Summable.tsum_le_tsum hb hsum.norm (hw.mul_left C)
    _ = _ := tsum_mul_left

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTransformBounds
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the literal angular Voronoi transform. Its Gamma quotient
is a product of two ordinary shifted Hecke quotients, so the only
special-function input is the same precise DLMF bounded-strip estimate. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplecticAngularShift_nonneg (ℓ : ℤ) : 0 ≤ metaplecticAngularShift ℓ := by
  unfold metaplecticAngularShift
  positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticGammaRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact far-left metaplectic Gamma growth from the finite recurrence.
Choosing Re s = 1/2-m gives the sharp height exponent 4m = 2+4A,
A=m-1/2. No additional Stirling or completed-height input is needed. -/
noncomputable section
namespace CubicFirstMoment

private lemma metaplectic_ascPochhammer_norm (n : ℕ) (z : ℂ) :
    ‖(ascPochhammer ℂ n).eval z‖ ≤ (‖z‖+(n:ℝ))^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,norm_mul]
    have hn : ‖z+(n:ℂ)‖ ≤ ‖z‖+(n:ℝ) := by simpa using norm_add_le z (n:ℂ)
    calc
      _ ≤ (‖z‖+(n:ℝ))^n*(‖z‖+(n:ℝ)) :=
        mul_le_mul ih hn (_root_.norm_nonneg _) (by positivity)
      _ = (‖z‖+(n:ℝ))^(n+1) := (pow_succ _ _).symm
      _ ≤ (‖z‖+((n+1:ℕ):ℝ))^(n+1) := by
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        linarith

/-- A symmetric Gamma ratio for any fixed real shift, retaining the
zero values at the totalized Gamma poles. -/
lemma metaplectic_symmetric_gamma_ratio (k : ℝ) (m : ℕ) (t : ℝ) :
    ‖Complex.Gamma ((1/2:ℂ)+(m:ℂ)+(k:ℂ)-(t:ℂ)*Complex.I) /
      Complex.Gamma ((1/2:ℂ)-(m:ℂ)+(k:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (|k|+3*(m:ℝ)+1)^(2*m)*(1+|t|)^(2*m) := by
  let z : ℂ := (1/2:ℂ)-(m:ℂ)+(k:ℂ)+(t:ℂ)*Complex.I
  by_cases hG : Complex.Gamma z = 0
  · change ‖_ / Complex.Gamma z‖ ≤ _
    rw [hG,div_zero,norm_zero]
    positivity
  have hreg : ∀ n : ℕ, z ≠ -(n:ℂ) := by
    intro n hn
    apply hG
    rw [hn,Complex.Gamma_neg_nat_eq_zero]
  have he : ((1/2:ℂ)+(m:ℂ)+(k:ℂ)-(t:ℂ)*Complex.I) =
      starRingEnd ℂ (z+(2*m:ℕ)) := by
    dsimp [z]
    simp only [map_add,map_sub,map_mul,Complex.conj_ofReal,Complex.conj_I,
      map_natCast,map_div₀,map_one,map_ofNat]
    push_cast
    ring
  have hq := Complex.Gamma_add_nat_div_Gamma_eq (n := 2*m) z hreg
  have hn : ‖z‖ ≤ |k|+(m:ℝ)+1+|t| := by
    calc
      _ ≤ ‖(1/2:ℂ)-(m:ℂ)+(k:ℂ)‖+‖(t:ℂ)*Complex.I‖ := norm_add_le _ _
      _ ≤ ‖(1/2:ℂ)-(m:ℂ)‖+‖(k:ℂ)‖+‖(t:ℂ)*Complex.I‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖(1/2:ℂ)‖+‖(m:ℂ)‖+‖(k:ℂ)‖+‖(t:ℂ)*Complex.I‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ _ := by simp; linarith
  calc
    _ = ‖Complex.Gamma (z+(2*m:ℕ))/Complex.Gamma z‖ := by
      rw [he,Complex.Gamma_conj,norm_div,norm_div,Complex.norm_conj]
    _ = ‖(ascPochhammer ℂ (2*m)).eval z‖ := congrArg (fun w : ℂ => ‖w‖) hq
    _ ≤ (‖z‖+((2*m:ℕ):ℝ))^(2*m) := metaplectic_ascPochhammer_norm _ _
    _ ≤ ((|k|+3*(m:ℝ)+1)*(1+|t|))^(2*m) := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast
      nlinarith [abs_nonneg k,abs_nonneg t,show (0:ℝ) ≤ m by positivity]
    _ = _ := mul_pow _ _ _

lemma metaplecticGamma_symmetric_factor (ℓ : ℤ) (m : ℕ) (t : ℝ) :
    metaplecticGammaQuotient ℓ ((1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I) =
      (Complex.Gamma ((1/2:ℂ)+(m:ℂ)+((metaplecticAngularShift ℓ-1/6:ℝ):ℂ)-(t:ℂ)*Complex.I) /
       Complex.Gamma ((1/2:ℂ)-(m:ℂ)+((metaplecticAngularShift ℓ-1/6:ℝ):ℂ)+(t:ℂ)*Complex.I)) *
      (Complex.Gamma ((1/2:ℂ)+(m:ℂ)+((metaplecticAngularShift ℓ+1/6:ℝ):ℂ)-(t:ℂ)*Complex.I) /
       Complex.Gamma ((1/2:ℂ)-(m:ℂ)+((metaplecticAngularShift ℓ+1/6:ℝ):ℂ)+(t:ℂ)*Complex.I)) := by
  have hk : (metaplecticAngularShift ℓ:ℂ) = (|ℓ|:ℤ)/2 := by
    simp only [metaplecticAngularShift,Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_ofNat]
  unfold metaplecticGammaQuotient
  have h1 : 5/6+(|ℓ|:ℤ)/2-((1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I) =
      (1/2:ℂ)+(m:ℂ)+((metaplecticAngularShift ℓ-1/6:ℝ):ℂ)-(t:ℂ)*Complex.I := by
    push_cast
    rw [hk]
    ring
  have h2 : 7/6+(|ℓ|:ℤ)/2-((1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I) =
      (1/2:ℂ)+(m:ℂ)+((metaplecticAngularShift ℓ+1/6:ℝ):ℂ)-(t:ℂ)*Complex.I := by
    push_cast
    rw [hk]
    ring
  have h3 : (1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I+(|ℓ|:ℤ)/2-1/6 =
      (1/2:ℂ)-(m:ℂ)+((metaplecticAngularShift ℓ-1/6:ℝ):ℂ)+(t:ℂ)*Complex.I := by
    push_cast
    rw [hk]
    ring
  have h4 : (1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I+(|ℓ|:ℤ)/2+1/6 =
      (1/2:ℂ)-(m:ℂ)+((metaplecticAngularShift ℓ+1/6:ℝ):ℂ)+(t:ℂ)*Complex.I := by
    push_cast
    rw [hk]
    ring
  rw [h1,h2,h3,h4]
  ring

/-- Sharp exponent on the far-left half-integral lines, sufficient for
arbitrary-power angular dual truncation. Constants depend only on ℓ,m. -/
theorem metaplecticGamma_half_integer_bound (ℓ : ℤ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖metaplecticGammaQuotient ℓ ((1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        C*(1+|t|)^(4*m) := by
  let k := metaplecticAngularShift ℓ
  let A := (|k-1/6|+3*(m:ℝ)+1)^(2*m)
  let B := (|k+1/6|+3*(m:ℝ)+1)^(2*m)
  have hA : 0 < A := pow_pos (by positivity) _
  have hB : 0 < B := pow_pos (by positivity) _
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro t
  rw [metaplecticGamma_symmetric_factor,norm_mul]
  have hminus := metaplectic_symmetric_gamma_ratio (k-1/6) m t
  have hplus := metaplectic_symmetric_gamma_ratio (k+1/6) m t
  calc
    _ ≤ (A*(1+|t|)^(2*m))*(B*(1+|t|)^(2*m)) :=
      mul_le_mul hminus hplus (_root_.norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show 4*m = 2*m+2*m by omega,pow_add]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSmoothMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin inversion for the literal arithmetic frequency coefficients.
The coefficient carries one frequency norm, so its Dirichlet variable is
`2*s-1`, exactly as in the theta Gamma completion. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaDirichlet_nonzero (a : Eisenstein→ℂ) (s : ℂ) :
    cubicThetaDirichlet a s = ∑' n : MetaplecticDualArgument,
      a n.val*(‖cubicThetaFrequency n.val‖:ℂ)^(-s) := by
  unfold cubicThetaDirichlet
  have hs : Function.support (fun n : Eisenstein =>
      if n=0 then (0:ℂ) else a n*(‖cubicThetaFrequency n‖:ℂ)^(-s)) ⊆ {n | n≠0} := by
    intro n hn hz
    exact hn (by simp [hz])
  rw [←tsum_subtype_eq_of_support_subset hs]
  apply tsum_congr
  intro n
  exact ite_eq_right n.property

lemma cubicTheta_norm_square_power {r : ℝ} (hr : 0 < r) (s : ℂ) :
    (r:ℂ)*((r^2:ℝ):ℂ)^(-s) = (r:ℂ)^(-(2*s-1)) := by
  rw [Complex.ofReal_pow,←Complex.cpow_nat_mul'
    (by simpa [Complex.arg_ofReal_of_nonneg hr.le] using neg_neg_of_pos Real.pi_pos)
    (by simpa [Complex.arg_ofReal_of_nonneg hr.le] using Real.pi_pos.le)]
  calc
    _ = (r:ℂ)^((1:ℂ)+(2:ℂ)*(-s)) := by
      rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne'),Complex.cpow_one]
      norm_num
    _ = _ := by congr 1; ring

lemma cubicTheta_norm_square_weight {r : ℝ} (hr : 0 < r) (σ : ℝ) :
    r*(r^2)^(-σ) = r^(-(2*σ-1)) := by
  rw [←Real.rpow_natCast r 2,←Real.rpow_mul hr.le]
  calc
    _ = r^(1+(2:ℝ)*(-σ)) := by rw [Real.rpow_add hr,Real.rpow_one]; norm_num
    _ = _ := by congr 1; ring

lemma cubicTheta_normDirichlet (a : Eisenstein→ℂ) (s : ℂ) :
    normDirichletSeries
      (fun n : MetaplecticDualArgument => a n.val*(‖cubicThetaFrequency n.val‖:ℂ))
      (fun n : MetaplecticDualArgument => ‖cubicThetaFrequency n.val‖^2) s =
        cubicThetaDirichlet a (2*s-1) := by
  rw [cubicThetaDirichlet_nonzero]
  unfold normDirichletSeries
  apply tsum_congr
  intro n
  rw [mul_assoc,cubicTheta_norm_square_power (cubicThetaFrequency_pos n.property)]

theorem cubicTheta_smooth_mellin {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ Z : ℝ} (hσ : 3/2<σ) (hZ : 0<Z) :
    (∑' n : MetaplecticDualArgument,
      a n.val*(‖cubicThetaFrequency n.val‖:ℂ)*W (‖cubicThetaFrequency n.val‖^2/Z)) =
    ((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,
      mellin W (σ+(t:ℂ)*Complex.I)*(Z:ℂ)^(σ+(t:ℂ)*Complex.I)*
        cubicThetaDirichlet a (2*(σ+(t:ℂ)*Complex.I)-1) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  have habs := (cubicTheta_mellin_weight_summable hC ha
    (by linarith : 2<2*σ-1)).subtype (fun n : Eisenstein => n≠0)
  have hnorm : Summable (fun n : MetaplecticDualArgument =>
      ‖a n.val*(‖cubicThetaFrequency n.val‖:ℂ)‖*(‖cubicThetaFrequency n.val‖^2)^(-σ)) := by
    convert habs using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    simp only [Function.comp_apply,n.property,ite_false, if_false,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (_root_.norm_nonneg _)]
    rw [mul_assoc,cubicTheta_norm_square_weight (cubicThetaFrequency_pos n.property)]
  have H := smooth_mellin_series
    (fun n : MetaplecticDualArgument => a n.val*(‖cubicThetaFrequency n.val‖:ℂ))
    (fun n : MetaplecticDualArgument => ‖cubicThetaFrequency n.val‖^2)
    (fun n => sq_pos_of_pos (cubicThetaFrequency_pos n.property)) W hW hpos hsm σ hnorm hZ
  simpa only [cubicTheta_normDirichlet] using H

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDirichletIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute interchange for the actual frequency Dirichlet series along
a vertical line. This will be applied to the dual series on a far-left
Mellin contour, where its argument has real part greater than two. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaDirichlet_integral_summable {a : Eisenstein→ℂ} {C σ : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C) (hσ : 2<σ)
    (u : ℝ→ℂ) (hre : ∀ t, (u t).re=σ)
    (H : ℝ→ℂ) (hH : Integrable H) :
    Summable (fun n : MetaplecticDualArgument =>
      a n.val*∫ t : ℝ, H t*(‖cubicThetaFrequency n.val‖:ℂ)^(-u t)) := by
  have hw := (cubicTheta_mellin_weight_summable hC ha hσ).subtype
    (fun n : Eisenstein => n≠0)
  have hw' : Summable (fun n : MetaplecticDualArgument =>
      ‖a n.val‖*‖cubicThetaFrequency n.val‖^(-σ)) := hw.congr (fun n => by
    dsimp only [Function.comp_apply]
    exact ite_eq_right n.property)
  apply (hw'.mul_right (∫ t : ℝ, ‖H t‖)).of_norm_bounded
  intro n
  rw [norm_mul]
  have hbound : ‖∫ t : ℝ, H t*(‖cubicThetaFrequency n.val‖:ℂ)^(-u t)‖ ≤
      ‖cubicThetaFrequency n.val‖^(-σ)*(∫ t : ℝ, ‖H t‖) := by
    rw [←integral_const_mul]
    apply norm_integral_le_of_norm_le (hH.norm.const_mul _)
    filter_upwards with t
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos
      (cubicThetaFrequency_pos n.property),Complex.neg_re,hre]
    exact le_of_eq (mul_comm _ _)
  exact (mul_le_mul_of_nonneg_left hbound (_root_.norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

theorem cubicThetaDirichlet_integral {a : Eisenstein→ℂ} {C σ : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, ‖a n‖ ≤ C) (hσ : 2<σ)
    (u : ℝ→ℂ) (hu : Continuous u) (hre : ∀ t, (u t).re=σ)
    (H : ℝ→ℂ) (hH : Integrable H) :
    (∫ t : ℝ, H t*cubicThetaDirichlet a (u t)) =
      ∑' n : MetaplecticDualArgument,
        a n.val*∫ t : ℝ, H t*(‖cubicThetaFrequency n.val‖:ℂ)^(-u t) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  let F (n : MetaplecticDualArgument) (t : ℝ) : ℂ :=
    H t*(a n.val*(‖cubicThetaFrequency n.val‖:ℂ)^(-u t))
  have hn (n : MetaplecticDualArgument) (t : ℝ) :
      ‖F n t‖=(‖a n.val‖*‖cubicThetaFrequency n.val‖^(-σ))*‖H t‖ := by
    dsimp only [F]
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos
      (cubicThetaFrequency_pos n.property),Complex.neg_re,hre]
    ring
  have hFi (n : MetaplecticDualArgument) : Integrable (F n) := by
    have : NeZero (‖cubicThetaFrequency n.val‖:ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr (cubicThetaFrequency_pos n.property).ne'⟩
    have hc : Continuous (fun t => a n.val*(‖cubicThetaFrequency n.val‖:ℂ)^(-u t)) :=
      continuous_const.mul ((differentiable_const_cpow_of_neZero _).continuous.comp hu.neg)
    exact (hH.norm.const_mul _).mono' (hH.aestronglyMeasurable.mul hc.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun t => (hn n t).le))
  have hw := (cubicTheta_mellin_weight_summable hC ha hσ).subtype
    (fun n : Eisenstein => n≠0)
  have hmass (n : MetaplecticDualArgument) : (∫ t : ℝ, ‖F n t‖) =
      (‖a n.val‖*‖cubicThetaFrequency n.val‖^(-σ))*(∫ t : ℝ, ‖H t‖) := by
    simp_rw [hn]
    rw [integral_const_mul]
  have hsum : Summable (fun n : MetaplecticDualArgument => ∫ t : ℝ, ‖F n t‖) := by
    have hw' : Summable (fun n : MetaplecticDualArgument =>
        ‖a n.val‖*‖cubicThetaFrequency n.val‖^(-σ)) := hw.congr (fun n => by
      dsimp only [Function.comp_apply]
      exact ite_eq_right n.property)
    simpa only [hmass] using hw'.mul_right (∫ t : ℝ, ‖H t‖)
  have hinter := integral_tsum_of_summable_integral_norm hFi hsum
  calc
    _ = ∫ t : ℝ, ∑' n : MetaplecticDualArgument, F n t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [cubicThetaDirichlet_nonzero,tsum_mul_left]
    _ = ∑' n : MetaplecticDualArgument, ∫ t : ℝ, F n t := hinter.symm
    _ = _ := by
      apply tsum_congr
      intro n
      rw [←integral_const_mul]
      congr 1
      funext t
      dsimp [F]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMellinPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact positive-real power bookkeeping for the additive theta transform. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_cpow_affine {r : ℝ} (hr : 0 < r) (j : ℝ) (c s : ℂ) :
    (r:ℂ)^((j:ℂ)*s+c) = (r:ℂ)^c*((r^j:ℝ):ℂ)^s := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_mul_ofReal_nonneg hr.le]
  ring

lemma cubicThetaDualPrefactor_ne_zero {q : Eisenstein} (hq : primary q) :
    cubicThetaDualPrefactor q≠0 := by
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl
      (Complex.ofReal_ne_zero.mpr (cubicThetaLevelScale_pos hq).ne'))
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))

lemma cubicThetaDualScale_pos {q : Eisenstein} (hq : primary q) {Z : ℝ} (hZ : 0<Z) :
    0 < cubicThetaDualScale q Z := by
  unfold cubicThetaDualScale
  positivity [cubicThetaLevelScale_pos hq]

lemma cubicTheta_dual_power {q : Eisenstein} (hq : primary q) {Z r : ℝ}
    (hZ : 0<Z) (hr : 0 < r) (s : ℂ) :
    (Z:ℂ)^s*(cubicThetaLevelScale q:ℂ)^(4*s-2)*
      ((2*Real.pi:ℝ):ℂ)^(4*s-2)*(r:ℂ)^(-(2*(1-s)-1)) =
    (cubicThetaLevelScale q:ℂ)^(-2:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2:ℂ)*(r:ℂ)^(-1:ℂ)*
      ((cubicThetaDualScale q Z*r^2:ℝ):ℂ)^s := by
  have hρ := cubicThetaLevelScale_pos hq
  have hπ : 0<2*Real.pi := by positivity
  have hp (v : ℝ) (hv : 0<v) :
      (v:ℂ)^(4*s-2) = (v:ℂ)^(-2:ℂ)*((v^4:ℝ):ℂ)^s := by
    simpa only [Complex.ofReal_ofNat,Complex.ofReal_neg,sub_eq_add_neg,
      Real.rpow_ofNat] using cubicTheta_cpow_affine hv 4 (-2) s
  have hrp : (r:ℂ)^(-(2*(1-s)-1)) = (r:ℂ)^(-1:ℂ)*((r^2:ℝ):ℂ)^s := by
    have H := cubicTheta_cpow_affine hr 2 (-1) s
    norm_num only [Complex.ofReal_ofNat,Real.rpow_ofNat] at H
    rw [show -(2*(1-s)-1)=(2:ℂ)*s+ -1 by ring]
    exact H
  rw [hp _ hρ,hp _ hπ,hrp]
  have hm (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      ((u*v:ℝ):ℂ)^s=(u:ℂ)^s*(v:ℂ)^s := by
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hu hv]
  simp only [cubicThetaDualScale]
  rw [hm _ _ (by positivity) (sq_nonneg r),
    hm _ _ (by positivity) hZ.le,hm _ _ (by positivity) (by positivity)]
  ring

lemma cubicTheta_archimedean_power {q : Eisenstein} (hq : primary q) {Z : ℝ}
    (hZ : 0<Z) (s : ℂ) :
    (Z:ℂ)^s*(cubicThetaLevelScale q:ℂ)^(4*s-2)*
      ((2*Real.pi:ℝ):ℂ)^(4*s-2) =
        cubicThetaDualPrefactor q*(cubicThetaDualScale q Z:ℂ)^s := by
  simpa only [Complex.ofReal_one,Complex.one_cpow,mul_one,one_pow,
    cubicThetaDualPrefactor] using cubicTheta_dual_power hq hZ (r:=1) zero_lt_one s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTransformContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour motion for the actual angular metaplectic transform. The two
fixed shifted Hecke Gamma strip estimates are the same published Stirling
input already used for the individual Hecke transforms. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplecticGamma_shift_factor (ℓ : ℤ) (s : ℂ) :
    metaplecticGammaQuotient ℓ s =
      angularGammaFEQuotient (metaplecticAngularShift ℓ-1/6) s *
      angularGammaFEQuotient (metaplecticAngularShift ℓ+1/6) s := by
  have hk : (metaplecticAngularShift ℓ:ℂ) = (|ℓ|:ℤ)/2 := by
    simp only [metaplecticAngularShift,Complex.ofReal_div,Complex.ofReal_intCast,
      Complex.ofReal_ofNat]
  unfold metaplecticGammaQuotient angularGammaFEQuotient
  push_cast
  rw [hk]
  have h1 : 1-s+((|ℓ|:ℤ)/2-1/6) = 5/6+(|ℓ|:ℤ)/2-s := by ring
  have h2 : 1-s+((|ℓ|:ℤ)/2+1/6) = 7/6+(|ℓ|:ℤ)/2-s := by ring
  have h3 : s+((|ℓ|:ℤ)/2-1/6) = s+(|ℓ|:ℤ)/2-1/6 := by ring
  have h4 : s+((|ℓ|:ℤ)/2+1/6) = s+(|ℓ|:ℤ)/2+1/6 := by ring
  rw [h1,h2,h3,h4]
  ring

lemma metaplecticGamma_strip_bound (ℓ : ℤ) (a : ℝ)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) a)
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ ∈ Icc a (1/2:ℝ), ∀ t : ℝ,
      ‖metaplecticGammaQuotient ℓ (σ+(t:ℂ)*Complex.I)‖ ≤ C*(1+|t|)^N := by
  obtain ⟨Cm,Nm,hCm,hgm⟩ := hm
  obtain ⟨Cp,Np,hCp,hgp⟩ := hp
  refine ⟨Cm*Cp,Nm+Np,mul_nonneg hCm hCp,?_⟩
  intro σ hσ t
  rw [metaplecticGamma_shift_factor,norm_mul]
  calc
    _ ≤ (Cm*(1+|t|)^Nm)*(Cp*(1+|t|)^Np) :=
      mul_le_mul (hgm σ hσ t) (hgp σ hσ t) (_root_.norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

lemma differentiableOn_metaplecticGammaQuotient (ℓ : ℤ) :
    DifferentiableOn ℂ (metaplecticGammaQuotient ℓ) {s : ℂ | s.re < 5/6} := by
  intro s hs
  have hk : 0 ≤ ((|ℓ|:ℤ):ℝ)/2 := by positivity
  have hreg (c : ℝ) (hc : 5/6 ≤ c) :
      ∀ n : ℕ, (c:ℂ)+(|ℓ|:ℤ)/2-s ≠ -(n:ℂ) := by
    intro n hn
    have he := congrArg Complex.re hn
    simp only [Complex.sub_re,Complex.add_re,Complex.div_ofNat_re,Complex.ofReal_re,
      Complex.intCast_re,Complex.neg_re,Complex.natCast_re] at he
    change s.re < 5/6 at hs
    have hn0 : (0:ℝ) ≤ n := by positivity
    linarith
  have h1 := (Complex.differentiableAt_Gamma ((5/6:ℂ)+(|ℓ|:ℤ)/2-s)
    (by simpa using hreg (5/6) le_rfl)).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => (5/6:ℂ)+(|ℓ|:ℤ)/2-z) s by fun_prop)
  have h2 := (Complex.differentiableAt_Gamma ((7/6:ℂ)+(|ℓ|:ℤ)/2-s)
    (by simpa using hreg (7/6) (by norm_num))).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => (7/6:ℂ)+(|ℓ|:ℤ)/2-z) s by fun_prop)
  have h3 := (Complex.differentiable_one_div_Gamma (s+(|ℓ|:ℤ)/2-1/6)).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => z+(|ℓ|:ℤ)/2-1/6) s by fun_prop)
  have h4 := (Complex.differentiable_one_div_Gamma (s+(|ℓ|:ℤ)/2+1/6)).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => z+(|ℓ|:ℤ)/2+1/6) s by fun_prop)
  convert ((h1.mul h2).mul (h3.mul h4)).differentiableWithinAt using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  dsimp [metaplecticGammaQuotient]
  ring

private lemma metaplectic_scale_strip {a b v : ℝ} (hv : 0 < v)
    {σ : ℝ} (hσ : σ ∈ Icc a b) :
    v^σ ≤ max (v^a) (v^b) := by
  by_cases h : 1 ≤ v
  · exact (Real.rpow_le_rpow_of_exponent_le h hσ.2).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge hv (le_of_not_ge h) hσ.1).trans (le_max_left _ _)

/-- Exact vertical contour move for the transform integrand. The scale
may lie on either side of one. -/
theorem metaplectic_transform_contour (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {a b v : ℝ} (hab : a ≤ b) (hb : b ≤ 1/2)
    (hv : 0 < v)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) a)
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) a) :
    (∫ t : ℝ, (v:ℂ)^((a:ℂ)+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((a:ℂ)+(t:ℂ)*Complex.I)*
      mellin W ((a:ℂ)+(t:ℂ)*Complex.I)) =
    ∫ t : ℝ, (v:ℂ)^((b:ℂ)+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((b:ℂ)+(t:ℂ)*Complex.I)*
      mellin W ((b:ℂ)+(t:ℂ)*Complex.I) := by
  obtain ⟨C,N,hC,hQ⟩ := metaplecticGamma_strip_bound ℓ a hm hp
  let L : ℂ → ℂ := fun s => (v:ℂ)^s*metaplecticGammaQuotient ℓ s
  let D : ℝ := max (v^a) (v^b)*C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hg (σ : ℝ) (hσ : σ ∈ Icc a b) (t : ℝ) :
      ‖L (σ+((t-0:ℝ):ℂ)*Complex.I)‖ ≤ D*(1+|t-0|)^N := by
    simp only [sub_zero]
    dsimp [L]
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    calc
      _ ≤ max (v^a) (v^b)*(C*(1+|t|)^N) :=
        mul_le_mul (metaplectic_scale_strip hv hσ) (hQ σ ⟨hσ.1,hσ.2.trans hb⟩ t)
          (_root_.norm_nonneg _) (by positivity)
      _ = _ := by dsimp [D]; ring
  have : NeZero (v:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hv.ne'⟩
  have hd : DifferentiableOn ℂ L (closedVerticalStrip a b) := by
    apply (differentiable_const_cpow_of_neZero _).differentiableOn.mul
    exact (differentiableOn_metaplecticGammaQuotient ℓ).mono (by
      intro s hs
      exact lt_of_le_of_lt (hs.2.trans hb) (by norm_num))
  let f : ℂ → ℂ := fun s => mellin W s*L s
  have hf : DifferentiableOn ℂ f (closedVerticalStrip a b) :=
    (smooth_mellin_entire W hW hpos hsm.continuous).differentiableOn.mul hd
  obtain ⟨K,_hK,hbound⟩ := norm_mellinHecke_integrand_le W hW hpos hsm
    (Z := 1) (by norm_num) 0 L hD N hg
  have hmajor (σ : ℝ) (hσ : σ ∈ Icc a b) (t : ℝ) :
      ‖f (σ+(t:ℂ)*Complex.I)‖ ≤ mellinEdgeMajorant K t := by
    simpa only [f,sub_zero,Complex.ofReal_one,Complex.one_cpow,mul_one] using hbound σ hσ t
  have hs := mellin_contour_shift_of_majorant hab f hf (mellinEdgeMajorant K)
    (mellinEdgeMajorant_integrable K) (mellinEdgeMajorant_tendsto K).1
    (mellinEdgeMajorant_tendsto K).2 hmajor
  convert hs using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1 <;> funext t <;> dsimp [f,L] <;> ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticKernelIntegrability
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence of the literal metaplectic Mellin kernel, derived
from the proved Gamma strip bound and the smooth weight's rapid decay. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem metaplecticKernel_integrable (ℓ : ℤ) (W : ℝ→ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {a v : ℝ} (ha : a ≤ 1/2) (hv : 0<v) :
    Integrable (fun t : ℝ => (v:ℂ)^(a+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ (a+(t:ℂ)*Complex.I)*
        mellin W (a+(t:ℂ)*Complex.I)) := by
  have hstrip := min_le_left a (1/2:ℝ)
  obtain ⟨C,N,hC,hQ⟩ := metaplecticGamma_strip_bound ℓ (min a (1/2))
    (angularGammaQuotientStripBound_proved _ _ (by linarith [metaplecticAngularShift_nonneg ℓ]))
    (angularGammaQuotientStripBound_proved _ _ (by linarith [metaplecticAngularShift_nonneg ℓ]))
  obtain ⟨Cw,hCw,hw⟩ := smooth_mellin_vertical_decay W hW hpos hsm a (N+2)
  have hg : Continuous (fun t : ℝ => metaplecticGammaQuotient ℓ (a+(t:ℂ)*Complex.I)) :=
    (differentiableOn_metaplecticGammaQuotient ℓ).continuousOn.comp_continuous
      (by fun_prop) (by intro t; change (a+(t:ℂ)*Complex.I).re<5/6; simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]; linarith)
  have : NeZero (v:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hv.ne'⟩
  have hc : Continuous (fun t : ℝ => (v:ℂ)^(a+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ (a+(t:ℂ)*Complex.I)*mellin W (a+(t:ℂ)*Complex.I)) :=
    (((differentiable_const_cpow_of_neZero _).continuous.comp (by fun_prop)).mul hg).mul
      ((smooth_mellin_entire W hW hpos hsm.continuous).continuous.comp (by fun_prop))
  apply (mellinEdgeMajorant_integrable (v^a*C*Cw)).mono' hc.aestronglyMeasurable
  filter_upwards with t
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
  have hr : (a+(t:ℂ)*Complex.I).re=a := by simp
  rw [hr]
  apply (le_div_iff₀ (by positivity : 0<(1+|t|)^2)).mpr
  calc
    _ ≤ (v^a*(C*(1+|t|)^N)*‖mellin W (a+(t:ℂ)*Complex.I)‖)*(1+|t|)^2 := by
      gcongr
      exact hQ a ⟨hstrip,ha⟩ t
    _ = (v^a*C)*((1+|t|)^(N+2)*‖mellin W (a+(t:ℂ)*Complex.I)‖) := by
      rw [pow_add]
      ring
    _ ≤ (v^a*C)*Cw := mul_le_mul_of_nonneg_left (hw t) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDualMellinIntegral
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the actual far-left dual Dirichlet integral into the literal
metaplectic transform, using absolute sum/integral interchange. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaDualMellinKernel_eq {q : Eisenstein} (hq : primary q)
    (ℓ : ℤ) (W : ℝ→ℂ) {Z : ℝ} (hZ : 0<Z) (s : ℂ) :
    cubicThetaDualMellinKernel q ℓ W Z s =
      mellin W s*(Z:ℂ)^s*(cubicThetaLevelScale q:ℂ)^(4*s-2)*
        ((2*Real.pi:ℝ):ℂ)^(4*s-2)*metaplecticGammaQuotient ℓ s := by
  calc
    _ = mellin W s*(cubicThetaDualPrefactor q*(cubicThetaDualScale q Z:ℂ)^s)*
        metaplecticGammaQuotient ℓ s := by unfold cubicThetaDualMellinKernel; ring
    _ = _ := by rw [←cubicTheta_archimedean_power hq hZ]; ring

lemma cubicThetaDualMellinKernel_integrable {q : Eisenstein} (hq : primary q)
    (ℓ : ℤ) (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {A Z : ℝ} (hA : 1/2<A) (hZ : 0<Z) :
    Integrable (fun t : ℝ => cubicThetaDualMellinKernel q ℓ W Z ((-A:ℂ)+(t:ℂ)*Complex.I)) := by
  have H := metaplecticKernel_integrable ℓ W hW hpos hsm (a := -A)
    (v := cubicThetaDualScale q Z) (by linarith) (cubicThetaDualScale_pos hq hZ)
  simpa only [cubicThetaDualMellinKernel,Complex.ofReal_neg] using
    H.const_mul (cubicThetaDualPrefactor q)

lemma cubicThetaDualMellinKernel_frequency {q : Eisenstein} (hq : primary q)
    (ℓ : ℤ) (W : ℝ→ℂ) {Z r : ℝ} (hZ : 0<Z) (hr : 0 < r) (s : ℂ) :
    cubicThetaDualMellinKernel q ℓ W Z s*(r:ℂ)^(-(2*(1-s)-1)) =
      (cubicThetaDualPrefactor q*(r:ℂ)^(-1:ℂ))*
        (((cubicThetaDualScale q Z*r^2:ℝ):ℂ)^s*metaplecticGammaQuotient ℓ s*mellin W s) := by
  have hp := cubicTheta_dual_power hq hZ hr s
  rw [cubicTheta_archimedean_power hq hZ] at hp
  change cubicThetaDualPrefactor q*(cubicThetaDualScale q Z:ℂ)^s*
    (r:ℂ)^(-(2*(1-s)-1)) =
      cubicThetaDualPrefactor q*(r:ℂ)^(-1:ℂ)*
        ((cubicThetaDualScale q Z*r^2:ℝ):ℂ)^s at hp
  calc
    _ = (cubicThetaDualPrefactor q*(cubicThetaDualScale q Z:ℂ)^s*
        (r:ℂ)^(-(2*(1-s)-1)))*(metaplecticGammaQuotient ℓ s*mellin W s) := by
      unfold cubicThetaDualMellinKernel
      ring
    _ = _ := by rw [hp]; ring

lemma cubicThetaDualMellinKernel_frequency_integral {q : Eisenstein} (hq : primary q)
    (ℓ : ℤ) (W : ℝ→ℂ) {A Z r : ℝ} (hZ : 0<Z) (hr : 0 < r) :
    (∫ t : ℝ, cubicThetaDualMellinKernel q ℓ W Z ((-A:ℂ)+(t:ℂ)*Complex.I)*
      (r:ℂ)^(-(2*(1-((-A:ℂ)+(t:ℂ)*Complex.I))-1))) =
      (cubicThetaDualPrefactor q*(r:ℂ)^(-1:ℂ))*
        ∫ t : ℝ, ((cubicThetaDualScale q Z*r^2:ℝ):ℂ)^((-A:ℂ)+(t:ℂ)*Complex.I)*
          metaplecticGammaQuotient ℓ ((-A:ℂ)+(t:ℂ)*Complex.I)*
            mellin W ((-A:ℂ)+(t:ℂ)*Complex.I) := by
  simp_rw [cubicThetaDualMellinKernel_frequency hq ℓ W hZ hr]
  rw [integral_const_mul]

theorem cubicTheta_dual_mellin_integral {q : Eisenstein} (hq : primary q)
    {a : Eisenstein→ℂ} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    (ℓ : ℤ) (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {A Z : ℝ} (hA : 1/2<A) (hZ : 0<Z) :
    ((1/(2*Real.pi):ℝ):ℂ)*(∫ t : ℝ,
      mellin W ((-A:ℂ)+(t:ℂ)*Complex.I)*(Z:ℂ)^((-A:ℂ)+(t:ℂ)*Complex.I)*
        (cubicThetaLevelScale q:ℂ)^(4*((-A:ℂ)+(t:ℂ)*Complex.I)-2)*
        ((2*Real.pi:ℝ):ℂ)^(4*((-A:ℂ)+(t:ℂ)*Complex.I)-2)*
        metaplecticGammaQuotient ℓ ((-A:ℂ)+(t:ℂ)*Complex.I)*
        cubicThetaDirichlet a (2*(1-((-A:ℂ)+(t:ℂ)*Complex.I))-1)) =
      cubicThetaDualPrefactor q*∑' n : MetaplecticDualArgument,
        a n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
          metaplecticTransform ℓ W A
            (cubicThetaDualScale q Z*‖cubicThetaFrequency n.val‖^2) := by
  let H (t : ℝ) : ℂ := cubicThetaDualMellinKernel q ℓ W Z ((-A:ℂ)+(t:ℂ)*Complex.I)
  have hInt := cubicThetaDirichlet_integral hC ha (by linarith : 2<1+2*A)
    (fun t => 2*(1-((-A:ℂ)+(t:ℂ)*Complex.I))-1) (by fun_prop)
    (by intro t; simp; ring) H
    (cubicThetaDualMellinKernel_integrable hq ℓ W hW hpos hsm hA hZ)
  calc
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∫ t : ℝ,
        H t*cubicThetaDirichlet a (2*(1-((-A:ℂ)+(t:ℂ)*Complex.I))-1)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [H]
      rw [cubicThetaDualMellinKernel_eq hq ℓ W hZ]
    _ = ((1/(2*Real.pi):ℝ):ℂ)*∑' n : MetaplecticDualArgument,
        a n.val*∫ t : ℝ, H t*(‖cubicThetaFrequency n.val‖:ℂ)^
          (-(2*(1-((-A:ℂ)+(t:ℂ)*Complex.I))-1)) := by rw [hInt]
    _ = _ := by
      rw [←tsum_mul_left,←tsum_mul_left]
      apply tsum_congr
      intro n
      dsimp only [H]
      rw [cubicThetaDualMellinKernel_frequency_integral hq ℓ W hZ
        (cubicThetaFrequency_pos n.property),metaplecticTransform,Complex.cpow_neg_one]
      simp only [Complex.ofReal_neg]
      ring

theorem cubicTheta_dual_mellin_summable {q : Eisenstein} (hq : primary q)
    {a : Eisenstein→ℂ} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    (ℓ : ℤ) (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {A Z : ℝ} (hA : 1/2<A) (hZ : 0<Z) :
    Summable (fun n : MetaplecticDualArgument => a n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
      metaplecticTransform ℓ W A (cubicThetaDualScale q Z*‖cubicThetaFrequency n.val‖^2)) := by
  have H := cubicThetaDirichlet_integral_summable hC ha (by linarith : 2<1+2*A)
    (fun t => 2*(1-((-A:ℂ)+(t:ℂ)*Complex.I))-1) (by intro t; simp; ring)
    (fun t => cubicThetaDualMellinKernel q ℓ W Z ((-A:ℂ)+(t:ℂ)*Complex.I))
    (cubicThetaDualMellinKernel_integrable hq ℓ W hW hpos hsm hA hZ)
  have H' : Summable (fun n : MetaplecticDualArgument => cubicThetaDualPrefactor q*
      (a n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
        metaplecticTransform ℓ W A (cubicThetaDualScale q Z*‖cubicThetaFrequency n.val‖^2))) :=
    (H.mul_left ((1/(2*Real.pi):ℝ):ℂ)).congr (fun n => by
    rw [cubicThetaDualMellinKernel_frequency_integral hq ℓ W hZ
      (cubicThetaFrequency_pos n.property),Complex.cpow_neg_one]
    rw [metaplecticTransform]
    simp only [Complex.ofReal_neg]
    ring)
  exact (summable_mul_left_iff (cubicThetaDualPrefactor_ne_zero hq)).mp H'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoefficientMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial Mellin identity for the actual selected and projected
coefficient families, with their horizontal phases retained. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCoefficientTwist_norm (a : Eisenstein→ℂ) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaCoefficientTwist a z n‖=‖a n‖ := by
  simp only [cubicThetaCoefficientTwist,norm_mul,Circle.norm_coe,mul_one]

lemma cubicThetaCoefficientTwist_angular_series (a : Eisenstein→ℂ) (z : ℂ) (v : ℝ) (ℓ : ℤ) :
    cubicThetaNonconstant (cubicThetaAngularCoefficient (cubicThetaCoefficientTwist a z) ℓ) (0,v)=
      cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,v) := by
  classical
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp only [cubicThetaSeriesTerm,hn,ite_true, if_true]
  · simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,cubicThetaCoefficientTwist,
      cubicThetaAngularCoefficient,tracePair,mul_zero,Complex.zero_re,
      AddChar.map_zero_eq_one,Circle.coe_one,mul_one]
    ring

theorem cubicThetaCoefficient_mellin {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n,‖a n‖≤C) (z : ℂ) (ℓ : ℤ) {s : ℂ} (hs : 3/2 < s.re) :
    mellin (fun v : ℝ => cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,v))
      (2*s+(ℓ.natAbs:ℂ)-1)=
      (1/4:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2*(s+(ℓ.natAbs:ℂ)/2))*
        Complex.Gamma (s+(ℓ.natAbs:ℂ)/2+1/6)*Complex.Gamma (s+(ℓ.natAbs:ℂ)/2-1/6)*
          cubicThetaDirichlet (fun n => theta ℓ n*cubicThetaCoefficientTwist a z n) (2*s-1) := by
  simp_rw [←cubicThetaCoefficientTwist_angular_series a z]
  exact cubicThetaAngular_completed hC
    (fun n => (cubicThetaCoefficientTwist_norm a z n).trans_le (ha n)) ℓ hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBoundedScaledMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entire upper Mellin tails at a positive scale, for the two bounded coefficient families in the actual projected transformation. -/
noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaBoundedScaledUpper_locallyIntegrable {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    LocallyIntegrable (thetaUpper (cubicThetaBoundedScaledAxis a ℓ z r)) := by
  let g : ℝ→ℂ := fun t => cubicThetaNonconstant
    (cubicThetaAngularCoefficient a ℓ) (z,r*max (1/2) t)
  have hg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (cubicThetaAngular_continuousAt hC
      ha ℓ (by positivity : 0 < r*max (1/2) t)).comp
    fun_prop
  have he : thetaUpper (cubicThetaBoundedScaledAxis a ℓ z r)=(Ioi 1).indicator g := by
    funext t
    by_cases ht : 1<t
    · simp only [thetaUpper,indicator_of_mem (show t∈Ioi (1:ℝ) from ht),cubicThetaBoundedScaledAxis,g,
        max_eq_right (by linarith : (1/2:ℝ)≤t)]
    · simp only [thetaUpper,indicator_of_notMem (show t∉Ioi (1:ℝ) from ht)]
  rw [he]
  exact hg.locallyIntegrable.indicator measurableSet_Ioi

lemma cubicThetaBoundedScaledUpper_isBigO {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    thetaUpper (cubicThetaBoundedScaledAxis a ℓ z r) =O[atTop]
      (fun t : ℝ => Real.exp (-(Real.pi/18*r)*t)) := by
  apply IsBigO.of_bound (cubicThetaAngularExpConstant C ℓ)
  filter_upwards [eventually_ge_atTop (max 2 r⁻¹)] with t ht
  have ht1 : 1<t := by linarith [le_trans (le_max_left (2:ℝ) r⁻¹) ht]
  have hrt : 1 ≤ r*t := by
    have hi : r⁻¹≤t := le_trans (le_max_right (2:ℝ) r⁻¹) ht
    have h := mul_le_mul_of_nonneg_left hi hr.le
    simpa only [mul_inv_cancel₀ hr.ne'] using h
  rw [thetaUpper,indicator_of_mem (show t∈Ioi (1:ℝ) from ht1),cubicThetaBoundedScaledAxis,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  simpa only [mul_assoc,neg_mul] using
    cubicThetaAngular_exponential_bound hC
      ha ℓ hrt z

lemma cubicThetaBoundedScaledUpper_small (a : Eisenstein→ℂ) (ℓ : ℤ) (z : ℂ) (r : ℝ) (s : ℂ) :
    thetaUpper (cubicThetaBoundedScaledAxis a ℓ z r) =O[𝓝[>] 0]
      (fun t : ℝ => t^(-(s.re-1))) := by
  apply IsBigO.of_bound 0
  filter_upwards [(eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  rw [thetaUpper,indicator_of_notMem (show t∉Ioi (1:ℝ) from not_lt.mpr ht.le),norm_zero]
  simp

theorem cubicThetaBoundedScaledUpper_mellinConvergent {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (z : ℂ) {r : ℝ}
    (hr : 0 < r) (s : ℂ) : MellinConvergent (thetaUpper (cubicThetaBoundedScaledAxis a ℓ z r)) s := by
  exact mellinConvergent_of_isBigO_rpow_exp (by positivity : 0<Real.pi/18*r)
    ((cubicThetaBoundedScaledUpper_locallyIntegrable hC ha ℓ z hr).locallyIntegrableOn _)
    (cubicThetaBoundedScaledUpper_isBigO hC ha ℓ z hr) (cubicThetaBoundedScaledUpper_small a ℓ z r s)
    (by linarith)

theorem cubicThetaBoundedScaledUpper_entire {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Differentiable ℂ (mellin (thetaUpper (cubicThetaBoundedScaledAxis a ℓ z r))) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp (by positivity : 0<Real.pi/18*r)
    ((cubicThetaBoundedScaledUpper_locallyIntegrable hC ha ℓ z hr).locallyIntegrableOn _)
    (cubicThetaBoundedScaledUpper_isBigO hC ha ℓ z hr) (cubicThetaBoundedScaledUpper_small a ℓ z r s)
    (by linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite primary projector gives an explicit dual coefficient
family, with absolute convergence and its actual constant term. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaProjectedCuspMultiplier_norm (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (j : Fin 3) :
    ‖cubicThetaProjectedCuspMultiplier g hc j‖=1 := cubicThetaKubotaValue_norm _

lemma cubicThetaProjectedCoefficient_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (k : Eisenstein) :
    ‖cubicThetaProjectedCoefficient g hc k‖≤243 := by
  have hω : ‖omega‖=1 := by
    have he := cubicTheta_unit_norm
      (Units.mkOfMulEqOne omegaE (omegaE^2) (by rw [mul_comm,←pow_succ,omegaE_cube]))
    exact he
  have hterm (j : Fin 3) :
      ‖omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
        star (cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j) (-k))‖≤243 := by
    simp only [norm_mul,norm_pow,norm_star,hω,one_pow,
      cubicThetaProjectedCuspMultiplier_norm,one_mul]
    exact cubicThetaActualCuspCoefficient_bound _ _
  rw [cubicThetaProjectedCoefficient,norm_div,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<3)).mpr
  calc
    _ ≤ ∑ j : Fin 3, ‖omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
        star (cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j) (-k))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, (243:ℝ) := Finset.sum_le_sum (fun j _ => hterm j)
    _ = _ := by norm_num

lemma cubicThetaNonconstant_three (a : Fin 3→Eisenstein→ℂ) (w : Fin 3→ℂ)
    (z : ℂ) (v : ℝ) (hs : ∀ j, Summable (cubicThetaSeriesTerm (a j) z v)) :
    cubicThetaNonconstant (fun k => (∑ j : Fin 3,w j*a j k)/3) (z,v)=
      (∑ j : Fin 3,w j*cubicThetaNonconstant (a j) (z,v))/3 := by
  have ht (k : Eisenstein) :
      cubicThetaSeriesTerm (fun k => (∑ j : Fin 3,w j*a j k)/3) z v k=
        (∑ j : Fin 3,w j*cubicThetaSeriesTerm (a j) z v k)/3 := by
    by_cases hk : k=0
    · simp [cubicThetaSeriesTerm,hk]
    · simp only [cubicThetaSeriesTerm,ite_eq_right hk]
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
      simp_rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
  unfold cubicThetaNonconstant
  simp_rw [ht]
  rw [tsum_div_const,Summable.tsum_finsetSum (fun j _ => (hs j).mul_left (w j))]
  simp_rw [tsum_mul_left]

lemma cubicThetaProjectedCoefficient_series (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc) (z,v)=
      (∑ j : Fin 3,omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
        cubicThetaNonconstant
          (fun k => star (cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j) (-k)))
          (z,v))/3 := by
  apply cubicThetaNonconstant_three
  intro j
  apply cubicThetaSeries_summable (by norm_num : (0:ℝ)≤243) _ hv z
  intro k hk
  rw [norm_star]
  exact (cubicThetaActualCuspCoefficient_bound _ _).trans
    (le_mul_of_one_le_right (by norm_num) (one_le_norm hk))

theorem cubicThetaNormalizedPrimaryProjection_expansion (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (p : CubicThetaPoint) :
    cubicThetaNonconstant cubicThetaSelectedCoefficient (g • p).val=
      cubicThetaProjectedConstant g hc*((p.val.2^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc)
          (p.val.1+(g 1 1:ℂ),p.val.2) := by
  have hp : (cubicThetaFullTranslation (g 1 1) • p).val=
      (p.val.1+(g 1 1:ℂ),p.val.2) := by
    rw [cubicThetaFullPointAction_apply,cubicThetaFullTranslation_complex,cubicThetaMobius_translation]
  rw [cubicThetaNormalizedPrimaryProjection_cusps g hc p,hp,
    cubicThetaProjectedCoefficient_series g hc _ p.property]
  have ht (j : Fin 3) : omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j*
      cubicThetaCuspExpansion (cubicThetaProjectedCuspType g j)
        (p.val.1+(g 1 1:ℂ),p.val.2))=
      omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
        star (cubicThetaActualCuspConstant (cubicThetaProjectedCuspType g j))*
          ((p.val.2^(2/3:ℝ):ℝ):ℂ)+
      omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
        cubicThetaNonconstant
          (fun k => star (cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j) (-k)))
          (p.val.1+(g 1 1:ℂ),p.val.2) := by
    rw [star_mul,cubicThetaCuspExpansion_conjugate]
    dsimp only [Prod.snd]
    ring
  simp_rw [ht]
  rw [Finset.sum_add_distrib,add_div]
  congr 1
  rw [←Finset.sum_mul]
  unfold cubicThetaProjectedConstant
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryBruhat
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational-cusp geometry for the actual primary projector. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimaryBruhat_identity (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) :
    cubicThetaFullComplex g=
      cubicThetaTranslationMatrix ((g 0 0:ℂ)/(g 1 0:ℂ))*
        cubicThetaInversionMatrix (g 1 0:ℂ)
          (fun he => primary_ne_zero hc (Subtype.ext he))*
        cubicThetaTranslationMatrix ((g 1 1:ℂ)/(g 1 0:ℂ)) := by
  have hq : (g 1 0:ℂ)≠0 := fun he => primary_ne_zero hc (Subtype.ext he)
  have hg : (g 0 0:ℂ)*(g 1 1:ℂ)-(g 0 1:ℂ)*(g 1 0:ℂ)=1 := by
    have he : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
      simpa only [Matrix.det_fin_two] using g.property
    exact_mod_cast he
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  change (g i j:ℂ)=
    (((!![1,(g 0 0:ℂ)/(g 1 0:ℂ);0,1] : Matrix (Fin 2) (Fin 2) ℂ)*
      !![0,-(g 1 0:ℂ)⁻¹;(g 1 0:ℂ),0])*!![1,(g 1 1:ℂ)/(g 1 0:ℂ);0,1]) i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [hq]
  all_goals first | (solve | ring) | linear_combination -hg

lemma cubicThetaPrimaryBruhat_point (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (p : CubicThetaPoint) :
    (g • p).val=
      ((cubicThetaInversion (g 1 0:ℂ) (p.val.1+(g 1 1:ℂ)/(g 1 0:ℂ),p.val.2)).1+
          (g 0 0:ℂ)/(g 1 0:ℂ),
        (cubicThetaInversion (g 1 0:ℂ) (p.val.1+(g 1 1:ℂ)/(g 1 0:ℂ),p.val.2)).2) := by
  have hq : (g 1 0:ℂ)≠0 := fun he => primary_ne_zero hc (Subtype.ext he)
  rw [cubicThetaFullPointAction_apply,cubicThetaPrimaryBruhat_identity g hc,
    ←cubicThetaMobius_comp _ _ p.property]
  rw [←cubicThetaMobius_comp _ _ (cubicThetaMobius_height_pos _ p.property),
    cubicThetaMobius_translation]
  rw [cubicThetaMobius_translation ((g 1 1:ℂ)/(g 1 0:ℂ)) p.val,
    cubicThetaMobius_inversion (p := (p.val.1+(g 1 1:ℂ)/(g 1 0:ℂ),p.val.2)) hq p.property]

theorem cubicThetaSelected_primary_cusp (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaNonconstant cubicThetaSelectedCoefficient
      ((cubicThetaInversion (g 1 0:ℂ) (z,v)).1+(g 0 0:ℂ)/(g 1 0:ℂ),
        (cubicThetaInversion (g 1 0:ℂ) (z,v)).2)=
      cubicThetaProjectedConstant g hc*((v^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc)
          (z-(g 1 1:ℂ)/(g 1 0:ℂ)+(g 1 1:ℂ),v) := by
  let p : CubicThetaPoint := ⟨(z-(g 1 1:ℂ)/(g 1 0:ℂ),v),hv⟩
  have hp := cubicThetaPrimaryBruhat_point g hc p
  dsimp only [p,Prod.fst,Prod.snd] at hp
  rw [sub_add_cancel] at hp
  have he := cubicThetaNormalizedPrimaryProjection_expansion g hc p
  rw [hp] at he
  exact he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedPlane
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual projected cusp expansion supports the same angular
extraction as the original theta series, with its own literal coefficients. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaProjectedCoefficient_arithmetic_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (n : Eisenstein) (hn : n≠0) :
    ‖cubicThetaProjectedCoefficient g hc n‖≤243*norm n :=
  (cubicThetaProjectedCoefficient_bound g hc n).trans
    (le_mul_of_one_le_right (by norm_num) (one_le_norm hn))

lemma cubicThetaSelected_projected_plane (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaNonconstant cubicThetaSelectedCoefficient
      ((cubicThetaInversion (g 1 0:ℂ) (z,v)).1+cubicThetaPrimaryCuspCenter g,
        (cubicThetaInversion (g 1 0:ℂ) (z,v)).2)=
      cubicThetaProjectedPlane g hc (z+cubicThetaPrimaryDualCenter g,v) := by
  have he := cubicThetaSelected_primary_cusp g hc z hv
  have hz : z-(g 1 1:ℂ)/(g 1 0:ℂ)+(g 1 1:ℂ)=z+cubicThetaPrimaryDualCenter g := by
    unfold cubicThetaPrimaryDualCenter
    ring
  rw [hz] at he
  exact he

attribute [local instance] OAI.CubicFirstMoment.instFactLtRealOfNat_solutions_9
lemma cubicThetaProjectedPlane_circle_coefficient (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (z d : ℂ) {v : ℝ} (hv : 0<v)
    (r : ℝ) (rev : Bool) {k : ℕ} (hk : 0<k) :
    fourierCoeff (fun t => cubicThetaProjectedPlane g hc
      (z+cubicThetaSignedCircle rev d r t,v)) (k:ℤ)=
      fourierCoeff (fun t => cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc)
        (z+cubicThetaSignedCircle rev d r t,v)) (k:ℤ) := by
  have hs := cubicThetaSeries_summable (by norm_num : (0:ℝ)≤243)
    (cubicThetaProjectedCoefficient_arithmetic_bound g hc) hv z
  have hf : Continuous (fun t => cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc)
      (z+cubicThetaSignedCircle rev d r t,v)) := by
    rw [cubicThetaCircleActual_series]
    exact cubicThetaCircleSeries_continuous hs.norm r
  change fourierCoeff (fun t => cubicThetaProjectedConstant g hc*((v^(2/3:ℝ):ℝ):ℂ)+
    cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc)
      (z+cubicThetaSignedCircle rev d r t,v)) (k:ℤ)=_
  exact cubicThetaCircle_coefficient_const_add _
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (by exact_mod_cast hk.ne')

theorem cubicThetaProjectedPlane_circle_limit (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (z : ℂ) (rev : Bool) {k : ℕ} (hk : 0<k)
    {d : ℝ→ℂ} {v : ℝ→ℝ} {d₀ : ℂ} {v₀ : ℝ}
    (hd : Tendsto d (𝓝[Set.Ioi 0] 0) (𝓝 d₀))
    (hv : Tendsto v (𝓝[Set.Ioi 0] 0) (𝓝 v₀)) (hv₀ : 0<v₀) :
    Tendsto (fun r : ℝ => fourierCoeff
      (fun t => cubicThetaProjectedPlane g hc (z+cubicThetaSignedCircle rev (d r) r t,v r))
        (k:ℤ)/(r:ℂ)^k) (𝓝[Set.Ioi 0] 0)
      (𝓝 (((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(cubicThetaCircleMultiplier rev d₀)^k*
        cubicThetaNonconstant
          (cubicThetaAngularCoefficient (cubicThetaProjectedCoefficient g hc)
            (cubicThetaCircleOrder rev k)) (z,v₀))) := by
  have H := cubicThetaCircleActual_limit (by norm_num : (0:ℝ)≤243)
    (cubicThetaProjectedCoefficient_arithmetic_bound g hc) z rev k hd hv hv₀
  apply H.congr'
  filter_upwards [hv.eventually (lt_mem_nhds hv₀)] with r hr
  rw [cubicThetaProjectedPlane_circle_coefficient g hc z (d r) hr r rev hk]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedAngular
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All nonzero angular orders of the actual primary-projected cusp
transformation. No Voronoi identity is assumed. -/
noncomputable section
open Filter
open scoped Topology MatrixGroups
namespace CubicFirstMoment

local instance instFactLtRealOfNat_solutions_10 : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

theorem cubicThetaSelected_projected_angular (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {v : ℝ} (hv : 0<v)
    (rev : Bool) {k : ℕ} (hk : 0<k) :
    cubicThetaNonconstant
      (cubicThetaAngularCoefficient (cubicThetaProjectedCoefficient g hc) (cubicThetaCircleOrder rev k))
        (cubicThetaPrimaryDualCenter g,v)=
      (cubicThetaCircleMultiplier (!rev) (-1/((g 1 0:ℂ)^2*(v:ℂ)^2)))^k*
        cubicThetaNonconstant
          (cubicThetaAngularCoefficient cubicThetaSelectedCoefficient (cubicThetaCircleOrder (!rev) k))
            (cubicThetaPrimaryCuspCenter g,(norm (g 1 0)*v)⁻¹) := by
  let z := cubicThetaPrimaryDualCenter g
  let z' := cubicThetaPrimaryCuspCenter g
  let q : ℂ := (g 1 0:ℂ)
  let fl := fun r : ℝ => fourierCoeff
    (fun t => cubicThetaProjectedPlane g hc (z+cubicThetaSignedCircle rev 1 r t,v)) (k:ℤ)/(r:ℂ)^k
  let fr := fun r : ℝ => fourierCoeff
    (fun t => cubicThetaNonconstant cubicThetaSelectedCoefficient
      (z'+cubicThetaSignedCircle (!rev) (cubicThetaCircleDualDirection q v r) r t,
        cubicThetaCircleDualHeight q v r)) (k:ℤ)/(r:ℂ)^k
  have hq : q≠0 := fun he => primary_ne_zero hc (Subtype.ext he)
  have heq (r : ℝ) : fr r=fl r := by
    have he : (fun t => cubicThetaNonconstant cubicThetaSelectedCoefficient
        (z'+cubicThetaSignedCircle (!rev) (cubicThetaCircleDualDirection q v r) r t,
          cubicThetaCircleDualHeight q v r))=
        fun t => cubicThetaProjectedPlane g hc (z+cubicThetaSignedCircle rev 1 r t,v) := by
      funext t
      have H := cubicThetaSelected_projected_plane g hc (cubicThetaSignedCircle rev 1 r t) hv
      rw [cubicThetaInversion_circle] at H
      simpa only [Prod.fst,Prod.snd,add_comm,z,z',q] using H
    dsimp only [fr,fl]
    rw [he]
  let A := (2*Real.pi*Complex.I)^k/(k.factorial:ℂ)
  have hl : Tendsto fl (𝓝[Set.Ioi 0] 0)
      (𝓝 (A*cubicThetaNonconstant
        (cubicThetaAngularCoefficient (cubicThetaProjectedCoefficient g hc) (cubicThetaCircleOrder rev k))
        (z,v))) := by
    have H := cubicThetaProjectedPlane_circle_limit g hc z rev hk
      (d := fun _ : ℝ => (1:ℂ)) (v := fun _ : ℝ => v) tendsto_const_nhds tendsto_const_nhds hv
    have hm : cubicThetaCircleMultiplier rev 1=1 := by cases rev <;> simp [cubicThetaCircleMultiplier]
    simpa only [hm,one_pow,mul_one,A,fl] using H
  have hbound (n : Eisenstein) (hn : n≠0) : ‖cubicThetaSelectedCoefficient n‖≤81*norm n :=
    (cubicThetaSelectedCoefficient_norm n).trans
      (le_mul_of_one_le_right (by norm_num) (one_le_norm hn))
  have hr : Tendsto fr (𝓝[Set.Ioi 0] 0)
      (𝓝 (A*(cubicThetaCircleMultiplier (!rev) (-1/(q^2*(v:ℂ)^2)))^k*
        cubicThetaNonconstant
          (cubicThetaAngularCoefficient cubicThetaSelectedCoefficient (cubicThetaCircleOrder (!rev) k))
            (z',(norm (g 1 0)*v)⁻¹))) := by
    have H := cubicThetaCircleActual_limit (by norm_num : (0:ℝ)≤81) hbound z' (!rev) k
      (cubicThetaCircleDualDirection_limit hq hv) (cubicThetaCircleDualHeight_limit hq hv)
      (inv_pos.mpr (mul_pos (norm_pos_of_ne_zero (primary_ne_zero hc)) hv))
    simpa only [norm,A,fr,q] using H
  have he := tendsto_nhds_unique hr (hl.congr' (Eventually.of_forall (fun r => (heq r).symm)))
  have hA : A≠0 := by
    apply div_ne_zero
    · apply pow_ne_zero
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    · exact_mod_cast Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hA
  change A*cubicThetaNonconstant
    (cubicThetaAngularCoefficient (cubicThetaProjectedCoefficient g hc) (cubicThetaCircleOrder rev k)) (z,v)=_
  calc
    _ = A*(cubicThetaCircleMultiplier (!rev) (-1/(q^2*(v:ℂ)^2)))^k*
      cubicThetaNonconstant
        (cubicThetaAngularCoefficient cubicThetaSelectedCoefficient (cubicThetaCircleOrder (!rev) k))
          (z',(norm (g 1 0)*v)⁻¹) := he.symm
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedAngularMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entire Mellin continuation for the two actual coefficient families
in the primary-projected rational-cusp transformation. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaSelectedCoefficient_arithmetic_bound (n : Eisenstein) (hn : n≠0) :
    ‖cubicThetaSelectedCoefficient n‖≤81*norm n :=
  (cubicThetaSelectedCoefficient_norm n).trans
    (le_mul_of_one_le_right (by norm_num) (one_le_norm hn))

theorem cubicThetaProjectedAngularAxis_functional (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {t : ℝ} (ht : 0<t) :
    cubicThetaProjectedAngularAxis g hc rev k (1/t)=
      cubicThetaLevelAngularRoot (g 1 0) rev k*(t:ℂ)^(2*k)*
        cubicThetaSelectedAngularAxis g rev k t := by
  have hv := mul_pos (cubicThetaLevelScale_pos hc) (inv_pos.mpr ht)
  have H := cubicThetaSelected_projected_angular g hc hv rev hk
  rw [cubicThetaLevelScale_reciprocal hc (inv_pos.mpr ht),inv_inv,
    cubicThetaLevelAngular_scaled_direction hc ht,cubicThetaCircleMultiplier_real_mul] at H
  simpa only [cubicThetaProjectedAngularAxis,cubicThetaSelectedAngularAxis,
    cubicThetaBoundedScaledAxis,cubicThetaLevelAngularRoot,one_div,mul_pow,pow_mul,mul_assoc] using H

theorem cubicThetaProjectedAngular_mellin (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k) (s : ℂ) :
    MellinConvergent (cubicThetaProjectedAngularAxis g hc rev k) s ∧
      mellin (cubicThetaProjectedAngularAxis g hc rev k) s=
        cubicThetaProjectedAngularCompleted g hc rev k s := by
  apply theta_mellin_split_angular k
    (fun t ht => cubicThetaProjectedAngularAxis_functional g hc rev hk ht)
  · exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤243)
      (cubicThetaProjectedCoefficient_arithmetic_bound g hc) _ _ (cubicThetaLevelScale_pos hc) s
  · exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤81)
      cubicThetaSelectedCoefficient_arithmetic_bound _ _ (cubicThetaLevelScale_pos hc) _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSelectedAngularMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse reciprocal law gives entire Mellin continuation for the
actual selected coefficients as well as for the projected dual family. -/
noncomputable section
open MeasureTheory Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaLevelAngularRoot_ne_zero {q : Eisenstein} (hq : primary q)
    (rev : Bool) (k : ℕ) : cubicThetaLevelAngularRoot q rev k≠0 := by
  have hqC : (q:ℂ)≠0 := fun he => primary_ne_zero hq (Subtype.ext he)
  have hN : (norm q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero (primary_ne_zero hq)).ne'
  have hd : -(norm q:ℂ)/(q:ℂ)^2≠0 := div_ne_zero (neg_ne_zero.mpr hN) (pow_ne_zero _ hqC)
  unfold cubicThetaLevelAngularRoot
  apply pow_ne_zero
  cases rev <;> simpa only [Bool.not_false,Bool.not_true,cubicThetaCircleMultiplier,
    Bool.false_eq_true,ite_false, if_false,ite_true, if_true,ne_eq,star_eq_zero] using hd

lemma cubicThetaSelectedAngularAxis_functional (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {t : ℝ} (ht : 0<t) :
    cubicThetaSelectedAngularAxis g rev k (1/t)=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*(t:ℂ)^(2*k)*
        cubicThetaProjectedAngularAxis g hc rev k t := by
  have he := cubicThetaProjectedAngularAxis_functional g hc rev hk (inv_pos.mpr ht)
  simp only [one_div,inv_inv,Complex.ofReal_inv,inv_pow] at he
  have hr := cubicThetaLevelAngularRoot_ne_zero hc rev k
  have htC : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [one_div]
  field_simp [hr,htC] at he ⊢
  exact he.symm

theorem cubicThetaSelectedAngular_mellin (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k) (s : ℂ) :
    MellinConvergent (cubicThetaSelectedAngularAxis g rev k) s ∧
      mellin (cubicThetaSelectedAngularAxis g rev k) s=
        cubicThetaSelectedAngularCompleted g hc rev k s := by
  apply theta_mellin_split_angular k
    (fun t ht => cubicThetaSelectedAngularAxis_functional g hc rev hk ht)
  · exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤81)
      cubicThetaSelectedCoefficient_arithmetic_bound _ _ (cubicThetaLevelScale_pos hc) s
  · exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤243)
      (cubicThetaProjectedCoefficient_arithmetic_bound g hc) _ _ (cubicThetaLevelScale_pos hc) _

theorem cubicThetaSelectedAngularCompleted_entire (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) :
    Differentiable ℂ (cubicThetaSelectedAngularCompleted g hc rev k) := by
  have hf := cubicThetaBoundedScaledUpper_entire (by norm_num : (0:ℝ)≤81)
    cubicThetaSelectedCoefficient_arithmetic_bound (cubicThetaCircleOrder (!rev) k)
    (cubicThetaPrimaryCuspCenter g) (cubicThetaLevelScale_pos hc)
  have hg := cubicThetaBoundedScaledUpper_entire (by norm_num : (0:ℝ)≤243)
    (cubicThetaProjectedCoefficient_arithmetic_bound g hc) (cubicThetaCircleOrder rev k)
    (cubicThetaPrimaryDualCenter g) (cubicThetaLevelScale_pos hc)
  have hlin : Differentiable ℂ (fun s : ℂ => ((2*k:ℕ):ℂ)-s) := by fun_prop
  exact hf.add ((hg.comp hlin).const_mul _)

theorem cubicThetaSelectedAngularCompleted_functional (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k) (s : ℂ) :
    cubicThetaSelectedAngularCompleted g hc rev k s=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*
        cubicThetaProjectedAngularCompleted g hc rev k (((2*k:ℕ):ℂ)-s) := by
  rw [←(cubicThetaSelectedAngular_mellin g hc rev hk s).2,
    ←(cubicThetaProjectedAngular_mellin g hc rev hk _).2]
  exact theta_mellin_functional_angular k
    (fun t ht => cubicThetaSelectedAngularAxis_functional g hc rev hk ht) s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entire continued Dirichlet series for the actual primary-projected
cusp pair, with the initial series fixed by the literal coefficients. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaBoundedScaledAxis_mellin {a : Eisenstein→ℂ} {C r : ℝ}
    (hC : 0≤C) (ha : ∀ n,‖a n‖≤C) (hr : 0 < r) (z : ℂ) (ℓ : ℤ)
    {s : ℂ} (hs : 3/2 < s.re) :
    mellin (cubicThetaBoundedScaledAxis a ℓ z r) (2*s+(ℓ.natAbs:ℂ)-1)=
      (r:ℂ)^(-(2*s+(ℓ.natAbs:ℂ)-1))*
        ((1/4:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2*(s+(ℓ.natAbs:ℂ)/2))*
          Complex.Gamma (s+(ℓ.natAbs:ℂ)/2+1/6)*Complex.Gamma (s+(ℓ.natAbs:ℂ)/2-1/6)*
          cubicThetaDirichlet (fun n => theta ℓ n*cubicThetaCoefficientTwist a z n) (2*s-1)) := by
  unfold cubicThetaBoundedScaledAxis
  rw [mellin_comp_mul_left (fun v : ℝ => cubicThetaNonconstant
    (cubicThetaAngularCoefficient a ℓ) (z,v)) _ hr,cubicThetaCoefficient_mellin hC ha z ℓ hs]
  rfl

lemma cubicThetaProjectedAngularCompleted_initial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : 3/2 < s.re) :
    cubicThetaProjectedAngularCompleted g hc rev k (2*s+(k:ℂ)-1)=
      cubicThetaAngularCompletion (g 1 0) k s*
        cubicThetaDirichlet (fun n => theta (cubicThetaCircleOrder rev k) n*
          cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
            (cubicThetaPrimaryDualCenter g) n) (2*s-1) := by
  rw [←(cubicThetaProjectedAngular_mellin g hc rev hk _).2]
  have H := cubicThetaBoundedScaledAxis_mellin (by norm_num : (0:ℝ)≤243)
    (cubicThetaProjectedCoefficient_bound g hc) (cubicThetaLevelScale_pos hc)
    (cubicThetaPrimaryDualCenter g) (cubicThetaCircleOrder rev k) hs
  have habs : (cubicThetaCircleOrder rev k).natAbs=k := by cases rev <;> simp [cubicThetaCircleOrder]
  rw [habs] at H
  rw [cubicThetaProjectedAngularAxis,H]
  unfold cubicThetaAngularCompletion
  rw [show -2*(s+(k:ℂ)/2)=-(2*s+(k:ℂ)) by ring]
  ring

lemma cubicThetaSelectedAngularCompleted_initial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : 3/2 < s.re) :
    cubicThetaSelectedAngularCompleted g hc rev k (2*s+(k:ℂ)-1)=
      cubicThetaAngularCompletion (g 1 0) k s*
        cubicThetaDirichlet (fun n => theta (cubicThetaCircleOrder (!rev) k) n*
          cubicThetaCoefficientTwist cubicThetaSelectedCoefficient
            (cubicThetaPrimaryCuspCenter g) n) (2*s-1) := by
  rw [←(cubicThetaSelectedAngular_mellin g hc rev hk _).2]
  have H := cubicThetaBoundedScaledAxis_mellin (by norm_num : (0:ℝ)≤81)
    cubicThetaSelectedCoefficient_norm (cubicThetaLevelScale_pos hc)
    (cubicThetaPrimaryCuspCenter g) (cubicThetaCircleOrder (!rev) k) hs
  have habs : (cubicThetaCircleOrder (!rev) k).natAbs=k := by cases rev <;> simp [cubicThetaCircleOrder]
  rw [habs] at H
  rw [cubicThetaSelectedAngularAxis,H]
  unfold cubicThetaAngularCompletion
  rw [show -2*(s+(k:ℂ)/2)=-(2*s+(k:ℂ)) by ring]
  ring

lemma cubicThetaAngularUncompletion_entire {q : Eisenstein} (hq : primary q) (k : ℕ) :
    Differentiable ℂ (cubicThetaAngularUncompletion q k) := by
  have hρ : (cubicThetaLevelScale q:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaLevelScale_pos hq).ne'
  have hπ : ((2*Real.pi:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hA : Differentiable ℂ (fun s : ℂ => 2*s+(k:ℂ)-1) := by fun_prop
  have hB : Differentiable ℂ (fun s : ℂ => 2*s+(k:ℂ)) := by fun_prop
  have hC : Differentiable ℂ (fun s : ℂ => s+(k:ℂ)/2+1/6) := by fun_prop
  have hD : Differentiable ℂ (fun s : ℂ => s+(k:ℂ)/2-1/6) := by fun_prop
  exact ((((hA.const_cpow (Or.inl hρ)).const_mul 4).mul (hB.const_cpow (Or.inl hπ))).mul
    (Complex.differentiable_one_div_Gamma.comp hC)).mul
      (Complex.differentiable_one_div_Gamma.comp hD)

theorem cubicThetaSelectedDirichlet_entire (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) :
    Differentiable ℂ (cubicThetaSelectedDirichlet g hc rev k) :=
  (cubicThetaAngularUncompletion_entire hc k).mul
    ((cubicThetaSelectedAngularCompleted_entire g hc rev k).comp (by fun_prop))

lemma cubicThetaAngular_initial_gamma {s : ℂ} (hs : 3/2 < s.re) (k : ℕ) :
    Complex.Gamma (s+(k:ℂ)/2+1/6)≠0 ∧ Complex.Gamma (s+(k:ℂ)/2-1/6)≠0 := by
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  constructor <;> apply Complex.Gamma_ne_zero_of_re_pos <;>
    simp only [Complex.add_re,Complex.sub_re,Complex.div_ofNat_re,Complex.natCast_re,Complex.one_re] <;>
    linarith

theorem cubicThetaProjectedDirichlet_initial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : 3/2 < s.re) :
    cubicThetaProjectedDirichlet g hc rev k s=
      cubicThetaDirichlet (fun n => theta (cubicThetaCircleOrder rev k) n*
        cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
          (cubicThetaPrimaryDualCenter g) n) (2*s-1) := by
  obtain ⟨h₁,h₂⟩ := cubicThetaAngular_initial_gamma hs k
  rw [cubicThetaProjectedDirichlet,cubicThetaProjectedAngularCompleted_initial g hc rev hk hs,
    ←mul_assoc,mul_comm (cubicThetaAngularUncompletion (g 1 0) k s),
    cubicThetaAngular_completion_cancel hc k s h₁ h₂,one_mul]

theorem cubicThetaSelectedDirichlet_initial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : 3/2 < s.re) :
    cubicThetaSelectedDirichlet g hc rev k s=
      cubicThetaDirichlet (fun n => theta (cubicThetaCircleOrder (!rev) k) n*
        cubicThetaCoefficientTwist cubicThetaSelectedCoefficient
          (cubicThetaPrimaryCuspCenter g) n) (2*s-1) := by
  obtain ⟨h₁,h₂⟩ := cubicThetaAngular_initial_gamma hs k
  rw [cubicThetaSelectedDirichlet,cubicThetaSelectedAngularCompleted_initial g hc rev hk hs,
    ←mul_assoc,mul_comm (cubicThetaAngularUncompletion (g 1 0) k s),
    cubicThetaAngular_completion_cancel hc k s h₁ h₂,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedUpperBound
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform vertical bounds for the two actual completed Mellin functions. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPairedUpper_bounded_strip (f g : ℝ→ℂ) (ε : ℂ) (k : ℕ)
    (hf : ∀ s, MellinConvergent (thetaUpper f) s)
    (hg : ∀ s, MellinConvergent (thetaUpper g) s) (a b : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s : ℂ, s.re∈Icc a b →
      ‖mellin (thetaUpper f) s+ε*mellin (thetaUpper g) (((2*k:ℕ):ℂ)-s)‖≤C := by
  let B := ((2*k:ℕ):ℝ)-a
  refine ⟨thetaUpperNormMass f b+‖ε‖*thetaUpperNormMass g B,
    add_nonneg (thetaUpperNormMass_nonneg f b)
      (mul_nonneg (_root_.norm_nonneg ε) (thetaUpperNormMass_nonneg g B)),?_⟩
  intro s hs
  have hfb : ‖mellin (thetaUpper f) s‖≤thetaUpperNormMass f b :=
    thetaUpper_vertical_bound (hf b) hs.2
  have hgb : ‖mellin (thetaUpper g) (((2*k:ℕ):ℂ)-s)‖≤thetaUpperNormMass g B := by
    apply thetaUpper_vertical_bound (hg B)
    simp only [Complex.sub_re,Complex.natCast_re]
    exact sub_le_sub_left hs.1 _
  exact (norm_add_le _ _).trans (add_le_add hfb (by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hgb (_root_.norm_nonneg ε)))

theorem cubicThetaSelectedAngularCompleted_bounded_strip (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) (a b : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s : ℂ, s.re∈Icc a b →
      ‖cubicThetaSelectedAngularCompleted g hc rev k s‖≤C := by
  apply cubicThetaPairedUpper_bounded_strip
  · intro s
    exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤81)
      cubicThetaSelectedCoefficient_arithmetic_bound _ _ (cubicThetaLevelScale_pos hc) s
  · intro s
    exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤243)
      (cubicThetaProjectedCoefficient_arithmetic_bound g hc) _ _ (cubicThetaLevelScale_pos hc) s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedFiniteOrder
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite vertical order follows from bounded completed Mellin tails and
the already proved reciprocal-Gamma estimate. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaUncompleted_finiteOrder {q : Eisenstein} (hq : primary q)
    (k : ℕ) (F : ℂ→ℂ)
    (hbounded : ∀ a b : ℝ, ∃ C : ℝ, 0≤C ∧ ∀ s : ℂ,s.re∈Icc a b → ‖F s‖≤C)
    (a b : ℝ) :
    FiniteVerticalOrder (fun s => cubicThetaAngularUncompletion q k s*F (2*s+(k:ℂ)-1)) a b := by
  let ρ := cubicThetaLevelScale q
  let p : ℝ := 2*Real.pi
  have hρ : 0<ρ := cubicThetaLevelScale_pos hq
  have hp : 0<p := by dsimp [p]; positivity
  let P : ℝ→ℝ := fun σ => 4*ρ^(2*σ+(k:ℝ)-1)*p^(2*σ+(k:ℝ))
  have hP : Continuous P := by
    have hA : Continuous (fun σ : ℝ => 2*σ+(k:ℝ)-1) := by fun_prop
    have hB : Continuous (fun σ : ℝ => 2*σ+(k:ℝ)) := by fun_prop
    exact (continuous_const.mul ((Real.continuous_const_rpow hρ.ne').comp
      hA)).mul ((Real.continuous_const_rpow hp.ne').comp hB)
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hP.continuousOn
  let D := max M 0
  have hD : 0≤D := le_max_right _ _
  have hPb (σ : ℝ) (hσ : σ∈Icc a b) : P σ≤D :=
    (le_abs_self _).trans ((hM σ hσ).trans (le_max_left _ _))
  obtain ⟨B₁,hB₁,hΓ₁⟩ := gammaInverseFiniteOrder (a+(k:ℝ)/2+1/6) (b+(k:ℝ)/2+1/6)
  obtain ⟨B₂,hB₂,hΓ₂⟩ := gammaInverseFiniteOrder (a+(k:ℝ)/2-1/6) (b+(k:ℝ)/2-1/6)
  obtain ⟨C,hC,hF⟩ := hbounded
    (2*a+(k:ℝ)-1) (2*b+(k:ℝ)-1)
  let K := D*C
  have hK : 0≤K := mul_nonneg hD hC
  refine ⟨K+B₁+B₂,2,by positivity,?_⟩
  intro s hs
  change ‖cubicThetaAngularUncompletion q k s*F (2*s+(k:ℂ)-1)‖≤_
  have hG₁ : ‖(Complex.Gamma (s+(k:ℂ)/2+1/6))⁻¹‖≤Real.exp (B₁*(1+|s.im|)^2) := by
    have H := hΓ₁ (s+(k:ℂ)/2+1/6) (by
      simp only [mem_Icc,Complex.add_re,Complex.div_ofNat_re,Complex.natCast_re,Complex.one_re]
      constructor <;> linarith [hs.1,hs.2])
    simpa only [Complex.add_im,Complex.div_ofNat_im,Complex.natCast_im,Complex.one_im,
      zero_div,add_zero] using H
  have hG₂ : ‖(Complex.Gamma (s+(k:ℂ)/2-1/6))⁻¹‖≤Real.exp (B₂*(1+|s.im|)^2) := by
    have H := hΓ₂ (s+(k:ℂ)/2-1/6) (by
      simp only [mem_Icc,Complex.add_re,Complex.sub_re,Complex.div_ofNat_re,Complex.natCast_re,Complex.one_re]
      constructor <;> linarith [hs.1,hs.2])
    simpa only [Complex.add_im,Complex.sub_im,Complex.div_ofNat_im,Complex.natCast_im,
      Complex.one_im,zero_div,add_zero,sub_zero] using H
  have hF' : ‖F (2*s+(k:ℂ)-1)‖≤C := by
    apply hF
    simp only [mem_Icc,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.re_ofNat,
      Complex.im_ofNat,Complex.natCast_re,Complex.one_re,zero_mul,sub_zero]
    constructor <;> linarith [hs.1,hs.2]
  have hpref : ‖4*(ρ:ℂ)^(2*s+(k:ℂ)-1)*(p:ℂ)^(2*s+(k:ℂ))‖≤D := by
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hρ,
      Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp only [Complex.norm_ofNat,Complex.add_re,Complex.sub_re,Complex.mul_re,
      Complex.re_ofNat,Complex.im_ofNat,Complex.natCast_re,Complex.one_re,zero_mul,sub_zero]
    exact hPb s.re hs
  have he : cubicThetaAngularUncompletion q k s*F (2*s+(k:ℂ)-1)=
      (4*(ρ:ℂ)^(2*s+(k:ℂ)-1)*(p:ℂ)^(2*s+(k:ℂ)))*
        (Complex.Gamma (s+(k:ℂ)/2+1/6))⁻¹*(Complex.Gamma (s+(k:ℂ)/2-1/6))⁻¹*
          F (2*s+(k:ℂ)-1) := rfl
  have hQ : 1≤(1+|s.im|)^2 := by nlinarith [abs_nonneg s.im,sq_nonneg |s.im|]
  calc
    _ ≤ (D*Real.exp (B₁*(1+|s.im|)^2))*Real.exp (B₂*(1+|s.im|)^2)*C := by
      rw [he,norm_mul,norm_mul,norm_mul]
      exact mul_le_mul (mul_le_mul (mul_le_mul hpref hG₁ (_root_.norm_nonneg _) hD)
        hG₂ (_root_.norm_nonneg _) (by positivity)) hF' (_root_.norm_nonneg _) (by positivity)
    _ = K*Real.exp ((B₁+B₂)*(1+|s.im|)^2) := by
      rw [add_mul,Real.exp_add]
      dsimp [K]
      ring
    _ ≤ Real.exp K*Real.exp ((B₁+B₂)*(1+|s.im|)^2) :=
      mul_le_mul_of_nonneg_right (le_trans (by linarith : K≤K+1) (Real.add_one_le_exp K)) (Real.exp_pos _).le
    _ = Real.exp (K+(B₁+B₂)*(1+|s.im|)^2) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hQ hK]

open scoped MatrixGroups

theorem cubicThetaSelectedDirichlet_finiteOrder (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) (a b : ℝ) :
    FiniteVerticalOrder (cubicThetaSelectedDirichlet g hc rev k) a b :=
  cubicThetaUncompleted_finiteOrder hc k (cubicThetaSelectedAngularCompleted g hc rev k)
    (cubicThetaSelectedAngularCompleted_bounded_strip g hc rev k) a b

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedFunctional
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual primary-projector pair has the published archimedean
Gamma quotient before finite arithmetic averaging. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaProjectedDirichlet_complete (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) (s : ℂ)
    (h₁ : Complex.Gamma (s+(k:ℂ)/2+1/6)≠0)
    (h₂ : Complex.Gamma (s+(k:ℂ)/2-1/6)≠0) :
    cubicThetaProjectedAngularCompleted g hc rev k (2*s+(k:ℂ)-1)=
      cubicThetaAngularCompletion (g 1 0) k s*cubicThetaProjectedDirichlet g hc rev k s := by
  rw [cubicThetaProjectedDirichlet,←mul_assoc,
    cubicThetaAngular_completion_cancel hc k s h₁ h₂,one_mul]

lemma cubicThetaGamma_dual_halfplane {s : ℂ} {k : ℕ} (hs : s.re<5/6+(k:ℝ)/2) :
    Complex.Gamma (1-s+(k:ℂ)/2+1/6)≠0 ∧
      Complex.Gamma (1-s+(k:ℂ)/2-1/6)≠0 := by
  constructor <;> apply Complex.Gamma_ne_zero_of_re_pos <;>
    simp only [Complex.add_re,Complex.sub_re,Complex.div_ofNat_re,Complex.natCast_re,Complex.one_re] <;>
    linarith

theorem cubicThetaSelectedDirichlet_gamma (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : s.re<5/6+(k:ℝ)/2) :
    cubicThetaSelectedDirichlet g hc rev k s=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*
        (cubicThetaLevelScale (g 1 0):ℂ)^(4*s-2)*((2*Real.pi:ℝ):ℂ)^(4*s-2)*
          metaplecticGammaQuotient (cubicThetaCircleOrder (!rev) k) s*
            cubicThetaProjectedDirichlet g hc rev k (1-s) := by
  obtain ⟨h₁,h₂⟩ := cubicThetaGamma_dual_halfplane hs
  have he : ((2*k:ℕ):ℂ)-(2*s+(k:ℂ)-1)=2*(1-s)+(k:ℂ)-1 := by push_cast; ring
  rw [cubicThetaSelectedDirichlet,cubicThetaSelectedAngularCompleted_functional g hc rev hk,he,
    cubicThetaProjectedDirichlet_complete g hc rev k (1-s) h₁ h₂]
  calc
    _ = (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*
        (cubicThetaAngularUncompletion (g 1 0) k s*cubicThetaAngularCompletion (g 1 0) k (1-s))*
          cubicThetaProjectedDirichlet g hc rev k (1-s) := by ring
    _ = _ := by rw [cubicThetaAngular_archimedean_ratio hc (!rev) k s]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedLineBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute initial-line bounds and the far-left bound needed to
move the actual selected-series Mellin contour. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaProjectedDirichlet_right_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {σ : ℝ} (hσ : 3/2<σ) (s : ℂ) (hs : s.re=σ) :
    ‖cubicThetaProjectedDirichlet g hc rev k s‖≤243*cubicThetaDirichletNormMass (2*σ-1) := by
  rw [cubicThetaProjectedDirichlet_initial g hc rev hk (by linarith)]
  apply cubicThetaDirichlet_norm_le (fun n hn => ?_) (by linarith : 2<2*σ-1) _ (by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      Complex.one_re,zero_mul,sub_zero,hs])
  rw [norm_mul,norm_theta hn,one_mul,cubicThetaCoefficientTwist_norm]
  exact cubicThetaProjectedCoefficient_bound g hc n

theorem cubicThetaSelectedDirichlet_right_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {σ : ℝ} (hσ : 3/2<σ) (s : ℂ) (hs : s.re=σ) :
    ‖cubicThetaSelectedDirichlet g hc rev k s‖≤81*cubicThetaDirichletNormMass (2*σ-1) := by
  rw [cubicThetaSelectedDirichlet_initial g hc rev hk (by linarith)]
  apply cubicThetaDirichlet_norm_le (fun n hn => ?_) (by linarith : 2<2*σ-1) _ (by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      Complex.one_re,zero_mul,sub_zero,hs])
  rw [norm_mul,norm_theta hn,one_mul,cubicThetaCoefficientTwist_norm]
  exact cubicThetaSelectedCoefficient_norm n

theorem cubicThetaSelectedDirichlet_left_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {m : ℕ} (hm : 2 ≤ m) : ∃ C : ℝ, 0≤C ∧ ∀ s : ℂ,s.re=1/2-(m:ℝ) →
      ‖cubicThetaSelectedDirichlet g hc rev k s‖≤C*(1+|s.im|)^(4*m) := by
  obtain ⟨G,hG,hΓ⟩ := metaplecticGamma_half_integer_bound (cubicThetaCircleOrder (!rev) k) m
  let q := g 1 0
  let A := cubicThetaLevelScale q^(-4*(m:ℝ))*(2*Real.pi)^(-4*(m:ℝ))
  let B := 243*cubicThetaDirichletNormMass (2*(m:ℝ))
  let ε := (cubicThetaLevelAngularRoot q rev k)⁻¹
  have hA : 0≤A := mul_nonneg (Real.rpow_nonneg (cubicThetaLevelScale_pos hc).le _)
    (Real.rpow_nonneg (by positivity) _)
  have hB : 0≤B := mul_nonneg (by norm_num) (cubicThetaDirichletNormMass_nonneg _)
  refine ⟨‖ε‖*A*G*B,by positivity,?_⟩
  intro s hs
  have hmR : (2:ℝ)≤ m := by exact_mod_cast hm
  have he : s=(1/2:ℂ)-(m:ℂ)+(s.im:ℂ)*Complex.I := by
    apply Complex.ext <;> simp [hs]
  have hgamma : ‖metaplecticGammaQuotient (cubicThetaCircleOrder (!rev) k) s‖≤G*(1+|s.im|)^(4*m) := by
    rw [he]
    simpa using hΓ s.im
  have hdual := cubicThetaProjectedDirichlet_right_bound g hc rev hk
    (σ:=1/2+(m:ℝ)) (by linarith) (1-s) (by simp [hs]; ring)
  have hb : ‖cubicThetaProjectedDirichlet g hc rev k (1-s)‖≤B := by
    simpa only [show 2*(1/2+(m:ℝ))-1=2*(m:ℝ) by ring] using hdual
  have hpow : (4*s-2).re= -4*(m:ℝ) := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero,hs]
    ring
  have hfac : ‖(cubicThetaLevelScale q:ℂ)^(4*s-2)‖*‖((2*Real.pi:ℝ):ℂ)^(4*s-2)‖=A := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (cubicThetaLevelScale_pos hc),
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<2*Real.pi),hpow]
  have hs' : s.re<5/6+(k:ℝ)/2 := by
    have hkn : (0:ℝ)≤k := Nat.cast_nonneg k
    linarith
  rw [cubicThetaSelectedDirichlet_gamma g hc rev hk hs']
  simp only [norm_mul]
  calc
    _ = (‖ε‖*A)*‖metaplecticGammaQuotient (cubicThetaCircleOrder (!rev) k) s‖*
      ‖cubicThetaProjectedDirichlet g hc rev k (1-s)‖ := by
        rw [←hfac]
        dsimp only [ε,q]
        ring
    _ ≤ (‖ε‖*A)*(G*(1+|s.im|)^(4*m))*B := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedPolynomialStrip
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial strip growth for the actual additive angular continuation,
derived from its functional equation and absolute initial series. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaSelectedDirichlet_polynomial_strip (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k) (a b : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0≤C ∧ ∀ s : ℂ, s.re∈Icc a b →
      ‖cubicThetaSelectedDirichlet g hc rev k s‖≤C*(1+|s.im|)^N := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1/2-a)
  let m := n+2
  let L : ℝ := 1/2-(m:ℝ)
  let R : ℝ := max (max a b) 2
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hLa : L<a := by dsimp [L,m]; push_cast; linarith
  have haR : a≤R := (le_max_left a b).trans (le_max_left _ _)
  have hbR : b≤R := (le_max_right a b).trans (le_max_left _ _)
  have hR2 : 2≤R := le_max_right _ _
  obtain ⟨C₀,hC₀,hleft⟩ := cubicThetaSelectedDirichlet_left_bound g hc rev hk hm
  let C₁ := 81*cubicThetaDirichletNormMass (2*R-1)
  have hC₁ : 0≤C₁ := mul_nonneg (by norm_num) (cubicThetaDirichletNormMass_nonneg _)
  let C := C₀+C₁
  have hC : 0≤C := add_nonneg hC₀ hC₁
  have hL : ∀ s : ℂ, s.re=L →
      ‖cubicThetaSelectedDirichlet g hc rev k s‖≤C*(1+|s.im|)^(4*m) := by
    intro s hs
    exact (hleft s hs).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hC₁) (by positivity))
  have hR : ∀ s : ℂ, s.re=R →
      ‖cubicThetaSelectedDirichlet g hc rev k s‖≤C*(1+|s.im|)^(4*m) := by
    intro s hs
    have H := cubicThetaSelectedDirichlet_right_bound g hc rev hk
      (σ := R) (by linarith) s hs
    calc
      _ ≤ C₁ := H
      _ ≤ C := le_add_of_nonneg_left hC₀
      _ ≤ _ := le_mul_of_one_le_right hC (one_le_pow₀ (by linarith [abs_nonneg s.im]))
  have H := polynomial_strip_of_finite_order (by linarith : L<R)
    (cubicThetaSelectedDirichlet_entire g hc rev k)
    (cubicThetaSelectedDirichlet_finiteOrder g hc rev k L R)
    hC (4*m) hL hR
  have hRL : 0 ≤ R-L+1 := by linarith
  refine ⟨C*2^(4*m)*(R-L+1)^(4*m),4*m,by positivity,?_⟩
  intro s hs
  exact H s ⟨hLa.le.trans hs.1,hs.2.trans hbR⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedContour
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth contour motion for the actual nonzero angular additive series.
Both analyticity and polynomial growth are derived from the arithmetic theta
transformation. The scale may be any positive real number. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaSelectedDirichlet_contour (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {a b Z : ℝ} (hab : a≤b) (hZ : 0<Z) :
    (∫ t : ℝ,mellin W (a+(t:ℂ)*Complex.I)*(Z:ℂ)^(a+(t:ℂ)*Complex.I)*
      cubicThetaSelectedDirichlet g hc rev k (a+(t:ℂ)*Complex.I))=
      ∫ t : ℝ,mellin W (b+(t:ℂ)*Complex.I)*(Z:ℂ)^(b+(t:ℂ)*Complex.I)*
        cubicThetaSelectedDirichlet g hc rev k (b+(t:ℂ)*Complex.I) := by
  obtain ⟨C,N,hC,hpoly⟩ :=
    cubicThetaSelectedDirichlet_polynomial_strip g hc rev hk a b
  let L : ℂ→ℂ := fun s => (Z:ℂ)^s*cubicThetaSelectedDirichlet g hc rev k s
  let B := max (Z^a) (Z^b)*C
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp (σ : ℝ) (hσ : σ∈Icc a b) (t : ℝ) :
      ‖L (σ+((t-0:ℝ):ℂ)*Complex.I)‖ ≤ B*(1+|t-0|)^N := by
    simp only [sub_zero]
    have hz : Z^σ ≤ max (Z^a) (Z^b) := by
      by_cases h : 1 ≤ Z
      · exact (Real.rpow_le_rpow_of_exponent_le h hσ.2).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hZ (le_of_not_ge h) hσ.1).trans
          (le_max_left _ _)
    have hd : ‖cubicThetaSelectedDirichlet g hc rev k
        (σ+(t:ℂ)*Complex.I)‖ ≤ C*(1+|t|)^N := by
      simpa using hpoly (σ+(t:ℂ)*Complex.I) (by simpa using hσ)
    dsimp only [L]
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hZ]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at *
    calc
      _ ≤  max (Z^a) (Z^b)*(C*(1+|t|)^N) := mul_le_mul hz hd
        (_root_.norm_nonneg _) (by positivity)
      _ = _ := by dsimp [B]; ring
  have : NeZero (Z:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hZ.ne'⟩
  have hLd : Differentiable ℂ L := (differentiable_const_cpow_of_neZero _).mul
    (cubicThetaSelectedDirichlet_entire g hc rev k)
  have H := mellinHecke_contour_shift W hW hpos hsm hab (Z:=1) (by norm_num) 0
    L hLd hB N hp
  simpa only [sub_zero,Complex.ofReal_one,Complex.one_cpow,mul_one,L,mul_assoc] using H

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedSmoothMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin inversion for the literal primary-selected coefficients
at every primary rational cusp. -/
noncomputable section
open MeasureTheory Set
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

lemma cubicTheta_twisted_angular_bound {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n,‖a n‖≤C) (z : ℂ) (ℓ : ℤ) (n : Eisenstein) :
    ‖theta ℓ n*cubicThetaCoefficientTwist a z n‖≤C := by
  by_cases hn : n=0
  · subst n
    by_cases hℓ : ℓ=0
    · simpa only [hℓ,theta_zero,one_mul,cubicThetaCoefficientTwist_norm] using ha 0
    · simpa [theta,zero_zpow ℓ hℓ] using hC
  · rw [norm_mul,norm_theta hn,one_mul,cubicThetaCoefficientTwist_norm]
    exact ha n

theorem cubicThetaSelected_smooth_continued (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ Z : ℝ} (hσ : 3/2<σ) (hZ : 0<Z) :
    cubicThetaSelectedAdditiveSum g rev k W Z=
      ((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,
        mellin W (σ+(t:ℂ)*Complex.I)*(Z:ℂ)^(σ+(t:ℂ)*Complex.I)*
          cubicThetaSelectedDirichlet g hc rev k (σ+(t:ℂ)*Complex.I) := by
  have ha (n : Eisenstein) : ‖theta (cubicThetaCircleOrder (!rev) k) n*
      cubicThetaCoefficientTwist cubicThetaSelectedCoefficient (cubicThetaPrimaryCuspCenter g) n‖≤81 :=
    cubicTheta_twisted_angular_bound (by norm_num) cubicThetaSelectedCoefficient_norm _ _ n
  unfold cubicThetaSelectedAdditiveSum
  rw [cubicTheta_smooth_mellin (by norm_num) ha W hW hpos hsm hσ hZ]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [cubicThetaSelectedDirichlet_initial g hc rev hk (by simpa using hσ)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSelectedVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual primary-selected additive Voronoi identity in every nonzero
angular type, prior to the finite cubic-character average. -/
noncomputable section
open MeasureTheory Set
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

theorem cubicThetaSelected_voronoi_far (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {A Z : ℝ} (hA : 1/2<A) (hZ : 0<Z) :
    cubicThetaSelectedAdditiveSum g rev k W Z=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*cubicThetaDualPrefactor (g 1 0)*
        ∑' n : MetaplecticDualArgument,
          (theta (cubicThetaCircleOrder rev k) n.val*
            cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
              (cubicThetaPrimaryDualCenter g) n.val)/
            (‖cubicThetaFrequency n.val‖:ℂ)*
            metaplecticTransform (cubicThetaCircleOrder (!rev) k) W A
              (cubicThetaDualScale (g 1 0) Z*‖cubicThetaFrequency n.val‖^2) := by
  have hs := cubicThetaSelected_smooth_continued g hc rev hk W hW hpos hsm
    (σ:=2) (by norm_num) hZ
  have hc' := cubicThetaSelectedDirichlet_contour g hc rev hk W hW hpos hsm
    (a:= -A) (b:=2) (by linarith) hZ
  rw [←hc'] at hs
  let a : Eisenstein→ℂ := fun n => theta (cubicThetaCircleOrder rev k) n*
    cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc) (cubicThetaPrimaryDualCenter g) n
  let F (s : ℂ) : ℂ := mellin W s*(Z:ℂ)^s*(cubicThetaLevelScale (g 1 0):ℂ)^(4*s-2)*
    ((2*Real.pi:ℝ):ℂ)^(4*s-2)*metaplecticGammaQuotient (cubicThetaCircleOrder (!rev) k) s*
      cubicThetaDirichlet a (2*(1-s)-1)
  have he (t : ℝ) :
      mellin W ((-A:ℂ)+(t:ℂ)*Complex.I)*(Z:ℂ)^((-A:ℂ)+(t:ℂ)*Complex.I)*
        cubicThetaSelectedDirichlet g hc rev k ((-A:ℂ)+(t:ℂ)*Complex.I)=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*F ((-A:ℂ)+(t:ℂ)*Complex.I) := by
    have hkn : (0:ℝ)≤k := Nat.cast_nonneg k
    rw [cubicThetaSelectedDirichlet_gamma g hc rev hk (by simp; linarith)]
    rw [cubicThetaProjectedDirichlet_initial g hc rev hk (by simp; linarith)]
    dsimp only [F,a]
    ring
  have hd := cubicTheta_dual_mellin_integral (a := a) hc (by norm_num : (0:ℝ)≤243)
    (fun n => cubicTheta_twisted_angular_bound (by norm_num)
      (cubicThetaProjectedCoefficient_bound g hc) (cubicThetaPrimaryDualCenter g)
        (cubicThetaCircleOrder rev k) n)
    (cubicThetaCircleOrder (!rev) k) W hW hpos hsm hA hZ
  calc
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∫ t : ℝ,
        (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*F ((-A:ℂ)+(t:ℂ)*Complex.I)) := by
      rw [hs]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simpa only [Complex.ofReal_neg] using he t
    _ = (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*
        (((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,F ((-A:ℂ)+(t:ℂ)*Complex.I)) := by
      rw [integral_const_mul]
      ring
    _ = _ := by rw [show (((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,
        F ((-A:ℂ)+(t:ℂ)*Complex.I))=_ from hd]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticShiftedVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The published small-line formula equals the actual far-left series.
Every contour change is proved for the literal transform before summing. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem metaplecticTransform_line_eq (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ A v : ℝ} (hσ : 0 < σ) (hA : σ ≤ A)
    (hv : 0 < v)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A)) :
    metaplecticTransform ℓ W σ v = metaplecticTransform ℓ W A v := by
  have he := metaplectic_transform_contour ℓ W hW hpos hsm
    (a := -A) (b := -σ) (by linarith) (by linarith) hv hm hp
  exact (congrArg (fun z : ℂ => ((1/(2*Real.pi):ℝ):ℂ)*z) he).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSelectedTransform
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual primary-selected angular transform on every negative line,
with absolute convergence inherited from its proved far-left formula. -/
noncomputable section
open Set
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

theorem cubicThetaSelected_voronoi (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ Z : ℝ} (hσ : 0<σ) (hZ : 0<Z) :
    Summable (fun n : MetaplecticDualArgument =>
      (theta (cubicThetaCircleOrder rev k) n.val*
        cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
          (cubicThetaPrimaryDualCenter g) n.val)/(‖cubicThetaFrequency n.val‖:ℂ)*
        metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
          (cubicThetaDualScale (g 1 0) Z*‖cubicThetaFrequency n.val‖^2)) ∧
    cubicThetaSelectedAdditiveSum g rev k W Z=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*cubicThetaDualPrefactor (g 1 0)*
        ∑' n : MetaplecticDualArgument,
          (theta (cubicThetaCircleOrder rev k) n.val*
            cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
              (cubicThetaPrimaryDualCenter g) n.val)/(‖cubicThetaFrequency n.val‖:ℂ)*
            metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
              (cubicThetaDualScale (g 1 0) Z*‖cubicThetaFrequency n.val‖^2) := by
  let A := σ+1
  let T (s : ℝ) (n : MetaplecticDualArgument) : ℂ :=
    (theta (cubicThetaCircleOrder rev k) n.val*
      cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
        (cubicThetaPrimaryDualCenter g) n.val)/(‖cubicThetaFrequency n.val‖:ℂ)*
      metaplecticTransform (cubicThetaCircleOrder (!rev) k) W s
        (cubicThetaDualScale (g 1 0) Z*‖cubicThetaFrequency n.val‖^2)
  have hA : 1/2<A := by dsimp [A]; linarith
  have hT : T σ=T A := by
    funext n
    dsimp only [T]
    rw [metaplecticTransform_line_eq (cubicThetaCircleOrder (!rev) k) W hW hpos hsm hσ
      (by dsimp [A]; linarith : σ≤A)
      (mul_pos (cubicThetaDualScale_pos hc hZ) (sq_pos_of_pos (cubicThetaFrequency_pos n.property)))
      (angularGammaQuotientStripBound_proved _ _ (by
        linarith [metaplecticAngularShift_nonneg (cubicThetaCircleOrder (!rev) k)]))
      (angularGammaQuotientStripBound_proved _ _ (by
        linarith [metaplecticAngularShift_nonneg (cubicThetaCircleOrder (!rev) k)]))]
  have hs : Summable (T A) := cubicTheta_dual_mellin_summable hc (by norm_num : (0:ℝ)≤243)
    (fun n => cubicTheta_twisted_angular_bound (by norm_num)
      (cubicThetaProjectedCoefficient_bound g hc) (cubicThetaPrimaryDualCenter g)
        (cubicThetaCircleOrder rev k) n)
    (cubicThetaCircleOrder (!rev) k) W hW hpos hsm hA hZ
  have he := cubicThetaSelected_voronoi_far g hc rev hk W hW hpos hsm hA hZ
  change Summable (T σ) ∧ _
  constructor
  · rwa [hT]
  · change cubicThetaSelectedAdditiveSum g rev k W Z=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*cubicThetaDualPrefactor (g 1 0)*∑' n,T σ n
    rw [hT]
    exact he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSelectedGaussSum
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact primary-pair reindexing of the smoothed additive sum. The common
numerator is lambda*c*d^3, so the squared frequency is N(c)N(d)^3/27. -/
noncomputable section
open Set
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaSelectedAdditiveSum_eq (g : SL(2,Eisenstein)) (rev : Bool)
    (k : ℕ) (W : ℝ→ℂ) (Z : ℝ) :
    cubicThetaSelectedAdditiveSum g rev k W Z=
      cubicThetaSelectedSmoothSum (cubicThetaCircleOrder (!rev) k)
        (cubicThetaPrimaryCuspCenter g) W Z := rfl

lemma cubicThetaPrimary_smooth_term (cd : CubicThetaPrimaryPair) (ℓ : ℤ)
    (z : ℂ) (W : ℝ→ℂ) (Z : ℝ) :
    theta ℓ (cubicThetaPrimaryNumerator cd)*
      cubicThetaCoefficientTwist cubicThetaConjugateCoefficient z (cubicThetaPrimaryNumerator cd)*
      (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ)*
      W (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖^2/Z)=
    ((3^(5/2:ℝ):ℝ):ℂ)*theta ℓ lambdaE*
      ((Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
        (Real.fourierChar (tracePair (cubicThetaFrequency (cubicThetaPrimaryNumerator cd)) z):ℂ)*
        W (norm cd.val.1*norm cd.val.2^3/(27*Z))) := by
  have he := cubicThetaTau_primary_conj cd.property.1 cd.property.2.1 cd.property.2.2
  change star ((‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ)*
    cubicThetaArithmeticCoefficient (cubicThetaPrimaryNumerator cd))=_ at he
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal] at he
  have he' : cubicThetaConjugateCoefficient (cubicThetaPrimaryNumerator cd)*
      (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ)=
      ((3^(5/2:ℝ):ℝ):ℂ)*(Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1 := by
    simpa only [cubicThetaConjugateCoefficient,←Complex.star_def,Complex.ofReal_mul] using he
  rw [cubicThetaPrimaryFrequency_sq,div_div]
  have ht : theta ℓ (cubicThetaPrimaryNumerator cd)=
      theta ℓ lambdaE*theta ℓ (cd.val.1*cd.val.2^3) := by
    simp only [cubicThetaPrimaryNumerator,theta_mul,mul_assoc]
  rw [ht,cubicThetaCoefficientTwist]
  calc
    _ = (cubicThetaConjugateCoefficient (cubicThetaPrimaryNumerator cd)*
        (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ))*
      (theta ℓ lambdaE*theta ℓ (cd.val.1*cd.val.2^3)*
        (Real.fourierChar (tracePair (cubicThetaFrequency (cubicThetaPrimaryNumerator cd)) z):ℂ)*
        W (norm cd.val.1*norm cd.val.2^3/(27*Z))) := by ring
    _ = _ := by rw [he']; ring

/-- This reindexing is an identity of the actual sum, with no convergence
hypothesis hidden in a change of variables. -/
theorem cubicThetaSelectedSmoothSum_pairs (ℓ : ℤ) (z : ℂ) (W : ℝ→ℂ) (Z : ℝ) :
    cubicThetaSelectedSmoothSum ℓ z W Z=
    ((3^(5/2:ℝ):ℝ):ℂ)*theta ℓ lambdaE*
      ∑' cd : CubicThetaPrimaryPair,
        (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
          (Real.fourierChar (tracePair (cubicThetaFrequency (cubicThetaPrimaryNumerator cd)) z):ℂ)*
          W (norm cd.val.1*norm cd.val.2^3/(27*Z)) := by
  let f (n : Eisenstein) : ℂ := theta ℓ n*
    cubicThetaCoefficientTwist cubicThetaSelectedCoefficient z n*
      (‖cubicThetaFrequency n‖:ℂ)*W (‖cubicThetaFrequency n‖^2/Z)
  have hs : Function.support f ⊆ {n | n≠0} := by
    intro n hn hz
    subst n
    exact hn (by simp [f,cubicThetaFrequency])
  change (∑' n : MetaplecticDualArgument,f n.val)=_
  calc
    _ = ∑' n : Eisenstein,f n := tsum_subtype_eq_of_support_subset hs
    _ = ∑' n : Eisenstein,if cubicThetaPrimarySupport n then
        theta ℓ n*cubicThetaCoefficientTwist cubicThetaConjugateCoefficient z n*
          (‖cubicThetaFrequency n‖:ℂ)*W (‖cubicThetaFrequency n‖^2/Z) else 0 := by
      apply tsum_congr
      intro n
      by_cases hn : cubicThetaPrimarySupport n <;>
        simp [f,cubicThetaCoefficientTwist,cubicThetaSelectedCoefficient,hn]
    _ = ∑' cd : CubicThetaPrimaryPair,
        theta ℓ (cubicThetaPrimaryNumerator cd)*
          cubicThetaCoefficientTwist cubicThetaConjugateCoefficient z (cubicThetaPrimaryNumerator cd)*
          (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ)*
          W (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖^2/Z) := cubicThetaPrimary_tsum _
    _ = _ := by simp_rw [cubicThetaPrimary_smooth_term]; rw [tsum_mul_left]

/-- Scaling the additive cusp by lambda cubed removes the inverse different
from every selected frequency. -/
lemma cubicThetaPrimary_additive_phase (cd : CubicThetaPrimaryPair) (r u : Eisenstein) :
    (Real.fourierChar (tracePair (cubicThetaFrequency (cubicThetaPrimaryNumerator cd))
      ((traceLambda^3*(u:ℂ))/(r:ℂ))):ℂ)=
      additivePhase r (cd.val.1*cd.val.2^3*u) := by
  rw [additivePhase_fourierChar]
  congr 1
  unfold tracePair cubicThetaFrequency cubicThetaPrimaryNumerator
  push_cast
  rw [lambdaE_coe]
  congr 2
  field_simp [traceLambda_ne_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSmoothPairSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact radial support gives genuine finite sums over the unique
primary squarefree/cube pairs. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaPrimary_smooth_support (W : ℝ→ℂ) (hW : HasCompactSupport W)
    {X : ℝ} (hX : 0<X) :
    Set.Finite {cd : CubicThetaPrimaryPair | W (norm cd.val.1*norm cd.val.2^3/X)≠0} := by
  obtain ⟨B,hB⟩ := hW.isCompact.isBounded.exists_norm_le
  have hpre : Set.Finite {cd : CubicThetaPrimaryPair |
      norm (cubicThetaPrimaryNumerator cd)≤3*(B*X)} :=
    Set.Finite.preimage cubicThetaPrimaryNumerator_injective.injOn (finite_norm_le _)
  apply hpre.subset
  intro cd hcd
  have hb := hB _ (subset_tsupport W hcd)
  have hprod : norm cd.val.1*norm cd.val.2^3≤B*X := by
    apply (div_le_iff₀ hX).mp
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb)
  have hf := cubicThetaFrequency_sq (cubicThetaPrimaryNumerator cd)
  rw [cubicThetaPrimaryFrequency_sq] at hf
  change norm (cubicThetaPrimaryNumerator cd)≤3*(B*X)
  linarith

lemma cubicThetaPrimary_smooth_summable (a : CubicThetaPrimaryPair→ℂ)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) {X : ℝ} (hX : 0<X) :
    Summable (fun cd : CubicThetaPrimaryPair =>
      a cd*W (norm cd.val.1*norm cd.val.2^3/X)) := by
  apply summable_of_hasFiniteSupport
  apply (cubicThetaPrimary_smooth_support W hW hX).subset
  intro cd hcd
  exact (mul_ne_zero_iff.mp hcd).2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCharacterAverage
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite cubic-character average of the actual selected Gauss sum.
The zero extension removes every cube factor sharing a prime with the level. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaPrimary_character_sum {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (c d : Eisenstein) :
    (∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
      additivePhase r (c*d^3*residueRepresentative r u))=
    (Real.sqrt (norm r):ℂ)*gauss r*
      (if IsCoprime r d then star (cubicSymbol r c) else 0) := by
  have hN : (Real.sqrt (norm r):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hr))).ne'
  calc
    _ = (Real.sqrt (norm r):ℂ)*frequencyGauss r (c*d^3) := by
      rw [frequencyGauss,tsum_fintype,←mul_assoc,mul_inv_cancel₀ hN,one_mul]
    _ = _ := by
      rw [frequencyGauss_squarefree hr hs,cubicSymbol_mul_upper hr,cubicSymbol_pow_upper hr]
      by_cases hd : IsCoprime r d
      · rw [ite_eq_left hd,cubicSymbol_cube_of_isCoprime hr d hd,mul_one]
        ring
      · rw [ite_eq_right hd,cubicSymbol_eq_zero_of_not_isCoprime hr hd]
        simp

lemma cubicThetaSelectedSmoothSum_rational (r u : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (X : ℝ) :
    cubicThetaSelectedSmoothSum ℓ ((traceLambda^3*(u:ℂ))/(r:ℂ)) W (X/27)=
      ((3^(5/2:ℝ):ℝ):ℂ)*theta ℓ lambdaE*cubicThetaPrimaryGaussSum r u ℓ W X := by
  rw [cubicThetaSelectedSmoothSum_pairs]
  have he : 27*(X/27)=X := by ring
  simp_rw [he,cubicThetaPrimary_additive_phase]
  rfl

theorem cubicThetaPrimaryGaussSum_average {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (ℓ : ℤ) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    {X : ℝ} (hX : 0<X) :
    (∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
      cubicThetaPrimaryGaussSum r (residueRepresentative r u) ℓ W X)=
    (Real.sqrt (norm r):ℂ)*gauss r*
      ∑' cd : CubicThetaPrimaryPair,
        if IsCoprime r cd.val.2 then
          (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
            star (cubicSymbol r cd.val.1)*W (norm cd.val.1*norm cd.val.2^3/X)
        else 0 := by
  let F (u : Residues r) (cd : CubicThetaPrimaryPair) : ℂ :=
    cubicSymbol r (residueRepresentative r u)*
      ((Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
        additivePhase r (cd.val.1*cd.val.2^3*residueRepresentative r u))*
          W (norm cd.val.1*norm cd.val.2^3/X)
  have hF (u : Residues r) : Summable (F u) := cubicThetaPrimary_smooth_summable _ W hW hX
  have hterm (cd : CubicThetaPrimaryPair) :
      (∑ u : Residues r,F u cd)=
      (Real.sqrt (norm r):ℂ)*gauss r*
        (if IsCoprime r cd.val.2 then
          (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
            star (cubicSymbol r cd.val.1)*W (norm cd.val.1*norm cd.val.2^3/X)
        else 0) := by
    let A := (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
      W (norm cd.val.1*norm cd.val.2^3/X)
    have ht : (∑ u : Residues r,F u cd)=A*
        ∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
          additivePhase r (cd.val.1*cd.val.2^3*residueRepresentative r u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [F,A]
      ring
    rw [ht,cubicThetaPrimary_character_sum hr hs]
    by_cases hd : IsCoprime r cd.val.2 <;> simp only [hd,ite_true, if_true,ite_false, if_false]
    · dsimp only [A]
      ring
    · ring
  calc
    _ = ∑ u : Residues r,∑' cd : CubicThetaPrimaryPair,F u cd := by
      apply Finset.sum_congr rfl
      intro u _
      rw [cubicThetaPrimaryGaussSum,←tsum_mul_left]
      apply tsum_congr
      intro cd
      dsimp only [F]
      ring
    _ = ∑' cd : CubicThetaPrimaryPair,∑ u : Residues r,F u cd :=
      (Summable.tsum_finsetSum (fun u _ => hF u)).symm
    _ = _ := by simp_rw [hterm]; rw [tsum_mul_left]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRawPairs
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Gauss average equals the manuscript's actual raw completed
sum. Nonsquarefree terms vanish by the proved finite Gauss-sum identity. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma metaplecticRawCompleted_primary_pairs (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (X : ℝ) :
    metaplecticRawCompleted r ℓ W X=
      ∑' cd : CubicThetaPrimaryPair,
        if IsCoprime r cd.val.2 then
          (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
            star (cubicSymbol r cd.val.1)*W (norm cd.val.1*norm cd.val.2^3/X)
        else 0 := by
  let f (du : PrimaryArgument × PrimaryArgument) : ℂ :=
    if IsCoprime (du.1:Eisenstein) r then
      (Real.sqrt (norm du.1):ℂ)*gauss du.2*theta ℓ (du.2*du.1^3)*
        star (cubicSymbol r du.2)*W (norm (du.2*du.1^3)/X)
    else 0
  have hs : Function.support f ⊆ {du | Squarefree (du.2:Eisenstein)} := by
    intro du hdu
    by_contra hns
    apply hdu
    dsimp only [f]
    rw [gauss_eq_zero_of_not_squarefree du.2.property hns]
    split_ifs <;> ring
  change (∑' du,f du)=_
  calc
    _ = ∑' du : {du : PrimaryArgument × PrimaryArgument // Squarefree (du.2:Eisenstein)},
        f du.val := (tsum_subtype_eq_of_support_subset hs).symm
    _ = ∑' cd : CubicThetaPrimaryPair,f (cubicThetaPrimaryPairEquiv cd).val :=
      (cubicThetaPrimaryPairEquiv.tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro cd
      dsimp only [f,cubicThetaPrimaryPairEquiv,Equiv.coe_fn_mk]
      rw [isCoprime_comm,norm_mul_eq,eisenstein_norm_pow]

theorem cubicThetaPrimaryGaussSum_average_raw {r : Eisenstein}
    (hr : primary r) (hs : Squarefree r) [Fintype (Residues r)]
    (ℓ : ℤ) (W : ℝ→ℂ) (hW : HasCompactSupport W) {X : ℝ} (hX : 0<X) :
    (∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
      cubicThetaPrimaryGaussSum r (residueRepresentative r u) ℓ W X)=
    (Real.sqrt (norm r):ℂ)*gauss r*metaplecticRawCompleted r ℓ W X := by
  rw [cubicThetaPrimaryGaussSum_average hr hs ℓ W hW hX,metaplecticRawCompleted_primary_pairs]

/-- Exact finite additive detection of the raw completed cubic Gauss sum,
with the angular lambda factor and the scale 27 both retained. -/
theorem cubicThetaSelectedSmoothSum_average_raw {r : Eisenstein}
    (hr : primary r) (hs : Squarefree r) [Fintype (Residues r)]
    (ℓ : ℤ) (W : ℝ→ℂ) (hW : HasCompactSupport W) {X : ℝ} (hX : 0<X) :
    (∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
      cubicThetaSelectedSmoothSum ℓ
        ((traceLambda^3*(residueRepresentative r u:ℂ))/(r:ℂ)) W (X/27))=
    (((3^(5/2:ℝ):ℝ):ℂ)*theta ℓ lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r)*metaplecticRawCompleted r ℓ W X := by
  simp_rw [cubicThetaSelectedSmoothSum_rational]
  calc
    _ = (((3^(5/2:ℝ):ℝ):ℂ)*theta ℓ lambdaE)*
        ∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
          cubicThetaPrimaryGaussSum r (residueRepresentative r u) ℓ W X := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = _ := by rw [cubicThetaPrimaryGaussSum_average_raw hr hs ℓ W hW hX]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueCusps
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete rational-cusp lift on every residue. Nonunit residues get
an arbitrary determinant-one lift, and their cubic character weight is zero. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaResidueCuspMatrix_cusp (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaPrimaryCuspCenter (cubicThetaResidueCuspMatrix r hr u)=
      (traceLambda^3*(u:ℂ))/(r:ℂ) := by
  rw [cubicThetaResidueCuspMatrix,dite_eq_left hu]
  unfold cubicThetaPrimaryCuspCenter
  rw [(cubicThetaNineGaussMatrix_entries r hr u hu).1,
    (cubicThetaNineGaussMatrix_entries r hr u hu).2.1,
    Subalgebra.coe_mul,Subalgebra.coe_pow,lambdaE_coe]

lemma cubicThetaResidueCuspMatrix_weighted (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (Z : ℝ) :
    cubicSymbol r u*cubicThetaSelectedAdditiveSum (cubicThetaResidueCuspMatrix r hr u) rev k W Z=
      cubicSymbol r u*cubicThetaSelectedSmoothSum (cubicThetaCircleOrder (!rev) k)
        ((traceLambda^3*(u:ℂ))/(r:ℂ)) W Z := by
  by_cases hu : IsCoprime r u
  · rw [cubicThetaSelectedAdditiveSum_eq,cubicThetaResidueCuspMatrix_cusp r hr u hu]
  · rw [cubicSymbol_eq_zero_of_not_isCoprime hr hu,zero_mul,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAveragedVoronoi
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite character average of the proved angular additive
Voronoi formula. The coefficient is the actual finite cusp average; further
local/Moebius simplification is kept separate. -/
noncomputable section
open scoped BigOperators MatrixGroups ContDiff
namespace CubicFirstMoment

theorem cubicThetaResidue_voronoi_oai {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (cubicThetaResidueDualTerm r hr rev k W σ X) ∧
    ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r))*
        metaplecticRawCompleted r (cubicThetaCircleOrder (!rev) k) W X=
    (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      ∑' n,cubicThetaResidueDualTerm r hr rev k W σ X n := by
  let g (u : Residues r) := cubicThetaResidueCuspMatrix r hr (residueRepresentative r u)
  let hp (u : Residues r) := cubicThetaResidueCuspPrimary r hr (residueRepresentative r u)
  let w (u : Residues r) := cubicSymbol r (residueRepresentative r u)
  let D (u : Residues r) (n : MetaplecticDualArgument) : ℂ :=
    theta (cubicThetaCircleOrder rev k) n.val*
      cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient (g u) (hp u))
        (cubicThetaPrimaryDualCenter (g u)) n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
      metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
        (cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2)
  let P := (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r
  have hE (u : Residues r) : Summable (D u) ∧
      cubicThetaSelectedAdditiveSum (g u) rev k W (X/27)=P*∑' n,D u n := by
    have H := cubicThetaSelected_voronoi (g u) (hp u) rev hk W hW hpos hsm hσ
      (div_pos hX (by norm_num) : 0<X/27)
    simpa only [g,cubicThetaResidueCuspMatrix_bottom,D,P] using H
  have ht (n : MetaplecticDualArgument) :
      (∑ u : Residues r,w u*D u n)=cubicThetaResidueDualTerm r hr rev k W σ X n := by
    unfold cubicThetaResidueDualTerm cubicThetaResidueDualCoefficient
    simp only [Finset.mul_sum,Finset.sum_div,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    dsimp only [w,D,g,hp]
    ring
  have hsum : Summable (fun n : MetaplecticDualArgument => ∑ u : Residues r,w u*D u n) :=
    summable_sum (fun u _ => (hE u).1.mul_left (w u))
  refine ⟨hsum.congr ht,?_⟩
  have hl := cubicThetaSelectedSmoothSum_average_raw hr hs (cubicThetaCircleOrder (!rev) k) W hW hX
  have hl' : (∑ u : Residues r,w u*cubicThetaSelectedAdditiveSum (g u) rev k W (X/27))=
      ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
        ((Real.sqrt (norm r):ℂ)*gauss r))*
          metaplecticRawCompleted r (cubicThetaCircleOrder (!rev) k) W X := by
    simpa only [g,w,cubicThetaResidueCuspMatrix_weighted] using hl
  rw [←hl']
  change _=P*∑' n,cubicThetaResidueDualTerm r hr rev k W σ X n
  calc
    _ = P*∑ u : Residues r,∑' n,w u*D u n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [(hE u).2,tsum_mul_left]
      ring
    _ = P*∑' n,∑ u : Residues r,w u*D u n := by
      rw [Summable.tsum_finsetSum (fun u _ => (hE u).1.mul_left (w u))]
    _ = _ := by simp_rw [ht]

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.cubicThetaResidue_voronoi_oai := @OAI.CubicFirstMoment.cubicThetaResidue_voronoi_oai
