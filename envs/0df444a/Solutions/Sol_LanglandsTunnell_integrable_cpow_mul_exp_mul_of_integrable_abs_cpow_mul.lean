-- Prove2me | solution 1 for LanglandsTunnell.integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/49414327-f6bd-5c90-b404-fecbf5f4bd4f

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Gamma
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul

set_option autoImplicit false

open MeasureTheory Set

namespace K8A2

theorem integral_rpow_mul_exp (r c : ℝ) (hr : -1 < r) (hc : 0 < c) :
    ∫ a in Ioi (0 : ℝ), a ^ r * Real.exp (-c * a ^ 2)
      = c ^ (-(r + 1) / 2) * (1 / 2) * Real.Gamma ((r + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := r) (b := c) two_pos hr hc
  simp only [Real.rpow_two] at h
  simpa using h

theorem integrableOn_rpow_mul_exp (r c : ℝ) (hr : -1 < r) (hc : 0 < c) :
    IntegrableOn (fun a : ℝ => a ^ r * Real.exp (-c * a ^ 2)) (Ioi 0) :=
  integrableOn_rpow_mul_exp_neg_mul_sq hc hr

theorem scale_pow (r u : ℝ) (hu : u ≠ 0) :
    (Real.pi * (u ^ 2)⁻¹) ^ (-(r + 1) / 2) = Real.pi ^ (-(r + 1) / 2) * |u| ^ (r + 1) := by
  have hu2 : 0 < u ^ 2 := by positivity
  rw [Real.mul_rpow Real.pi_pos.le (inv_nonneg.mpr hu2.le), Real.inv_rpow hu2.le, ← Real.rpow_neg (by positivity),
    show u ^ 2 = |u| ^ (2 : ℝ) by rw [Real.rpow_two, sq_abs], ← Real.rpow_mul (abs_nonneg u)]
  congr 2; ring

end K8A2

theorem solution
    (w : ℂ) (hw : -1 < w.re) (K : ℝ → ℝ → ℝ → ℂ)
    (hK : Measurable fun p : ℝ × ℝ × ℝ => K p.1 p.2.1 p.2.2)
    (h3 : Integrable (fun q : ℝ × ℝ × ℝ => ((|q.2.1| : ℝ) : ℂ) ^ (w + 1) * K q.1 q.2.1 q.2.2)
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))))) :
    Integrable (fun p : ℝ × ℝ × ℝ × ℝ =>
        ((p.1 : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * (p.1 ^ 2 * (p.2.2.1 ^ 2)⁻¹))) : ℂ) * K p.2.1 p.2.2.1 p.2.2.2)
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))))) := by
  set r : ℝ := w.re with hr

  have hF : Measurable (fun p : ℝ × ℝ × ℝ × ℝ =>
      ((p.1 : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * (p.1 ^ 2 * (p.2.2.1 ^ 2)⁻¹))) : ℂ) * K p.2.1 p.2.2.1 p.2.2.2) := by
    have h1 : Measurable (fun p : ℝ × ℝ × ℝ × ℝ => ((p.1 : ℝ) : ℂ) ^ w) :=
      (Complex.measurable_ofReal.comp measurable_fst).pow_const w
    have h2 : Measurable (fun p : ℝ × ℝ × ℝ × ℝ => (Real.exp (-(Real.pi * (p.1 ^ 2 * (p.2.2.1 ^ 2)⁻¹))) : ℂ)) := by
      apply Complex.measurable_ofReal.comp
      apply Real.measurable_exp.comp
      fun_prop
    have h3' : Measurable (fun p : ℝ × ℝ × ℝ × ℝ => K p.2.1 p.2.2.1 p.2.2.2) := hK.comp measurable_snd
    exact (h1.mul h2).mul h3'
  rw [integrable_prod_iff' hF.aestronglyMeasurable]

  have hu0 : ∀ᵐ y ∂((volume.restrict (Iio (0 : ℝ))).prod ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))))),
      (y : ℝ × ℝ × ℝ).2.1 ≠ 0 := by
    have q1 : Measure.QuasiMeasurePreserving (fun y : ℝ × ℝ × ℝ => y.2.1)
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))))) volume :=
      Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd
    have h0 : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ (0 : ℝ) := by
      rw [ae_iff, show {a : ℝ | ¬a ≠ 0} = {0} by ext; simp]; exact measure_singleton 0
    exact q1.ae h0
  constructor
  ·
    filter_upwards [hu0] with y hy
    have hc : 0 < Real.pi * (y.2.1 ^ 2)⁻¹ := mul_pos Real.pi_pos (inv_pos.mpr (by positivity))
    have hreal := K8A2.integrableOn_rpow_mul_exp r _ (by rw [hr]; exact hw) hc
    have hmeas : AEStronglyMeasurable (fun a : ℝ =>
        ((a : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * (a ^ 2 * (y.2.1 ^ 2)⁻¹))) : ℂ) * K y.1 y.2.1 y.2.2)
        (volume.restrict (Ioi (0 : ℝ))) := by
      apply Measurable.aestronglyMeasurable
      have h1 : Measurable (fun a : ℝ => ((a : ℝ) : ℂ) ^ w) := Complex.measurable_ofReal.pow_const w
      have h2 : Measurable (fun a : ℝ => (Real.exp (-(Real.pi * (a ^ 2 * (y.2.1 ^ 2)⁻¹))) : ℂ)) := by
        apply Complex.measurable_ofReal.comp; apply Real.measurable_exp.comp; fun_prop
      exact (h1.mul h2).mul measurable_const
    refine Integrable.mono' ((hreal.mul_const ‖K y.1 y.2.1 y.2.2‖)) hmeas ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun a ha => ?_)
    have ha' : (0 : ℝ) < a := ha
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha', Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← hr]
    apply le_of_eq
    congr 2
    congr 1; ring
  ·
    have key : ∀ y : ℝ × ℝ × ℝ, y.2.1 ≠ 0 →
        (∫ a in Ioi (0 : ℝ), ‖((a : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * (a ^ 2 * (y.2.1 ^ 2)⁻¹))) : ℂ) * K y.1 y.2.1 y.2.2‖)
          = (Real.pi ^ (-(r + 1) / 2) * (1 / 2) * Real.Gamma ((r + 1) / 2)) * (|y.2.1| ^ (r + 1) * ‖K y.1 y.2.1 y.2.2‖) := by
      intro y hy
      have hc : 0 < Real.pi * (y.2.1 ^ 2)⁻¹ := mul_pos Real.pi_pos (inv_pos.mpr (by positivity))
      have h1 : (∫ a in Ioi (0 : ℝ), ‖((a : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * (a ^ 2 * (y.2.1 ^ 2)⁻¹))) : ℂ) *
            K y.1 y.2.1 y.2.2‖)
          = ∫ a in Ioi (0 : ℝ), (a ^ r * Real.exp (-(Real.pi * (y.2.1 ^ 2)⁻¹) * a ^ 2)) * ‖K y.1 y.2.1 y.2.2‖ := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun a ha => ?_)
        have ha' : (0 : ℝ) < a := ha
        rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha', Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), ← hr]
        congr 2; congr 1; ring
      rw [h1, integral_mul_const, K8A2.integral_rpow_mul_exp r _ (by rw [hr]; exact hw) hc, K8A2.scale_pow r _ hy]
      ring
    have hnorm : Integrable (fun q : ℝ × ℝ × ℝ => |q.2.1| ^ (r + 1) * ‖K q.1 q.2.1 q.2.2‖)
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))))) := by
      refine (h3.norm).congr ?_
      filter_upwards [hu0] with q hq
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hq), Complex.add_re, Complex.one_re, ← hr]
    refine (hnorm.const_mul (Real.pi ^ (-(r + 1) / 2) * (1 / 2) * Real.Gamma ((r + 1) / 2))).congr ?_
    filter_upwards [hu0] with y hy
    exact (key y hy).symm

end S_LanglandsTunnell_integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul
end P2MW
export P2MW.S_LanglandsTunnell_integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul (solution)
