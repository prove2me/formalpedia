-- Prove2me | solution 1 for KernelGammaEnvelope.norm_Gamma_quarter_lower
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:52:25.02223+00:00
-- url     : https://prove2.me/submissions/a2432116-47f3-4118-b76a-3d503c94b2d9

import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_KernelGammaEnvelope
import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Theorems.Thm_KernelGammaEnvelope_norm_sin_le_exp_abs_im
namespace ThetaGap
end ThetaGap
namespace XiLineZeros
end XiLineZeros
/-  KernelGammaEnvelope.lean -- ANDURIL G2 kernel discharge: a crude but RIGOROUS two-sided
    envelope for the magnitude of the Gamma_R factor on the critical line, and the EXPLICIT
    polar decomposition of `gLine` that consumes it.

    ## Why this file exists

    `ZeroSignDecomp_t14.gLine_sign_decomp_t` writes

        gLine t = M * (cos phi * Re zeta(1/2+it) - sin phi * Im zeta(1/2+it)),   M > 0,

    but hides `M` behind an existential, because the sign route never needs its size.  A VALUE box
    for `gLine t` (the `memR` facts that `CheckBand.checkLine_correct` consumes) does need it: a box
    that excludes 0 carries a positive lower bound on `|gLine t|`, hence on `M`.  Nothing in the corpus
    bounds `|Gamma_R(1/2+it)|` (the `CheckBand` / `ZeroSignDecomp_t14` headers call it "the single
    precisely identified blocker").  This file supplies the missing piece in its cheapest honest form:

      * `norm_Gamma_le_Gamma_re` : `|Gamma(s)| <= Gamma(Re s)` for `Re s > 0` (Euler's integral and
        `norm_integral_le_integral_norm`).
      * `norm_sin_le_exp_abs_im` : `|sin z| <= exp |Im z|`.
      * `norm_Gamma_quarter_lower` : `(9/4) * exp(-pi |y|) <= |Gamma(1/4 + i y)|`, from the reflection
        formula `Gamma(s) Gamma(1-s) = pi / sin(pi s)` and the two upper bounds above.
      * `norm_Gamma_quarter_upper` : `|Gamma(1/4 + i y)| <= 4`.
      * `gLine_decomp_explicit` : the decomposition with `M = pi^(-1/4) * |Gamma(1/4 + i t/2)|` named.
      * `gammaRMag_bounds` : `(3/4) * exp(-pi |t| / 2) <= M <= 4`, `M = gammaRMag t`.

    The lower bound is loose (at t = 22 it undershoots the true `M = 3.2e-8` by a factor of about
    4e7), but it is a theorem, and it is all a sign-definite box needs: the reflected-band checker
    only reads signs.

    conjecture1_proved = False.  Elementary Gamma-function inequalities, not a proof of RH.
-/





open Complex Real MeasureTheory XiLineZeros ThetaGap

namespace KernelGammaEnvelope

/-! ## 1.  `|Gamma(s)| <= Gamma(Re s)` -/

/-- **Euler-integral norm bound.**  For `0 < Re s`, `|Gamma(s)| <= Gamma(Re s)`: the norm of Euler's
    integral is at most the integral of the norm, and `|exp(-x) x^(s-1)| = exp(-x) x^(Re s - 1)`. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simp

/-- `Gamma(x) <= 1` on `[1, 2]` (convexity of `Gamma` with `Gamma 1 = Gamma 2 = 1`). -/
theorem Gamma_le_one_of_mem_Icc {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : Real.Gamma x ≤ 1 := by
  have hc := Real.convexOn_Gamma
  have hseg : x ∈ segment ℝ (1 : ℝ) 2 := by
    rw [segment_eq_Icc (by norm_num)]; exact ⟨h1, h2⟩
  have h := hc.le_on_segment (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num) hseg
  rwa [Real.Gamma_one, Real.Gamma_two, max_self] at h



/-- `Gamma(3/4) <= 4/3`  (`Gamma(7/4) = (3/4) Gamma(3/4)` and `Gamma(7/4) <= 1`). -/
theorem Gamma_three_quarter_le : Real.Gamma (3 / 4) ≤ 4 / 3 := by
  have h := Real.Gamma_add_one (s := (3 / 4 : ℝ)) (by norm_num)
  have hle : Real.Gamma (3 / 4 + 1) ≤ 1 := Gamma_le_one_of_mem_Icc (by norm_num) (by norm_num)
  rw [h] at hle
  linarith

/-! ## 2.  `|sin z| <= exp |Im z|` -/



/-! ## 3.  Two-sided bounds for `|Gamma(1/4 + i y)|` -/





/-! ## 4.  The explicit polar decomposition of `gLine` -/









end KernelGammaEnvelope


/-  KernelGammaEnvelope.lean -- ANDURIL G2 kernel discharge: a crude but RIGOROUS two-sided
    envelope for the magnitude of the Gamma_R factor on the critical line, and the EXPLICIT
    polar decomposition of `gLine` that consumes it.

    ## Why this file exists

    `ZeroSignDecomp_t14.gLine_sign_decomp_t` writes

        gLine t = M * (cos phi * Re zeta(1/2+it) - sin phi * Im zeta(1/2+it)),   M > 0,

    but hides `M` behind an existential, because the sign route never needs its size.  A VALUE box
    for `gLine t` (the `memR` facts that `CheckBand.checkLine_correct` consumes) does need it: a box
    that excludes 0 carries a positive lower bound on `|gLine t|`, hence on `M`.  Nothing in the corpus
    bounds `|Gamma_R(1/2+it)|` (the `CheckBand` / `ZeroSignDecomp_t14` headers call it "the single
    precisely identified blocker").  This file supplies the missing piece in its cheapest honest form:

      * `norm_Gamma_le_Gamma_re` : `|Gamma(s)| <= Gamma(Re s)` for `Re s > 0` (Euler's integral and
        `norm_integral_le_integral_norm`).
      * `norm_sin_le_exp_abs_im` : `|sin z| <= exp |Im z|`.
      * `norm_Gamma_quarter_lower` : `(9/4) * exp(-pi |y|) <= |Gamma(1/4 + i y)|`, from the reflection
        formula `Gamma(s) Gamma(1-s) = pi / sin(pi s)` and the two upper bounds above.
      * `norm_Gamma_quarter_upper` : `|Gamma(1/4 + i y)| <= 4`.
      * `gLine_decomp_explicit` : the decomposition with `M = pi^(-1/4) * |Gamma(1/4 + i t/2)|` named.
      * `gammaRMag_bounds` : `(3/4) * exp(-pi |t| / 2) <= M <= 4`, `M = gammaRMag t`.

    The lower bound is loose (at t = 22 it undershoots the true `M = 3.2e-8` by a factor of about
    4e7), but it is a theorem, and it is all a sign-definite box needs: the reflected-band checker
    only reads signs.

    conjecture1_proved = False.  Elementary Gamma-function inequalities, not a proof of RH.
-/





open Complex Real MeasureTheory XiLineZeros ThetaGap

section
namespace KernelGammaEnvelope
end KernelGammaEnvelope
open KernelGammaEnvelope

/-! ## 1.  `|Gamma(s)| <= Gamma(Re s)` -/









/-! ## 2.  `|sin z| <= exp |Im z|` -/



/-! ## 3.  Two-sided bounds for `|Gamma(1/4 + i y)|` -/




theorem solution (y : ℝ) :
    (9 / 4) * Real.exp (-(Real.pi * |y|)) ≤ ‖Complex.Gamma (((1/4 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
  set s : ℂ := ((1/4 : ℝ) : ℂ) + (y : ℂ) * I with hs
  have hsre : s.re = 1 / 4 := by rw [hs]; simp
  have hs1re : (1 - s).re = 3 / 4 := by rw [Complex.sub_re, hsre]; simp; norm_num
  have hG1 : ‖Complex.Gamma (1 - s)‖ ≤ 4 / 3 := by
    have h := norm_Gamma_le_Gamma_re (s := 1 - s) (by rw [hs1re]; norm_num)
    rw [hs1re] at h
    exact le_trans h Gamma_three_quarter_le
  have hGs0 : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hGs10 : Complex.Gamma (1 - s) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [hs1re]; norm_num)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- norms of the reflection identity
  have hprod_ne : Complex.Gamma s * Complex.Gamma (1 - s) ≠ 0 := mul_ne_zero hGs0 hGs10
  have hsin_ne : Complex.sin (↑Real.pi * s) ≠ 0 := by
    intro h0; rw [h0, div_zero] at hrefl; exact hprod_ne hrefl
  have hnorm : ‖Complex.Gamma s‖ * ‖Complex.Gamma (1 - s)‖
      = Real.pi / ‖Complex.sin (↑Real.pi * s)‖ := by
    rw [← norm_mul, hrefl, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi_pos]
  -- |sin(pi s)| <= exp(pi |y|)
  have hsinle : ‖Complex.sin (↑Real.pi * s)‖ ≤ Real.exp (Real.pi * |y|) := by
    have h := norm_sin_le_exp_abs_im (↑Real.pi * s)
    have him : (↑Real.pi * s).im = Real.pi * y := by rw [hs]; simp
    rw [him, abs_mul, abs_of_pos hpi_pos] at h
    exact h
  have hsinpos : 0 < ‖Complex.sin (↑Real.pi * s)‖ := norm_pos_iff.mpr hsin_ne
  have hG1pos : 0 < ‖Complex.Gamma (1 - s)‖ := norm_pos_iff.mpr hGs10
  have hexp_pos : 0 < Real.exp (Real.pi * |y|) := Real.exp_pos _
  -- |Gamma s| = pi / (|sin| * |Gamma(1-s)|)
  have h3 : ‖Complex.Gamma s‖ * ‖Complex.Gamma (1 - s)‖ * ‖Complex.sin (↑Real.pi * s)‖
      = Real.pi := by
    rw [hnorm]; field_simp
  have hGs : ‖Complex.Gamma s‖
      = Real.pi / (‖Complex.sin (↑Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖) := by
    rw [eq_div_iff (ne_of_gt (mul_pos hsinpos hG1pos))]
    calc ‖Complex.Gamma s‖ * (‖Complex.sin (↑Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖)
        = ‖Complex.Gamma s‖ * ‖Complex.Gamma (1 - s)‖ * ‖Complex.sin (↑Real.pi * s)‖ := by ring
      _ = Real.pi := h3
  rw [hGs]
  have hden : ‖Complex.sin (↑Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖
      ≤ Real.exp (Real.pi * |y|) * (4 / 3) :=
    mul_le_mul hsinle hG1 (le_of_lt hG1pos) (le_of_lt hexp_pos)
  have hdenpos : 0 < ‖Complex.sin (↑Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖ :=
    mul_pos hsinpos hG1pos
  have hstep : Real.pi / (Real.exp (Real.pi * |y|) * (4 / 3))
      ≤ Real.pi / (‖Complex.sin (↑Real.pi * s)‖ * ‖Complex.Gamma (1 - s)‖) :=
    div_le_div_of_nonneg_left (le_of_lt hpi_pos) hdenpos hden
  have hexpneg : Real.exp (-(Real.pi * |y|)) = (Real.exp (Real.pi * |y|))⁻¹ := Real.exp_neg _
  have hpi3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
  calc (9 / 4) * Real.exp (-(Real.pi * |y|))
      = (9 / 4) / Real.exp (Real.pi * |y|) := by rw [hexpneg]; ring
    _ ≤ Real.pi / (Real.exp (Real.pi * |y|) * (4 / 3)) := by
        rw [div_le_div_iff₀ hexp_pos (by positivity)]
        nlinarith [hexp_pos]
    _ ≤ _ := hstep
