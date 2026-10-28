-- Prove2me | solution 1 for KernelGammaEnvelope.gammaRMag_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:58:39.331323+00:00
-- url     : https://prove2.me/submissions/8911f74b-5536-4f3e-87c2-9c79adc3316c

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
import Theorems.Thm_KernelGammaEnvelope_norm_Gamma_quarter_lower
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

/-- `Gamma(1/4) <= 4`  (`Gamma(5/4) = Gamma(1/4)/4` and `Gamma(5/4) <= 1`). -/
theorem Gamma_quarter_le : Real.Gamma (1 / 4) ≤ 4 := by
  have h := Real.Gamma_add_one (s := (1 / 4 : ℝ)) (by norm_num)
  have hle : Real.Gamma (1 / 4 + 1) ≤ 1 := Gamma_le_one_of_mem_Icc (by norm_num) (by norm_num)
  rw [h] at hle
  linarith



/-! ## 2.  `|sin z| <= exp |Im z|` -/



/-! ## 3.  Two-sided bounds for `|Gamma(1/4 + i y)|` -/

/-- **Upper bound** `|Gamma(1/4 + i y)| <= 4`. -/
theorem norm_Gamma_quarter_upper (y : ℝ) :
    ‖Complex.Gamma (((1/4 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ 4 := by
  have hre : (((1/4 : ℝ) : ℂ) + (y : ℂ) * I).re = 1 / 4 := by simp
  have h := norm_Gamma_le_Gamma_re (s := ((1/4 : ℝ) : ℂ) + (y : ℂ) * I) (by rw [hre]; norm_num)
  rw [hre] at h
  exact le_trans h Gamma_quarter_le



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





/-! ## 4.  The explicit polar decomposition of `gLine` -/








theorem solution (t : ℝ) :
    (3 / 4) * Real.exp (-(Real.pi * |t / 2|)) ≤ gammaRMag t ∧ gammaRMag t ≤ 4 := by
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  have hlo := norm_Gamma_quarter_lower (t / 2)
  have hhi := norm_Gamma_quarter_upper (t / 2)
  have hGnn : 0 ≤ ‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ := norm_nonneg _
  have hp_le : Real.pi ^ (-(1/4):ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
  have hp_pos : 0 < Real.pi ^ (-(1/4):ℝ) := Real.rpow_pos_of_pos hpipos _
  -- pi^(-1/4) >= 1/2 (crude): pi <= 16, so pi^(1/4) <= 16^(1/4) = 2.
  have hp_ge : (1 / 2) ≤ Real.pi ^ (-(1/4):ℝ) := by
    rw [Real.rpow_neg (le_of_lt hpipos)]
    have h16 : Real.pi ≤ 16 := by linarith [Real.pi_lt_d2]
    have hq : Real.pi ^ ((1:ℝ)/4) ≤ 2 := by
      calc Real.pi ^ ((1:ℝ)/4) ≤ (16:ℝ) ^ ((1:ℝ)/4) :=
            Real.rpow_le_rpow (le_of_lt hpipos) h16 (by norm_num)
        _ = 2 := by
            rw [show (16:ℝ) = 2 ^ (4:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
    have hqpos : 0 < Real.pi ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hpipos _
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num]
    exact inv_anti₀ hqpos hq
  unfold gammaRMag
  constructor
  · -- (3/4) e^{-pi|t/2|} <= (1/3) (9/4) e^{-pi|t/2|} <= pi^(-1/4) |Gamma|
    have hE : 0 ≤ Real.exp (-(Real.pi * |t / 2|)) := le_of_lt (Real.exp_pos _)
    calc (3 / 4) * Real.exp (-(Real.pi * |t / 2|))
        ≤ (1 / 2) * ((9 / 4) * Real.exp (-(Real.pi * |t / 2|))) := by nlinarith [hE]
      _ ≤ Real.pi ^ (-(1/4):ℝ) * ‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ :=
          mul_le_mul hp_ge hlo (by positivity) (le_of_lt hp_pos)
  · calc Real.pi ^ (-(1/4):ℝ) * ‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖
        ≤ 1 * 4 := mul_le_mul hp_le hhi hGnn (by norm_num)
      _ = 4 := by norm_num
