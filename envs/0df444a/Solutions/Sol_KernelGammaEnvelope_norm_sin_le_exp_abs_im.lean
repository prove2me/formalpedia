-- Prove2me | solution 1 for KernelGammaEnvelope.norm_sin_le_exp_abs_im
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:35:22.362393+00:00
-- url     : https://prove2.me/submissions/ad27097a-4708-45dd-9b0b-421368816a03

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

section
namespace KernelGammaEnvelope
end KernelGammaEnvelope
open KernelGammaEnvelope

/-! ## 1.  `|Gamma(s)| <= Gamma(Re s)` -/









/-! ## 2.  `|sin z| <= exp |Im z|` -/


theorem solution (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h1 : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, zero_sub, neg_neg]
    exact le_abs_self _
  have h2 : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub]
    exact neg_le_abs _
  rw [Complex.sin]
  calc ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2‖
      = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
    _ ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by gcongr
    _ = Real.exp |z.im| := by ring
