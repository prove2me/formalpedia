-- Prove2me | solution 1 for KernelGammaEnvelope.gamma_r_polar_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:35:07.98768+00:00
-- url     : https://prove2.me/submissions/3265c1af-9e31-4778-a7b8-612e576d74c8

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



/-! ## 3.  Two-sided bounds for `|Gamma(1/4 + i y)|` -/





/-! ## 4.  The explicit polar decomposition of `gLine` -/


theorem solution (t : ℝ) (Λ : ℝ)
    (hbranch : Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)
        = (‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ : ℂ) * Complex.exp (Complex.I * (Λ:ℂ))) :
    Gammaℝ ((1/2:ℂ) + (t:ℂ)*I)
      = ((Real.pi ^ (-(1/4):ℝ) * ‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((Λ - (t/2) * Real.log Real.pi : ℝ):ℂ)) := by
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  set NG : ℝ := ‖Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I)‖ with hNG
  have hhalf : ((1/2:ℂ) + (t:ℂ)*I)/2 = ((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I := by push_cast; ring
  have hpi : (Real.pi : ℂ) ^ (-((1/2:ℂ) + (t:ℂ)*I)/2)
      = ((Real.pi ^ (-(1/4):ℝ) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((- (t/2) * Real.log Real.pi : ℝ):ℂ)) := by
    have hlog : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
      rw [Complex.ofReal_log hpipos.le]
    have hne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [Complex.cpow_def_of_ne_zero hne, hlog,
      show (Real.log Real.pi : ℂ) * (-((1/2:ℂ) + (t:ℂ)*I)/2)
          = (((-(1/4):ℝ) * Real.log Real.pi : ℝ):ℂ)
            + Complex.I * ((-(t/2) * Real.log Real.pi : ℝ):ℂ) by push_cast; ring,
      Complex.exp_add]
    congr 1
    rw [Real.rpow_def_of_pos hpipos, Complex.ofReal_exp, mul_comm]
  rw [Gammaℝ_def, hhalf, hbranch, hpi,
    show Complex.exp (Complex.I * ((Λ - (t/2) * Real.log Real.pi : ℝ):ℂ))
        = Complex.exp (Complex.I * ((- (t/2) * Real.log Real.pi : ℝ):ℂ))
          * Complex.exp (Complex.I * (Λ:ℂ)) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
  push_cast; ring
