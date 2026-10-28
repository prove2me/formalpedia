-- Prove2me | solution 1 for KernelGammaEnvelope.gLine_decomp_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:50:59.65948+00:00
-- url     : https://prove2.me/submissions/ac898353-563e-4027-957b-72a241ff86e6

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
import Theorems.Thm_KernelGammaEnvelope_gamma_r_polar_explicit
import Theorems.Thm_ThetaConverge_convergence_obligation
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






theorem solution (t : ℝ) (ht : t ≠ 0) :
    ∃ Λ : ℝ, Filter.Tendsto (imLnVal (1/4) (t/2)) Filter.atTop (nhds Λ) ∧
      gLine t = gammaRMag t *
        (Real.cos (Λ - (t/2) * Real.log Real.pi) * (riemannZeta ((1/2:ℂ)+(t:ℂ)*I)).re
          - Real.sin (Λ - (t/2) * Real.log Real.pi) * (riemannZeta ((1/2:ℂ)+(t:ℂ)*I)).im) := by
  have hGne : Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hcontra
    have him := congrArg Complex.im hcontra
    simp at him
    exact ht (by linarith [him])
  obtain ⟨Λ, hΛtend, hbranch⟩ :=
    ThetaConverge.convergence_obligation (1/4) (t/2) (by norm_num) hGne
  have hG := gamma_r_polar_explicit t Λ hbranch
  refine ⟨Λ, hΛtend, ?_⟩
  set φ : ℝ := Λ - (t/2) * Real.log Real.pi with hφ
  set Z : ℂ := riemannZeta ((1/2:ℂ)+(t:ℂ)*I) with hZ
  have hs0 : ((1/2 : ℂ) + (t:ℂ)*I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hGRne : Gammaℝ ((1/2:ℂ) + (t:ℂ)*I) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos; simp [Complex.add_re, Complex.mul_re]
  have hcomp : completedRiemannZeta ((1/2:ℂ)+(t:ℂ)*I) = Gammaℝ ((1/2:ℂ) + (t:ℂ)*I) * Z := by
    rw [hZ, riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ hGRne]
  have hgl : gLine t = (completedRiemannZeta ((1/2:ℂ)+(t:ℂ)*I)).re := rfl
  rw [hgl, hcomp, hG,
    show Complex.exp (Complex.I * (φ:ℂ)) = Complex.exp ((φ:ℂ) * Complex.I) by rw [mul_comm],
    Complex.exp_ofReal_mul_I]
  unfold gammaRMag
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring
