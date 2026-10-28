-- Prove2me | solution 1 for H1000Line.phase_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:03:01.564221+00:00
-- url     : https://prove2.me/submissions/460ca1bc-8f38-4280-b9ea-c7b130d0c1bd

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_H1000Phase
import Definitions.Def_ArdaRH65K_Turing121_KernelGammaEnvelope
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_H1000Line_arctan_part
import Theorems.Thm_H1000Line_lnBox_sound
import Theorems.Thm_H1000Line_log_inner_eq
import Theorems.Thm_RSDesignTheta_logpi_box
import Theorems.Thm_RSDesignTheta_theta_bracket
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
namespace ThetaGap
end ThetaGap
/-  RSTheta.lean -- ANDURIL Riemann-Siegel brick B0 (theta): a HEIGHT-UNIFORM kernel enclosure of
    the Riemann-Siegel phase, plus one instance at t = 280000.

    ## Provenance

    Promoted on 2026-09-23 from `Probes/RSDesign_theta.lean`, the calibration probe of the RS design
    memo (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 4.0 and op O-4). Every proof is
    unchanged. Two things differ from the probe:

      * The statement of the registry theorem `gaussBranch_theta_sub_thetaMain_le` now spells every
        name in full: `Filter.Tendsto`, `ThetaGap.imLnVal`, `Filter.atTop`, `nhds`. That makes it the
        verbatim text of the proposed `AND_theta_branch` statement (memo op O-4). The grant gate
        matches statement to artifact by normalized text, and the registry statement cannot rely on
        this file's `open` lines. Both spellings elaborate to the same term.
      * The trailing `#print axioms` lines moved to the guard `AxiomGuardRSTheta.lean`.

    The namespace stays `RSDesignTheta`, so names cited from the probe still resolve.

    ## What this file proves (no `sorry`, no `native_decide`, no new axioms).

    The island's sign bridge `ZeroSignDecomp.gLine_sign_decomp_t` writes
        gLine t = M * (cos phi * Re zeta(1/2+it) - sin phi * Im zeta(1/2+it)),   M > 0,
        phi = Lam - (t/2) log pi,   Lam = lim_n imLnVal (1/4) (t/2) n,
    so every on-line sign needs a box for `phi` (= the Riemann-Siegel theta).  The existing route
    (`ForgeRate.rate_at`) bounds `|Lam - imLnVal x y n0|` by `2(|y|(x+1) + |y|^3/(3 n0))/n0`, which needs
    `n0 >> y^(3/2)` arctan terms: about 10^9 terms at t = 280000.  That is the "theta Euler route
    dies above a few hundred" wall.

    This file replaces the rate bound by a CLOSED-FORM Stirling bracket with an explicit remainder,
    valid at EVERY height, proved by an elementary convex-trapezoid argument (no Bernoulli
    functions, no polygamma, no complex Stirling, no Mathlib gap):

      * `trapezoid_convex`   : for F' = f, f' = g, g monotone on [a, a+1]:
                               0 <= (f a + f (a+1))/2 - (F (a+1) - F a) <= (g (a+1) - g a)/4.
      * `lam_bracket`        : for x > 0, y >= 0, any n0, and Lam = lim imLnVal x y:
            C - y/(4((x+n0)^2 + y^2)) <= Lam <= C,
            C = FA n0 + fA n0 / 2 - sum_{k <= n0} fA k - y,
            fA u = arctan (y/(x+u)),  FA u = (x+u) arctan (y/(x+u)) + (y/2) log ((x+u)^2 + y^2).
      * `theta_bracket`      : n0 = 0, x = 1/4, y = t/2, for every t > 0:
            thetaS t - 1/(2t) <= Lam - (t/2) log pi <= thetaS t,
            thetaS t = (t/4) log (1/16 + t^2/4) - (1/4) arctan (2t) - t/2 - (t/2) log pi.
      * `theta_sub_thetaMain`, `gaussBranch_theta_sub_thetaMain_le` : against the corpus main term
            `ZeroFreeBridge.thetaMain`, |Lam - (t/2) log pi - thetaMain t| <= 1/t for every t > 0 --
            the statement DESIGN_AND_ladder_1e9 section 3.3 proposed for `AND_theta_branch` (there with
            t >= 200 and the misspelled `ZetaReflection.imLnVal`; the island name is `ThetaGap.imLnVal`).
      * `theta_280000_box`   : the numeric instance at t = 280000 (reduced mod 2 pi, K = 216236),
                               an interval of width about 2e-6 around 2.2434215934
                               (mpmath siegeltheta(280000) - 2 pi K = 2.2434215934093).

    So the theta brick of the RS era costs O(1) transcendental evaluations per point at any height
    (two logs, one arctan, log pi shared), instead of O(t^(3/2)) arctan terms.  The general
    `lam_bracket` (any x > 0) also covers the Gamma_R edge quantities Im log Gamma(x + iT/2) at
    x = 1 (sigma = 2) and, after one shift Gamma(z) = Gamma(z+1)/z, at sigma = -1.

    Calibration (the probe, 2026-09-23): 646 lines, two compile iterations. `lake env lean` took about
    20 s wall, of which kernel type checking was 0.33 s and `norm_num` elaboration 4.7 s.

    conjecture1_proved = False.  A finite enclosure of one special-function value plus a
    height-uniform inequality; nothing here bears on the Riemann Hypothesis.
-/



open Real Filter Topology Set ThetaGap

namespace RSDesignTheta

/-! ## 1.  The convex trapezoid lemma. -/





/-! ## 2.  The θ-series summand, its antiderivative and derivative. -/















/-! ## 3.  The finite sandwich of `imLnVal`. -/











/-! ## 4.  The limit of `H n` and the Stirling bracket for `Lam`. -/





/-! ## 5.  The Riemann-Siegel phase: the `n0 = 0`, `x = 1/4`, `y = t/2` specialisation. -/









/-! ## 6.  The numeric instance at `t = 280000` (the top of the h280000 ladder).

All constants below are short decimals chosen by an untrusted script; every inequality between
them and the exact series values is re-checked by `norm_num`/`linarith` in the kernel.  The log
brackets use Mathlib's `Real.abs_log_sub_add_sum_range_le` (Taylor series of `log (1 - x)` with the
geometric remainder `|x|^(n+1)/(1-|x|)`), the pi bracket is Mathlib's `pi_gt_d20`/`pi_lt_d20`. -/

/-- `log 2` to about `7e-15` (48 terms of the `x = 1/2` series). -/
theorem log2_box :
    (3465735902799708427977/5000000000000000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ 6931471805599487910229/10000000000000000000000 := by
  have hx : |(1/2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 48
  have hl : Real.log (1 - 1/2 : ℝ) = -Real.log 2 := by
    rw [show (1:ℝ) - 1/2 = 2⁻¹ by norm_num, Real.log_inv]
  have habs : |(1/2 : ℝ)| = 1/2 := abs_of_pos (by norm_num)
  rw [hl, habs, abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

















end RSDesignTheta


/-  H1000Phase.lean -- the Riemann-Siegel phase at a rational height, as kernel-checkable integer
    bounds (lane h1000-prep; consumed by `H1000Line`).

    For `t = tn / 2^tq` and the branch limit `Λ = lim imLnVal (1/4) (t/2)` (the one
    `KernelGammaEnvelope.gLine_decomp_explicit` exposes), `phase_sound` gives

        phaseLo tn tq k nl ≤ (Λ - (t/2) log π) · 2^64 ≤ phaseHi tn tq k nl,

    where `phaseLo`, `phaseHi` are plain `Int`/`Nat` computations (the kernel evaluates them) of the
    height-uniform bracket `RSTheta.theta_bracket`:
        thetaS t - 1/(2t) ≤ Λ - (t/2) log π ≤ thetaS t,
        thetaS t = (t/4) log (1/16 + t²/4) - (1/4) arctan (2t) - t/2 - (t/2) log π.
    Ingredients: `log (1/16 + t²/4) = (k - 2tq - 4) log 2 - log (1 - (A - 2^k)/A)`, `A = 4^tq + 4 tn²`
    (`log_inner_eq`); the fixed-point series of `-log (1 - x)` with Mathlib's geometric remainder
    `Real.abs_log_sub_add_sum_range_le` (`lnBox_sound`); `log 2`, `log π` from `RSTheta.log2_box`,
    `logpi_box`; `π` from `Real.pi_gt_d20`, `pi_lt_d20`; `arctan (2t) = π/2 - arctan w` with
    `w - w³/3 ≤ arctan w ≤ w` (`ArctanTaylor`).  Every rounding is outward (`fdiv`, `cdiv`).

    Trust: axioms [propext, Classical.choice, Quot.sound] (AxiomGuardH1000Line.lean); no `sorry`.
    conjecture1_proved = False.  Elementary enclosures of one special-function value; nothing here
    bears on the Riemann Hypothesis.
-/






open Real Filter Topology
open ArbEcon ArbEcon.OrderK

namespace H1000Line

noncomputable section

/-! ## A. Floor and ceiling division of an integer by a positive natural. -/





theorem fdiv_le (a : ℤ) {b : ℕ} (hb : 0 < b) : ((fdiv a b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  have hb' : (b : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hb)
  have h := Int.ediv_mul_le a hb'
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hbR]
  have h' : (((a / (b : ℤ)) * (b : ℤ) : ℤ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
  rw [Int.cast_mul, Int.cast_natCast] at h'
  exact h'

theorem le_cdiv (a : ℤ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ ((cdiv a b : ℤ) : ℝ) := by
  have h := fdiv_le (-a) hb
  unfold fdiv at h
  unfold cdiv
  rw [Int.cast_neg]
  rw [Int.cast_neg, neg_div] at h
  linarith

/-! ## B. The series `-log (1 - a/b) = Σ_j (a/b)^(j+1)/(j+1)` in fixed point (scale `2^64`). -/



theorem ONE_eq : ((ONE : ℕ) : ℝ) = 2 ^ 64 := by norm_num [ONE]

















/-! ## C. Scaled constants: `log 2`, `log π`, `π/8`, `2π` at scale `2^64`. -/










theorem log2_scaled : (L2LO : ℝ) ≤ Real.log 2 * 2 ^ 64 ∧ Real.log 2 * 2 ^ 64 ≤ L2HI := by
  obtain ⟨h1, h2⟩ := RSDesignTheta.log2_box
  have hP : (0 : ℝ) ≤ 2 ^ 64 := by positivity
  have a1 := mul_le_mul_of_nonneg_right h1 hP
  have a2 := mul_le_mul_of_nonneg_right h2 hP
  constructor
  · have e : (L2LO : ℝ) ≤ 3465735902799708427977 / 5000000000000000000000 * 2 ^ 64 := by
      norm_num [L2LO]
    linarith
  · have e : 6931471805599487910229 / 10000000000000000000000 * 2 ^ 64 ≤ (L2HI : ℝ) := by
      norm_num [L2HI]
    linarith

theorem logpi_scaled : (LPLO : ℝ) ≤ Real.log π * 2 ^ 64 ∧ Real.log π * 2 ^ 64 ≤ LPHI := by
  obtain ⟨h1, h2⟩ := RSDesignTheta.logpi_box
  have hP : (0 : ℝ) ≤ 2 ^ 64 := by positivity
  have a1 := mul_le_mul_of_nonneg_right h1 hP
  have a2 := mul_le_mul_of_nonneg_right h2 hP
  constructor
  · have e : (LPLO : ℝ) ≤ 11447298858493313056567 / 10000000000000000000000 * 2 ^ 64 := by
      norm_num [LPLO]
    linarith
  · have e : 5723649429247365361409 / 5000000000000000000000 * 2 ^ 64 ≤ (LPHI : ℝ) := by
      norm_num [LPHI]
    linarith





/-! ## D. The Riemann-Siegel phase `φ = Λ - (t/2) log π` at `t = tn / 2^tq`. -/











theorem phaseOk_spec {tn tq k : ℕ} (h : phaseOk tn tq k = true) :
    2 ^ k ≤ AA tn tq ∧ AA tn tq < 2 * 2 ^ k ∧ 2 * tq + 4 ≤ k ∧ 1 ≤ tn ∧ 2 ^ tq ≤ 2 * tn := by
  simp only [phaseOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩



theorem innerBox_sound {tn tq k : ℕ} (nl : ℕ) (h : phaseOk tn tq k = true) :
    (((innerBox tn tq k nl).1 : ℤ) : ℝ) ≤ Real.log (1 / 16 + ((tn : ℝ) / 2 ^ tq) ^ 2 / 4) * 2 ^ 64 ∧
    Real.log (1 / 16 + ((tn : ℝ) / 2 ^ tq) ^ 2 / 4) * 2 ^ 64 ≤ (((innerBox tn tq k nl).2 : ℤ) : ℝ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := phaseOk_spec h
  have hA : 0 < AA tn tq := lt_of_lt_of_le (Nat.two_pow_pos k) h1
  have h2a : 2 * (AA tn tq - 2 ^ k) < AA tn tq := by omega
  obtain ⟨lb1, lb2⟩ := lnBox_sound (AA tn tq - 2 ^ k) (AA tn tq) nl hA h2a
  obtain ⟨l1, l2⟩ := log2_scaled
  rw [log_inner_eq h]
  simp only [innerBox]
  set j : ℕ := k - (2 * tq + 4)
  have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have m1 := mul_le_mul_of_nonneg_left l1 hj
  have m2 := mul_le_mul_of_nonneg_left l2 hj
  push_cast
  constructor <;> nlinarith [m1, m2, lb1, lb2]





end

end H1000Line


/-  H1000Phase.lean -- the Riemann-Siegel phase at a rational height, as kernel-checkable integer
    bounds (lane h1000-prep; consumed by `H1000Line`).

    For `t = tn / 2^tq` and the branch limit `Λ = lim imLnVal (1/4) (t/2)` (the one
    `KernelGammaEnvelope.gLine_decomp_explicit` exposes), `phase_sound` gives

        phaseLo tn tq k nl ≤ (Λ - (t/2) log π) · 2^64 ≤ phaseHi tn tq k nl,

    where `phaseLo`, `phaseHi` are plain `Int`/`Nat` computations (the kernel evaluates them) of the
    height-uniform bracket `RSTheta.theta_bracket`:
        thetaS t - 1/(2t) ≤ Λ - (t/2) log π ≤ thetaS t,
        thetaS t = (t/4) log (1/16 + t²/4) - (1/4) arctan (2t) - t/2 - (t/2) log π.
    Ingredients: `log (1/16 + t²/4) = (k - 2tq - 4) log 2 - log (1 - (A - 2^k)/A)`, `A = 4^tq + 4 tn²`
    (`log_inner_eq`); the fixed-point series of `-log (1 - x)` with Mathlib's geometric remainder
    `Real.abs_log_sub_add_sum_range_le` (`lnBox_sound`); `log 2`, `log π` from `RSTheta.log2_box`,
    `logpi_box`; `π` from `Real.pi_gt_d20`, `pi_lt_d20`; `arctan (2t) = π/2 - arctan w` with
    `w - w³/3 ≤ arctan w ≤ w` (`ArctanTaylor`).  Every rounding is outward (`fdiv`, `cdiv`).

    Trust: axioms [propext, Classical.choice, Quot.sound] (AxiomGuardH1000Line.lean); no `sorry`.
    conjecture1_proved = False.  Elementary enclosures of one special-function value; nothing here
    bears on the Riemann Hypothesis.
-/






open Real Filter Topology
open ArbEcon ArbEcon.OrderK

section
namespace H1000Line
end H1000Line
open H1000Line

noncomputable section

/-! ## A. Floor and ceiling division of an integer by a positive natural. -/









/-! ## B. The series `-log (1 - a/b) = Σ_j (a/b)^(j+1)/(j+1)` in fixed point (scale `2^64`). -/





















/-! ## C. Scaled constants: `log 2`, `log π`, `π/8`, `2π` at scale `2^64`. -/


















/-! ## D. The Riemann-Siegel phase `φ = Λ - (t/2) log π` at `t = tn / 2^tq`. -/




















theorem solution (tn tq k nl : ℕ) (hok : phaseOk tn tq k = true) (Λ : ℝ)
    (hΛ : Tendsto (ThetaGap.imLnVal (1 / 4) (((tn : ℝ) / 2 ^ tq) / 2)) atTop (𝓝 Λ)) :
    ((phaseLo tn tq k nl : ℤ) : ℝ) ≤ (Λ - ((tn : ℝ) / 2 ^ tq) / 2 * Real.log π) * 2 ^ 64 ∧
    (Λ - ((tn : ℝ) / 2 ^ tq) / 2 * Real.log π) * 2 ^ 64 ≤ ((phaseHi tn tq k nl : ℤ) : ℝ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := phaseOk_spec hok
  have htnR : (0 : ℝ) < tn := by exact_mod_cast h4
  have hq : (0 : ℝ) < 2 ^ tq := by positivity
  have hP : (0 : ℝ) < 2 ^ 64 := by positivity
  have hpos4 : 0 < 4 * 2 ^ tq := by positivity
  have hpos2 : 0 < 2 * 2 ^ tq := by positivity
  have hpos2t : 0 < 2 * tn := by omega
  -- the integer pieces, abstracted before any cast normalisation
  obtain ⟨i1, i2⟩ := innerBox_sound nl hok
  obtain ⟨a1, a2⟩ := arctan_part (tq := tq) h4
  have t1lo := fdiv_le ((innerBox tn tq k nl).1 * (tn : ℤ)) hpos4
  have t1hi := le_cdiv ((innerBox tn tq k nl).2 * (tn : ℤ)) hpos4
  have t3lo := fdiv_le (-((tn * ONE : ℕ) : ℤ)) hpos2
  have t3hi := le_cdiv (-((tn * ONE : ℕ) : ℤ)) hpos2
  have t4lo := fdiv_le (-((tn * LPHI : ℕ) : ℤ)) hpos2
  have t4hi := le_cdiv (-((tn * LPLO : ℕ) : ℤ)) hpos2
  have t5 := le_cdiv ((2 ^ tq * ONE : ℕ) : ℤ) hpos2t
  simp only [phaseLo, phaseHi, Int.cast_add, Int.cast_sub, Int.cast_natCast]
  set I1 := (innerBox tn tq k nl).1 with hI1
  set I2 := (innerBox tn tq k nl).2 with hI2
  set F1 := fdiv (I1 * (tn : ℤ)) (4 * 2 ^ tq) with hF1
  set G1 := cdiv (I2 * (tn : ℤ)) (4 * 2 ^ tq) with hG1
  set F2 := fdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) with hF2
  set G2 := cdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) with hG2
  set C2 := cdiv ((2 ^ tq * 2 ^ tq * 2 ^ tq * ONE : ℕ) : ℤ) (96 * tn * tn * tn) with hC2
  set F3 := fdiv (-((tn * ONE : ℕ) : ℤ)) (2 * 2 ^ tq) with hF3
  set G3 := cdiv (-((tn * ONE : ℕ) : ℤ)) (2 * 2 ^ tq) with hG3
  set F4 := fdiv (-((tn * LPHI : ℕ) : ℤ)) (2 * 2 ^ tq) with hF4
  set G4 := cdiv (-((tn * LPLO : ℕ) : ℤ)) (2 * 2 ^ tq) with hG4
  set G5 := cdiv ((2 ^ tq * ONE : ℕ) : ℤ) (2 * tn) with hG5
  set t : ℝ := (tn : ℝ) / 2 ^ tq with ht
  have htpos : 0 < t := by rw [ht]; positivity
  obtain ⟨tb1, tb2⟩ := RSDesignTheta.theta_bracket t htpos Λ hΛ
  unfold RSDesignTheta.thetaS at tb1 tb2
  set L := Real.log (1 / 16 + t ^ 2 / 4) with hL
  -- rewrite each piece's real bound
  have ef : ∀ z : ℤ, ((z * (tn : ℤ) : ℤ) : ℝ) / ((4 * 2 ^ tq : ℕ) : ℝ) = (z : ℝ) * (t / 4) := by
    intro z; rw [ht]; push_cast; field_simp
  rw [ef] at t1lo t1hi
  have e3 : ((-((tn * ONE : ℕ) : ℤ) : ℤ) : ℝ) / ((2 * 2 ^ tq : ℕ) : ℝ) = -t / 2 * 2 ^ 64 := by
    rw [ht]; push_cast; rw [ONE_eq]; field_simp
  rw [e3] at t3lo t3hi
  have e4 : ∀ c : ℕ, ((-((tn * c : ℕ) : ℤ) : ℤ) : ℝ) / ((2 * 2 ^ tq : ℕ) : ℝ) = -(t / 2) * (c : ℝ) := by
    intro c; rw [ht]; push_cast; field_simp
  rw [e4] at t4lo t4hi
  have e5 : (((2 ^ tq * ONE : ℕ) : ℤ) : ℝ) / ((2 * tn : ℕ) : ℝ) = 1 / (2 * t) * 2 ^ 64 := by
    rw [ht]; push_cast; rw [ONE_eq]; field_simp
  rw [e5] at t5
  have m1 : (I1 : ℝ) * (t / 4) ≤ t / 4 * L * 2 ^ 64 := by
    have := mul_le_mul_of_nonneg_right i1 (by positivity : (0 : ℝ) ≤ t / 4)
    linarith
  have m2 : t / 4 * L * 2 ^ 64 ≤ (I2 : ℝ) * (t / 4) := by
    have := mul_le_mul_of_nonneg_right i2 (by positivity : (0 : ℝ) ≤ t / 4)
    linarith
  obtain ⟨lp1, lp2⟩ := logpi_scaled
  have m4lo : -(t / 2) * (LPHI : ℝ) ≤ -(t / 2 * Real.log π) * 2 ^ 64 := by
    have := mul_le_mul_of_nonneg_left lp2 (by positivity : (0 : ℝ) ≤ t / 2)
    linarith
  have m4hi : -(t / 2 * Real.log π) * 2 ^ 64 ≤ -(t / 2) * (LPLO : ℝ) := by
    have := mul_le_mul_of_nonneg_left lp1 (by positivity : (0 : ℝ) ≤ t / 2)
    linarith
  have htarc : 2 * ((tn : ℝ) / 2 ^ tq) = 2 * t := by rw [ht]
  rw [htarc] at a1 a2
  constructor
  · have hφ := mul_le_mul_of_nonneg_right tb1 hP.le
    have : (t / 4 * L - 1 / 4 * Real.arctan (2 * t) - t / 2 - t / 2 * Real.log π - 1 / (2 * t))
        * 2 ^ 64 = t / 4 * L * 2 ^ 64 + -(1 / 4) * Real.arctan (2 * t) * 2 ^ 64 + -t / 2 * 2 ^ 64
          + -(t / 2 * Real.log π) * 2 ^ 64 - 1 / (2 * t) * 2 ^ 64 := by ring
    linarith
  · have hφ := mul_le_mul_of_nonneg_right tb2 hP.le
    have : (t / 4 * L - 1 / 4 * Real.arctan (2 * t) - t / 2 - t / 2 * Real.log π) * 2 ^ 64
        = t / 4 * L * 2 ^ 64 + -(1 / 4) * Real.arctan (2 * t) * 2 ^ 64 + -t / 2 * 2 ^ 64
          + -(t / 2 * Real.log π) * 2 ^ 64 := by ring
    linarith
