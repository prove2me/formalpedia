-- Prove2me | solution 1 for H1000Line.trig_phase
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:05:51.010619+00:00
-- url     : https://prove2.me/submissions/e1e020f5-f084-40d9-af1b-92c146e2df54

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
import Definitions.Def_ArdaRH65K_Turing121_H1000Point
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
import Theorems.Thm_ArbEcon_OrderK_valid64
import Theorems.Thm_ArbEcon_trig_sound
import Theorems.Thm_H1000Line_phase_sound
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
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









/-! ## B. The series `-log (1 - a/b) = Σ_j (a/b)^(j+1)/(j+1)` in fixed point (scale `2^64`). -/





















/-! ## C. Scaled constants: `log 2`, `log π`, `π/8`, `2π` at scale `2^64`. -/
















theorem twopi_scaled : (TPLO : ℝ) ≤ 2 * π * 2 ^ 64 ∧ 2 * π * 2 ^ 64 ≤ TPHI := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  constructor
  · have e : (TPLO : ℝ) ≤ 2 * 3.14159265358979323846 * 2 ^ 64 := by norm_num [TPLO]
    nlinarith
  · have e : 2 * 3.14159265358979323847 * 2 ^ 64 ≤ (TPHI : ℝ) := by norm_num [TPHI]
    nlinarith

/-! ## D. The Riemann-Siegel phase `φ = Λ - (t/2) log π` at `t = tn / 2^tq`. -/





















end

end H1000Line


/-  H1000Point.lean -- the point record and the pieces of the on-line sign certificate (lane
    h1000-prep; consumed by `H1000Line`).

    `LinePt` (height `t = tn / 2^tq`, EM cut, evaluator states, remainder and phase hints, claimed
    sign) and the kernel-evaluable pieces of `ptCheck`: the Dirichlet chunks `dirOk`
    (`ArbEcon.chunk_sound`), the integer zeta ball `zcX, zrX, zcY, zrY` at scale `zW`
    (`zball_sound`, from `EMZetaHighEval.zeta_ballK`, `EMZetaHighCheck.corr_eq`, `remOdd_sound`), the
    shifted phase interval `thLo, thHi` and its `trig` (`trig_phase`, from `H1000Phase.phase_sound` and
    `ArbEcon.trig_sound`), the product ball `sCtr ± sRad` of `S · 2^64 · W` (`s_ball`), and the
    positive magnitude factor of `gLine` (`gLine_eq_mag_mul`).

    Trust: axioms [propext, Classical.choice, Quot.sound] (AxiomGuardH1000Line.lean); no `sorry`.
    conjecture1_proved = False.
-/



open Real Filter Topology
open ArbEcon ArbEcon.OrderK

section
namespace H1000Line
end H1000Line
open H1000Line

noncomputable section

/-! ## E. The point record, the Dirichlet chunks and the integer zeta ball. -/



























/-! ## F. The product ball and the sign test. -/






















theorem solution (p : LinePt) (hph : phaseOk p.tn p.tq p.k = true) (hlo0 : 0 ≤ thLo p) (Λ : ℝ)
    (hΛ : Tendsto (ThetaGap.imLnVal (1 / 4) (tOf p / 2)) atTop (𝓝 Λ)) :
    |Real.cos (phiOf p Λ) * 2 ^ 64 - sgn (trigP p).cs * ((trigP p).cm : ℝ)| ≤ ((trigP p).cr : ℝ) ∧
    |Real.sin (phiOf p Λ) * 2 ^ 64 - sgn (trigP p).ss * ((trigP p).sm : ℝ)| ≤ ((trigP p).sr : ℝ) := by
  obtain ⟨ph1, ph2⟩ := phase_sound p.tn p.tq p.k p.nl hph Λ hΛ
  have ph1' : ((phaseLo p.tn p.tq p.k p.nl : ℤ) : ℝ) ≤ phiOf p Λ * 2 ^ 64 := ph1
  have ph2' : phiOf p Λ * 2 ^ 64 ≤ ((phaseHi p.tn p.tq p.k p.nl : ℤ) : ℝ) := ph2
  obtain ⟨tp1, tp2⟩ := twopi_scaled
  have hm0 : (0 : ℝ) ≤ p.m := by positivity
  have m1 := mul_le_mul_of_nonneg_left tp1 hm0
  have m2 := mul_le_mul_of_nonneg_left tp2 hm0
  have e2 : (phiOf p Λ + (p.m : ℝ) * (2 * π)) * 2 ^ 64
      = phiOf p Λ * 2 ^ 64 + (p.m : ℝ) * (2 * π * 2 ^ 64) := by ring
  have hlo : (((thLo p).toNat : ℕ) : ℝ) ≤ (phiOf p Λ + (p.m : ℝ) * (2 * π)) * 2 ^ 64 := by
    have e : (((thLo p).toNat : ℕ) : ℝ) = ((thLo p : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hlo0]
    rw [e, e2]
    simp only [thLo, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    linarith
  have hhi : (phiOf p Λ + (p.m : ℝ) * (2 * π)) * 2 ^ 64 ≤ (((thHi p).toNat : ℕ) : ℝ) := by
    have e : ((thHi p : ℤ) : ℝ) ≤ (((thHi p).toNat : ℕ) : ℝ) := by
      rw [← Int.cast_natCast]; exact_mod_cast Int.self_le_toNat (thHi p)
    refine le_trans ?_ e
    rw [e2]
    simp only [thHi, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    linarith
  have htr := trig_sound (cfg64 p.tn p.tq) (tOf p) 9 (valid64 p.tn p.tq (tOf p) rfl)
    (phiOf p Λ + (p.m : ℝ) * (2 * π)) _ _ hlo hhi
  obtain ⟨hc, hsn, _, _⟩ := htr
  unfold SBall at hc hsn
  rw [Real.cos_add_nat_mul_two_pi] at hc
  rw [Real.sin_add_nat_mul_two_pi] at hsn
  exact ⟨hc, hsn⟩
