-- Prove2me | solution 1 for H1000Line.log_inner_eq
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:00:01.113891+00:00
-- url     : https://prove2.me/submissions/94935ad0-b806-4e7e-be32-ebc42df22afc

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


















/-! ## D. The Riemann-Siegel phase `φ = Λ - (t/2) log π` at `t = tn / 2^tq`. -/











theorem phaseOk_spec {tn tq k : ℕ} (h : phaseOk tn tq k = true) :
    2 ^ k ≤ AA tn tq ∧ AA tn tq < 2 * 2 ^ k ∧ 2 * tq + 4 ≤ k ∧ 1 ≤ tn ∧ 2 ^ tq ≤ 2 * tn := by
  simp only [phaseOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩









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














theorem solution {tn tq k : ℕ} (h : phaseOk tn tq k = true) :
    Real.log (1 / 16 + ((tn : ℝ) / 2 ^ tq) ^ 2 / 4)
      = ((k - (2 * tq + 4) : ℕ) : ℝ) * Real.log 2
        + -Real.log (1 - ((AA tn tq - 2 ^ k : ℕ) : ℝ) / (AA tn tq : ℕ)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := phaseOk_spec h
  have hA : (0 : ℝ) < (AA tn tq : ℕ) := by
    have : 0 < AA tn tq := lt_of_lt_of_le (Nat.two_pow_pos k) h1
    exact_mod_cast this
  have hAeq : ((AA tn tq : ℕ) : ℝ) = (2 : ℝ) ^ tq * 2 ^ tq + 4 * tn * tn := by
    simp [AA]
  have e1 : (1 / 16 + ((tn : ℝ) / 2 ^ tq) ^ 2 / 4) = ((AA tn tq : ℕ) : ℝ) / 2 ^ (2 * tq + 4) := by
    rw [hAeq]
    have hq : (0 : ℝ) < 2 ^ tq := by positivity
    rw [show (2 : ℝ) ^ (2 * tq + 4) = (2 ^ tq) ^ 2 * 16 by rw [pow_add, pow_mul']; norm_num]
    field_simp
    ring
  have e2 : (1 : ℝ) - ((AA tn tq - 2 ^ k : ℕ) : ℝ) / (AA tn tq : ℕ) = (2 : ℝ) ^ k / (AA tn tq : ℕ) := by
    rw [Nat.cast_sub h1]
    push_cast
    field_simp
    ring
  have e3 : ((k - (2 * tq + 4) : ℕ) : ℝ) = (k : ℝ) - (2 * tq + 4) := by
    rw [Nat.cast_sub h3]; push_cast; ring
  rw [e1, e2, e3, Real.log_div (ne_of_gt (by positivity)) (ne_of_gt hA),
    Real.log_div (ne_of_gt hA) (ne_of_gt (by positivity)), Real.log_pow, Real.log_pow]
  push_cast
  ring
