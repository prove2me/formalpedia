-- Prove2me | solution 1 for H1000Line.arctan_part
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:54:33.417975+00:00
-- url     : https://prove2.me/submissions/00c39cc7-e756-49c5-a1d6-b7108cdc2401

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
import Theorems.Thm_ArctanTaylor_arctan_le_self
import Theorems.Thm_ArctanTaylor_self_sub_cube_le_arctan
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














theorem pi8_scaled : (P8LO : ℝ) ≤ π / 8 * 2 ^ 64 ∧ π / 8 * 2 ^ 64 ≤ P8HI := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  constructor
  · have e : (P8LO : ℝ) ≤ 3.14159265358979323846 / 8 * 2 ^ 64 := by norm_num [P8LO]
    nlinarith
  · have e : 3.14159265358979323847 / 8 * 2 ^ 64 ≤ (P8HI : ℝ) := by norm_num [P8HI]
    nlinarith



/-! ## D. The Riemann-Siegel phase `φ = Λ - (t/2) log π` at `t = tn / 2^tq`. -/





















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


















theorem solution {tn tq : ℕ} (htn : 1 ≤ tn) :
    ((fdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) : ℤ) : ℝ)
        - ((cdiv ((2 ^ tq * 2 ^ tq * 2 ^ tq * ONE : ℕ) : ℤ) (96 * tn * tn * tn) : ℤ) : ℝ)
        - (P8HI : ℝ)
      ≤ -(1 / 4) * Real.arctan (2 * ((tn : ℝ) / 2 ^ tq)) * 2 ^ 64 ∧
    -(1 / 4) * Real.arctan (2 * ((tn : ℝ) / 2 ^ tq)) * 2 ^ 64
      ≤ ((cdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) : ℤ) : ℝ) - (P8LO : ℝ) := by
  have htnR : (0 : ℝ) < tn := by exact_mod_cast htn
  have hq : (0 : ℝ) < 2 ^ tq := by positivity
  set w : ℝ := (2 : ℝ) ^ tq / (2 * tn) with hw
  have hw0 : 0 ≤ w := by positivity
  have harc : Real.arctan (2 * ((tn : ℝ) / 2 ^ tq)) = π / 2 - Real.arctan w := by
    have h := Real.arctan_inv_of_pos (x := 2 * ((tn : ℝ) / 2 ^ tq)) (by positivity)
    have hinv : (2 * ((tn : ℝ) / 2 ^ tq))⁻¹ = w := by rw [hw]; field_simp
    rw [hinv] at h
    linarith
  have a1 := ArctanTaylor.arctan_le_self hw0
  have a2 := ArctanTaylor.self_sub_cube_le_arctan hw0
  obtain ⟨p1, p2⟩ := pi8_scaled
  have hpos1 : 0 < 8 * tn := by omega
  have hpos2 : 0 < 96 * tn * tn * tn := by positivity
  have f1 := fdiv_le ((2 ^ tq * ONE : ℕ) : ℤ) hpos1
  have c1 := le_cdiv ((2 ^ tq * ONE : ℕ) : ℤ) hpos1
  have c2 := le_cdiv ((2 ^ tq * 2 ^ tq * 2 ^ tq * ONE : ℕ) : ℤ) hpos2
  have e1 : (((2 ^ tq * ONE : ℕ) : ℤ) : ℝ) / ((8 * tn : ℕ) : ℝ) = w / 4 * 2 ^ 64 := by
    rw [hw]; push_cast; rw [ONE_eq]; field_simp; ring
  have e2 : (((2 ^ tq * 2 ^ tq * 2 ^ tq * ONE : ℕ) : ℤ) : ℝ) / ((96 * tn * tn * tn : ℕ) : ℝ)
      = w ^ 3 / 12 * 2 ^ 64 := by
    rw [hw]; push_cast; rw [ONE_eq]; field_simp; ring
  rw [e1] at f1 c1
  rw [e2] at c2
  set F := ((fdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) : ℤ) : ℝ)
  set C1 := ((cdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) : ℤ) : ℝ)
  set C2 := ((cdiv ((2 ^ tq * 2 ^ tq * 2 ^ tq * ONE : ℕ) : ℤ) (96 * tn * tn * tn) : ℤ) : ℝ)
  rw [harc]
  have hP : (0 : ℝ) < 2 ^ 64 := by positivity
  have b1 := mul_le_mul_of_nonneg_right a1 hP.le
  have b2 := mul_le_mul_of_nonneg_right a2 hP.le
  constructor
  · have : -(1 / 4) * (π / 2 - Real.arctan w) * 2 ^ 64
        = -(π / 8 * 2 ^ 64) + Real.arctan w * 2 ^ 64 / 4 := by ring
    rw [this]
    have : (w - w ^ 3 / 3) * 2 ^ 64 / 4 = w / 4 * 2 ^ 64 - w ^ 3 / 12 * 2 ^ 64 := by ring
    linarith
  · have : -(1 / 4) * (π / 2 - Real.arctan w) * 2 ^ 64
        = -(π / 8 * 2 ^ 64) + Real.arctan w * 2 ^ 64 / 4 := by ring
    rw [this]
    have : w * 2 ^ 64 / 4 = w / 4 * 2 ^ 64 := by ring
    linarith
