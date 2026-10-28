-- Prove2me | solution 1 for H1000Line.lnBox_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:00:17.035024+00:00
-- url     : https://prove2.me/submissions/0c1cfc56-0aff-4b20-a3ab-cbb2751e9304

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
/-  Probes/ArbEconomics_Sound.lean -- soundness of the Nat-only zeta evaluator (ArbEconomics_Eval).

    Every function of `ArbEconomics_Eval` is shown to produce a TRUE enclosure:
      * `logInc`   : `S <= (log m - log (m-1)) 2^P <= S + K + T`
                     (Mathlib `Real.hasSum_pow_div_log_of_abs_lt_one`, `abs_log_sub_add_sum_range_le`);
      * `termOf`   : `Rlo <= 2^P / sqrt m <= Rhi` for ANY Newton iterate (two-sided validation);
      * `trig`     : cos/sin balls of `theta` from the (pi/2)-reduction, the Horner scheme
                     (Mathlib `Complex.exp_bound`) and the quadrant rotation;
      * `step`/`run` : the loop invariant `Inv` (log bracket + Re/Im balls of the partial zeta sum).

    The main theorem `run_sound` turns a kernel-checked chunk equation
    `St.beq (run cfg L s) s' = true` into `Inv n s -> Inv (n + L) s'`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/










open Real Finset

namespace ArbEcon

/-! ## A. floor division / shifts, cast to ℝ -/

theorem natdiv_le (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

theorem lt_natdiv_add_one (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b < ((a / b : ℕ) : ℝ) + 1 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hbR]
  have h1 : a < (a / b + 1) * b := by
    have := Nat.lt_div_mul_add (a := a) hb
    nlinarith [this]
  have h2 : ((a : ℕ) : ℝ) < (((a / b + 1) * b : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith







/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/










/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/


























/-! ## H. the zeta term, the term product, one step, the run -/























end ArbEcon


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



theorem ONE_eq : ((ONE : ℕ) : ℝ) = 2 ^ 64 := by norm_num [ONE]





theorem lser_zero (one a b i pa pb acc : ℕ) : lser one a b 0 i pa pb acc = (acc, pa, pb) := rfl

theorem lser_succ (one a b n i pa pb acc : ℕ) :
    lser one a b (n + 1) i pa pb acc
      = lser one a b n (i + 1) (pa * a) (pb * b) (acc + pa * one / (pb * (i + 1))) := rfl

theorem lser_spec (one a b : ℕ) : ∀ (n i acc : ℕ),
    lser one a b n i (a ^ (i + 1)) (b ^ (i + 1)) acc
      = (acc + ∑ j ∈ Finset.range n, lterm one a b (i + j), a ^ (i + n + 1), b ^ (i + n + 1)) := by
  intro n
  induction n with
  | zero => intro i acc; simp [lser_zero]
  | succ n ih =>
    intro i acc
    rw [lser_succ, ← pow_succ, ← pow_succ, ih (i + 1)]
    have hs : ∑ j ∈ Finset.range (n + 1), lterm one a b (i + j)
        = lterm one a b i + ∑ j ∈ Finset.range n, lterm one a b (i + 1 + j) := by
      rw [Finset.sum_range_succ', add_comm, add_zero]
      refine congrArg (lterm one a b i + ·) (Finset.sum_congr rfl fun j _ => ?_)
      rw [show i + (j + 1) = i + 1 + j by ring]
    rw [hs]
    have e1 : i + 1 + n + 1 = i + (n + 1) + 1 := by ring
    rw [e1]
    simp only [lterm, Prod.mk.injEq, and_true]
    ring

theorem lser_spec0 (one a b n : ℕ) :
    lser one a b n 0 a b 0 = (∑ j ∈ Finset.range n, lterm one a b j, a ^ (n + 1), b ^ (n + 1)) := by
  have h := lser_spec one a b n 0 0
  simp only [zero_add, pow_one] at h
  exact h





/-! ## C. Scaled constants: `log 2`, `log π`, `π/8`, `2π` at scale `2^64`. -/


















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



















theorem solution (a b nl : ℕ) (hb : 0 < b) (h2 : 2 * a < b) :
    (((lnBox a b nl).1 : ℤ) : ℝ) ≤ -Real.log (1 - (a : ℝ) / b) * 2 ^ 64 ∧
    -Real.log (1 - (a : ℝ) / b) * 2 ^ 64 ≤ (((lnBox a b nl).2 : ℤ) : ℝ) := by
  have hspec := lser_spec0 ONE a b nl
  simp only [lnBox, hspec]
  set S := ∑ j ∈ Finset.range nl, lterm ONE a b j with hS
  set EU : ℕ := a ^ (nl + 1) * ONE * b / (b ^ (nl + 1) * (b - a)) + 1 with hEU
  set x : ℝ := (a : ℝ) / b with hx
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : a < b := by omega
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 / 2 := by
    rw [hx, div_lt_iff₀ hbR]
    have : ((2 * a : ℕ) : ℝ) < b := by exact_mod_cast h2
    push_cast at this; linarith
  have hP : (0 : ℝ) < 2 ^ 64 := by positivity
  -- each floored term against the exact term
  have hterm : ∀ j : ℕ, (lterm ONE a b j : ℝ) ≤ x ^ (j + 1) / ((j : ℝ) + 1) * 2 ^ 64 ∧
      x ^ (j + 1) / ((j : ℝ) + 1) * 2 ^ 64 < (lterm ONE a b j : ℝ) + 1 := by
    intro j
    have e : x ^ (j + 1) / ((j : ℝ) + 1) * 2 ^ 64
        = ((a ^ (j + 1) * ONE : ℕ) : ℝ) / ((b ^ (j + 1) * (j + 1) : ℕ) : ℝ) := by
      rw [hx, div_pow]; push_cast; rw [ONE_eq]; field_simp
    rw [e]
    have hpos : 0 < b ^ (j + 1) * (j + 1) := by positivity
    exact ⟨natdiv_le _ _, lt_natdiv_add_one _ _ hpos⟩
  have hsum_lo : (S : ℝ) ≤ (∑ j ∈ Finset.range nl, x ^ (j + 1) / ((j : ℝ) + 1)) * 2 ^ 64 := by
    rw [hS, Finset.sum_mul]; push_cast
    exact Finset.sum_le_sum (fun j _ => (hterm j).1)
  have hsum_hi : (∑ j ∈ Finset.range nl, x ^ (j + 1) / ((j : ℝ) + 1)) * 2 ^ 64 ≤ (S : ℝ) + nl := by
    rw [hS, Finset.sum_mul]; push_cast
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range nl) => (hterm j).2.le)
    rw [Finset.sum_add_distrib] at h
    simpa using h
  -- the Mathlib remainder bound
  have habs := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; linarith) nl
  rw [abs_of_nonneg hx0] at habs
  have hbaR : (0 : ℝ) < (b : ℝ) - a := by
    have : (a : ℝ) < b := by exact_mod_cast hab
    linarith
  have htail : x ^ (nl + 1) / (1 - x) * 2 ^ 64 ≤ (EU : ℝ) := by
    have h1 : (1 : ℝ) - (a : ℝ) / b = ((b : ℝ) - a) / b := by field_simp
    have e : x ^ (nl + 1) / (1 - x) * 2 ^ 64
        = ((a ^ (nl + 1) * ONE * b : ℕ) : ℝ) / ((b ^ (nl + 1) * (b - a) : ℕ) : ℝ) := by
      rw [hx, h1, div_pow]
      push_cast [Nat.cast_sub hab.le]
      rw [ONE_eq]
      field_simp
    rw [e, hEU]
    have hpos : 0 < b ^ (nl + 1) * (b - a) := by
      have : 0 < b - a := by omega
      positivity
    have := lt_natdiv_add_one (a ^ (nl + 1) * ONE * b) (b ^ (nl + 1) * (b - a)) hpos
    push_cast at this ⊢
    linarith
  have hsplit : -Real.log (1 - x) * 2 ^ 64
      = (∑ j ∈ Finset.range nl, x ^ (j + 1) / ((j : ℝ) + 1)) * 2 ^ 64
        - ((∑ j ∈ Finset.range nl, x ^ (j + 1) / ((j : ℝ) + 1)) + Real.log (1 - x)) * 2 ^ 64 := by
    ring
  have hmid := abs_le.mp habs
  have hm1 : -(x ^ (nl + 1) / (1 - x)) * 2 ^ 64
      ≤ ((∑ j ∈ Finset.range nl, x ^ (j + 1) / ((j : ℝ) + 1)) + Real.log (1 - x)) * 2 ^ 64 :=
    mul_le_mul_of_nonneg_right hmid.1 hP.le
  have hm2 : ((∑ j ∈ Finset.range nl, x ^ (j + 1) / ((j : ℝ) + 1)) + Real.log (1 - x)) * 2 ^ 64
      ≤ x ^ (nl + 1) / (1 - x) * 2 ^ 64 :=
    mul_le_mul_of_nonneg_right hmid.2 hP.le
  push_cast
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith
