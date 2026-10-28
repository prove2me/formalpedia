-- Prove2me | solution 1 for H1000Line.s_ball
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:54:39.27506+00:00
-- url     : https://prove2.me/submissions/39bd9521-826b-4227-b352-be16343653fa

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











/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/










/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/






theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]



















/-! ## H. the zeta term, the term product, one step, the run -/























end ArbEcon


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

namespace H1000Line

noncomputable section

/-! ## E. The point record, the Dirichlet chunks and the integer zeta ball. -/



























/-! ## F. The product ball and the sign test. -/

/-- `|αβ - Cc| ≤ r1 (|c| + r2) + |C| r2` from `|α - C| ≤ r1`, `|β - c| ≤ r2`. -/
theorem prod_ball {α β C c r1 r2 : ℝ} (h1 : |α - C| ≤ r1) (h2 : |β - c| ≤ r2) :
    |α * β - C * c| ≤ r1 * (|c| + r2) + |C| * r2 := by
  have e : α * β - C * c = (α - C) * β + C * (β - c) := by ring
  rw [e]
  have hb : |β| ≤ |c| + r2 := by
    have := abs_sub_abs_le_abs_sub β c
    linarith
  have hr1 : 0 ≤ r1 := le_trans (abs_nonneg _) h1
  calc |(α - C) * β + C * (β - c)| ≤ |(α - C) * β| + |C * (β - c)| := abs_add_le _ _
    _ = |α - C| * |β| + |C| * |β - c| := by rw [abs_mul, abs_mul]
    _ ≤ r1 * (|c| + r2) + |C| * r2 :=
        add_le_add (mul_le_mul h1 hb (abs_nonneg _) hr1) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))



theorem sgnI_cast (b : Bool) : ((sgnI b : ℤ) : ℝ) = sgn b := by
  cases b <;> simp [sgnI, sgn]





















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
























theorem solution (p : LinePt) (Λ : ℝ)
    (hc : |Real.cos (phiOf p Λ) * 2 ^ 64 - sgn (trigP p).cs * ((trigP p).cm : ℝ)| ≤ ((trigP p).cr : ℝ))
    (hsn : |Real.sin (phiOf p Λ) * 2 ^ 64 - sgn (trigP p).ss * ((trigP p).sm : ℝ)| ≤ ((trigP p).sr : ℝ))
    (hX : |(riemannZeta (sOf (tOf p))).re * (zW p : ℝ) - (zcX p : ℝ)| ≤ (zrX p : ℝ))
    (hY : |(riemannZeta (sOf (tOf p))).im * (zW p : ℝ) - (zcY p : ℝ)| ≤ (zrY p : ℝ)) :
    |(Real.cos (phiOf p Λ) * (riemannZeta (sOf (tOf p))).re
        - Real.sin (phiOf p Λ) * (riemannZeta (sOf (tOf p))).im) * 2 ^ 64 * (zW p : ℝ)
      - (sCtr p : ℝ)| ≤ (sRad p : ℝ) := by
  have pc := prod_ball hc hX
  have ps := prod_ball hsn hY
  have habsC : |sgn (trigP p).cs * ((trigP p).cm : ℝ)| = ((trigP p).cm : ℝ) := by
    rw [abs_mul, abs_sgn, one_mul, abs_of_nonneg (by positivity)]
  have habsS : |sgn (trigP p).ss * ((trigP p).sm : ℝ)| = ((trigP p).sm : ℝ) := by
    rw [abs_mul, abs_sgn, one_mul, abs_of_nonneg (by positivity)]
  rw [habsC] at pc
  rw [habsS] at ps
  have hctr : ((sCtr p : ℤ) : ℝ) = sgn (trigP p).cs * ((trigP p).cm : ℝ) * (zcX p : ℝ)
      - sgn (trigP p).ss * ((trigP p).sm : ℝ) * (zcY p : ℝ) := by
    simp only [sCtr, Int.cast_sub, Int.cast_mul, Int.cast_natCast, sgnI_cast]
  have hrad : ((sRad p : ℤ) : ℝ) = ((trigP p).cr : ℝ) * (|(zcX p : ℝ)| + (zrX p : ℝ))
      + ((trigP p).cm : ℝ) * (zrX p : ℝ) + ((trigP p).sr : ℝ) * (|(zcY p : ℝ)| + (zrY p : ℝ))
      + ((trigP p).sm : ℝ) * (zrY p : ℝ) := by
    simp only [sRad, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hctr, hrad]
  set X := (riemannZeta (sOf (tOf p))).re
  set Y := (riemannZeta (sOf (tOf p))).im
  have e : (Real.cos (phiOf p Λ) * X - Real.sin (phiOf p Λ) * Y) * 2 ^ 64 * (zW p : ℝ)
      - (sgn (trigP p).cs * ((trigP p).cm : ℝ) * (zcX p : ℝ)
        - sgn (trigP p).ss * ((trigP p).sm : ℝ) * (zcY p : ℝ))
      = (Real.cos (phiOf p Λ) * 2 ^ 64 * (X * (zW p : ℝ))
          - sgn (trigP p).cs * ((trigP p).cm : ℝ) * (zcX p : ℝ))
        - (Real.sin (phiOf p Λ) * 2 ^ 64 * (Y * (zW p : ℝ))
          - sgn (trigP p).ss * ((trigP p).sm : ℝ) * (zcY p : ℝ)) := by ring
  rw [e]
  refine le_trans (abs_sub _ _) ?_
  linarith [pc, ps]
