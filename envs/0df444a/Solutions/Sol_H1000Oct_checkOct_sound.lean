-- Prove2me | solution 1 for H1000Oct.checkOct_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:05:07.180024+00:00
-- url     : https://prove2.me/submissions/c4695a83-d620-4cca-b591-2bd3f7a53618

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabClear
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
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
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
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
import Theorems.Thm_ArbEcon_Off_corr_eqG
import Theorems.Thm_ArbEcon_Off_wball_sound
import Theorems.Thm_H1000Oct_oct_ball
import Theorems.Thm_ZetaReflection_EMHigh_emCorr_re_im
namespace ArbEcon
end ArbEcon
namespace ArbEcon.Off
end ArbEcon.Off
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  EMZetaOfflineSound.lean -- soundness of the off-line Nat-only evaluator (EMZetaOfflineEval).

    Every function of `EMZetaOfflineEval` produces a TRUE enclosure:
      * `imul_sound`     : the product `x · v` of a nonnegative bracket and a term ball;
      * `ampl_sound`     : the validated Newton root brackets `2^P m^(-σ)`, `σ = (a - b)/q`
                           (for ANY Newton output: the two kernel comparisons decide the bracket);
      * `termTB_sound`   : the term ball of `m^(-s) = m^(-σ)(cos θ - i sin θ)`, `θ = t log m`;
      * `addChain_sound` : accumulator `k` receives `(log m)^k m^(-s)`;
      * `stepO_sound`, `runO_sound`, `chunkO_sound` : the loop invariant `InvO` (log bracket and
                           the `p + 1` complex balls of `Σ_{m ≤ n} (log m)^k m^(-s)`).
    The log increment and the cos/sin kernels are `ArbEcon.logInc`/`ArbEcon.trig`, whose soundness
    (`ArbEcon.logInc_bound`, `ArbEcon.trig_sound`) is reused unchanged.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/



open Real Finset

namespace ArbEcon

namespace Off



/-! ## A. Specifications. -/















/-! ## B. The bracket-times-ball product. -/



/-! ## C. Term balls, accumulation, the log chain. -/







/-! ## D. The validated amplitude bracket. -/





/-! ## E. The term `m^(-s)`. -/





/-! ## F. The partial sums. -/

theorem psumK_succ (σ t : ℝ) (k n : ℕ) :
    psumK σ t k (n + 1) = psumK σ t k n
      + ((Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ k * (((n + 1 : ℕ) : ℕ) : ℂ) ^ (-sOfG σ t) := by
  simp only [psumK]
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]





/-! ## G. One step, the run, the chunks. -/

















end Off

end ArbEcon


/-  EMZetaOfflineSlabCheck.lean -- lane offline: the KERNEL checker of a zero-free cell.

    The off-line evaluator run at a center `c = σc + i tc` with `p + 1` accumulators gives, after
    `N - 1` and `N` terms, balls of `S_k = Σ_{n<N} (log n)^k n^(-c)` and of `S_k + (log N)^k N^(-c)`.
    With the exact correction factor `emCorr K c N = (BreN + i BimN)/BD` (`corrDataG`) they give balls
    of the Taylor weights `W_k = S_k + (log N)^k N^(-c) emCorr K c N` of `EMZetaOfflineSlab`.

      * `wData`, `wball_sound`  -- the ball of `W_k`, scaled by `2^P BD`;
      * `sumM`, `sumM_sound`    -- `Σ_{k≥1} ‖W_k‖ rn^k rd^(p-k) (p!/k!)` from above;
      * `checkCell`, `checkCell_sound` -- ONE Boolean check (run by `decide +kernel`) proving
                                   `Σ_{k=1}^p ‖W_k‖ r^k/k! + FN/FD < ‖W_0‖`, `r = rn/rd`, the
                                   hypothesis `hmain` of `zeta_ne_zero_of_cell`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing about RH.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

/-! ## A. The Taylor weights from the evaluator's partial sums. -/

theorem Wk_eq_psumK (K N : ℕ) (hN : 1 ≤ N) (σ t : ℝ) (k : ℕ) :
    Wk K N (sOfG σ t) k = psumK σ t k (N - 1)
      + (psumK σ t k N - psumK σ t k (N - 1)) * emCorr K (sOfG σ t) N := by
  have hNm : N - 1 + 1 = N := by omega
  have hsucc := psumK_succ σ t k (N - 1)
  rw [hNm] at hsucc
  rw [hsucc]
  simp only [Wk, psumK]
  rw [hNm]
  push_cast
  ring

/-! ## B. The ball of a weight. -/









/-! ## C. The weighted sum over `k ≥ 1`. -/





/-! ## D. The cell checker. -/









end Off

end ArbEcon


/-  H1000Octant.lean -- lane h1000-integrate: the kernel-checked OCTANT PIECE, the evaluator side of
    brick K6c (`ArgHoriz`) for the horizontal edges `[2, -1] + i T` of the RvM rectangles.

    `ArgHoriz.hAH_of_octCert_boxes` reduces `argChangeHoriz ζ T 2 (-1) ∈ [L, H]` to an octant
    certificate: breakpoints `2 = p 0 > p 1 > … > p m = -1`, one octant label `k j` per piece, and
    the no-crossing facts `0 < octX (k j) ζ(x + i T)` for every `x` of piece `j`, plus two point
    enclosures at `x = 2` and `x = -1`.  This file proves the no-crossing fact of ONE piece from ONE
    run of the off-line evaluator (`EMZetaOfflineEval`, `p + 1` accumulators) at the piece center
    `c = σc + i tc` and ONE Boolean check run by `decide +kernel`:

      A1. `emCorr_sub_le_norm`, `norm_emCorr_le_norm` -- the correction-factor bounds of
          `EMZetaOfflineSlab` with `a ≤ ‖c - 1‖` in place of `a ≤ Im c` (so they hold near `s = 1`
          at small heights);
      A2. `emFinite_taylor_le_G` -- the Taylor model of the EM finite part for ANY real part of the
          center: `‖n^(-c)‖ ≤ G` for `n ≤ N` (`G = 1` for `σc ≥ 0`, `N^(-σc)` for `σc < 0`);
      B.  `pochNormSq_mono_abs`, `em_remainder_horiz` -- the order-(2K+1) remainder uniformly on a
          horizontal segment `xlo ≤ x ≤ xhi` (negative `x` allowed, `x > -2K`);
          `natCpow_norm_le_of_pow` -- the `G` certificate `Gd^q N^b ≤ Gn^q N^a`;
      C.  `octLo`, `octUp`, `sumOct`, `checkOct`, `checkOct_sound` -- the kernel check
          `Σ_{k=1}^p |octX (W_k)| r^k/k! + (|α| + |β|) F < octX (W_0)` on the evaluator balls;
      D.  `piece_octX_pos` -- THE PIECE: for every real `x` with `|x - σc| ≤ r`,
          `0 < ArgHoriz.octX kk (ζ(x + i tc))`.  Along a horizontal piece `h = x - σc` is REAL, so
          the octant projection of the Taylor polynomial is a real polynomial in `h` and only the
          projections `octX (W_k)` enter;
      E.  `abs_sub_le_of_mem_uIcc`, `budget_mono` -- small helpers for the generated certificates.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (AxiomGuardAllZerosKernel_h1000).  No `sorry`.
    conjecture1_proved = False.  Finite interval arithmetic along finitely many segments; nothing
    here bears on the Riemann Hypothesis.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace H1000Oct

open ArbEcon ArbEcon.Off

/-! ## A1. The correction factor, with `a ≤ ‖c - 1‖`. -/





/-! ## A2. The Taylor model for any real part of the center. -/



/-! ## B. The remainder along a horizontal segment, and the `G` certificate. -/









/-! ## C. The kernel check of a piece. -/



theorem octX_eq_octXv (kk : ℤ) (w : ℂ) :
    ArgHoriz.octX kk w = octXv (ArgHoriz.octA kk) (ArgHoriz.octB kk) w := rfl













theorem natAbs_cast (α : ℤ) : (((α.natAbs : ℤ)) : ℝ) = |(α : ℝ)| := by
  rw [Int.natCast_natAbs, Int.cast_abs]





theorem sumOct_sound (P : ℕ) (f1 f2 : ℕ → ℂ) (B : ℂ) (α β BreN BimN BD : ℤ) (hBD : (0 : ℝ) < BD)
    (hBre : B.re = (BreN : ℝ) / BD) (hBim : B.im = (BimN : ℝ) / BD) (rn rd p : ℕ) :
    ∀ (m k : ℕ) (xs1 xs2 : List Acc), xs1.length = m → xs2.length = m →
      AccsOK P f1 k xs1 → AccsOK P f2 k xs2 →
      ∑ j ∈ Finset.Ico k (k + m), |octXv α β (f1 j + (f2 j - f1 j) * B)| * (2 ^ P * BD)
          * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ))
        ≤ (sumOct α β BreN BimN BD rn rd p k xs1 xs2 : ℝ) := by
  have hS : (0 : ℝ) < 2 ^ P * BD := by positivity
  intro m
  induction m with
  | zero =>
    intro k xs1 xs2 hl1 hl2 _ _
    rw [List.length_eq_zero_iff] at hl1 hl2
    subst hl1; subst hl2
    simp [sumOct]
  | succ m ih =>
    intro k xs1 xs2 hl1 hl2 hA1 hA2
    match xs1, xs2, hl1, hl2, hA1, hA2 with
    | x1 :: ys1, x2 :: ys2, hl1, hl2, hA1, hA2 =>
      obtain ⟨hx1, hy1⟩ := hA1
      obtain ⟨hx2, hy2⟩ := hA2
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl1 hl2
      have hrec := ih (k + 1) ys1 ys2 hl1 hl2 hy1 hy2
      have hb := wball_sound P (f1 k) (f2 k) x1 x2 hx1 hx2 BreN BimN BD hBD B hBre hBim
      have hre : |(f1 k + (f2 k - f1 k) * B).re * (2 ^ P * BD) - ((wData BreN BimN BD x1 x2).1 : ℝ)|
          ≤ ((wData BreN BimN BD x1 x2).2.2.1 : ℝ) := by rw [← mul_assoc]; exact hb.1
      have him : |(f1 k + (f2 k - f1 k) * B).im * (2 ^ P * BD) - ((wData BreN BimN BD x1 x2).2.1 : ℝ)|
          ≤ ((wData BreN BimN BD x1 x2).2.2.2 : ℝ) := by rw [← mul_assoc]; exact hb.2
      have hu := (oct_ball α β (f1 k + (f2 k - f1 k) * B) (2 ^ P * BD) hS _ hre him).2
      have hfac : (0 : ℝ) ≤ (rn : ℝ) ^ k * (rd : ℝ) ^ (p - k) * ((p ! / k ! : ℕ) : ℝ) := by positivity
      rw [show k + (m + 1) = (k + 1) + m by ring, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      have hs : (sumOct α β BreN BimN BD rn rd p k (x1 :: ys1) (x2 :: ys2) : ℝ)
          = (octUp α β (wData BreN BimN BD x1 x2) : ℝ) * ((rn : ℝ) ^ k * (rd : ℝ) ^ (p - k)
              * ((p ! / k ! : ℕ) : ℝ)) + (sumOct α β BreN BimN BD rn rd p (k + 1) ys1 ys2 : ℝ) := by
        simp only [sumOct, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]; ring
      rw [hs]
      have := mul_le_mul_of_nonneg_right hu hfac
      linarith









/-! ## D. The piece. -/





/-! ## E. Helpers for the generated certificates. -/







/-! ## F. Closed forms for the generated budgets (K ≤ 6), and the slab-cell wrapper. -/











/-! ## G. Generated-certificate adapters. -/









end H1000Oct


/-  H1000Octant.lean -- lane h1000-integrate: the kernel-checked OCTANT PIECE, the evaluator side of
    brick K6c (`ArgHoriz`) for the horizontal edges `[2, -1] + i T` of the RvM rectangles.

    `ArgHoriz.hAH_of_octCert_boxes` reduces `argChangeHoriz ζ T 2 (-1) ∈ [L, H]` to an octant
    certificate: breakpoints `2 = p 0 > p 1 > … > p m = -1`, one octant label `k j` per piece, and
    the no-crossing facts `0 < octX (k j) ζ(x + i T)` for every `x` of piece `j`, plus two point
    enclosures at `x = 2` and `x = -1`.  This file proves the no-crossing fact of ONE piece from ONE
    run of the off-line evaluator (`EMZetaOfflineEval`, `p + 1` accumulators) at the piece center
    `c = σc + i tc` and ONE Boolean check run by `decide +kernel`:

      A1. `emCorr_sub_le_norm`, `norm_emCorr_le_norm` -- the correction-factor bounds of
          `EMZetaOfflineSlab` with `a ≤ ‖c - 1‖` in place of `a ≤ Im c` (so they hold near `s = 1`
          at small heights);
      A2. `emFinite_taylor_le_G` -- the Taylor model of the EM finite part for ANY real part of the
          center: `‖n^(-c)‖ ≤ G` for `n ≤ N` (`G = 1` for `σc ≥ 0`, `N^(-σc)` for `σc < 0`);
      B.  `pochNormSq_mono_abs`, `em_remainder_horiz` -- the order-(2K+1) remainder uniformly on a
          horizontal segment `xlo ≤ x ≤ xhi` (negative `x` allowed, `x > -2K`);
          `natCpow_norm_le_of_pow` -- the `G` certificate `Gd^q N^b ≤ Gn^q N^a`;
      C.  `octLo`, `octUp`, `sumOct`, `checkOct`, `checkOct_sound` -- the kernel check
          `Σ_{k=1}^p |octX (W_k)| r^k/k! + (|α| + |β|) F < octX (W_0)` on the evaluator balls;
      D.  `piece_octX_pos` -- THE PIECE: for every real `x` with `|x - σc| ≤ r`,
          `0 < ArgHoriz.octX kk (ζ(x + i tc))`.  Along a horizontal piece `h = x - σc` is REAL, so
          the octant projection of the Taylor polynomial is a real polynomial in `h` and only the
          projections `octX (W_k)` enter;
      E.  `abs_sub_le_of_mem_uIcc`, `budget_mono` -- small helpers for the generated certificates.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (AxiomGuardAllZerosKernel_h1000).  No `sorry`.
    conjecture1_proved = False.  Finite interval arithmetic along finitely many segments; nothing
    here bears on the Riemann Hypothesis.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace H1000Oct
end H1000Oct
open H1000Oct

open ArbEcon ArbEcon.Off

/-! ## A1. The correction factor, with `a ≤ ‖c - 1‖`. -/





/-! ## A2. The Taylor model for any real part of the center. -/



/-! ## B. The remainder along a horizontal segment, and the `G` certificate. -/









/-! ## C. The kernel check of a piece. -/
































set_option maxHeartbeats 2000000
theorem solution (c : Cfg) (o : OCfg) (σ t : ℝ) (hσ : σ = ((o.a : ℝ) - o.b) / o.q)
    (ht : t = (c.tn : ℝ) / 2 ^ c.tq) (K N p : ℕ) (xs1 xs2 : List Acc) (rn rd FN FD : ℕ) (kk : ℤ)
    (h1 : AccsOK c.P (fun k => psumK σ t k (N - 1)) 0 xs1)
    (h2 : AccsOK c.P (fun k => psumK σ t k N) 0 xs2)
    (hc : checkOct c o K N p xs1 xs2 rn rd FN FD kk = true) :
    ∑ k ∈ Finset.Ico 1 (p + 1), |ArgHoriz.octX kk (Wk K N (sOfG σ t) k)| * ((rn : ℝ) / rd) ^ k
        / (k ! : ℝ)
      + (|((ArgHoriz.octA kk : ℤ) : ℝ)| + |((ArgHoriz.octB kk : ℤ) : ℝ)|) * ((FN : ℝ) / FD)
      < ArgHoriz.octX kk (Wk K N (sOfG σ t) 0) := by
  match xs1, xs2, h1, h2, hc with
  | x1 :: ys1, x2 :: ys2, h1, h2, hc =>
    simp only [checkOct, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hK1, hK6⟩, hN2⟩, hrd⟩, hFD⟩, hq1⟩, htn1⟩, hl1⟩, hl2⟩, hmainZ⟩ := hc
    have hl1' : ys1.length = p := Nat.eq_of_beq_eq_true hl1
    have hl2' : ys2.length = p := Nat.eq_of_beq_eq_true hl2
    obtain ⟨hx1, hy1⟩ := h1
    obtain ⟨hx2, hy2⟩ := h2
    set u : ℕ := 2 ^ c.tq with hudef
    have hu : 0 < u := Nat.two_pow_pos _
    have huR : (0 : ℝ) < u := by exact_mod_cast hu
    have ht' : t = (c.tn : ℝ) / u := by rw [ht, hudef]; push_cast; ring
    have hσ' : σ = (((o.a : ℤ) - o.b : ℤ) : ℝ) / o.q := by rw [hσ]; push_cast; ring
    obtain ⟨hcre, hcim⟩ := corr_eqG K ((o.a : ℤ) - o.b) o.q u c.tn N hK1 hK6 (by omega) hu
      (by omega) (by omega) σ t hσ' ht'
    set cd := corrDataG K ((o.a : ℤ) - o.b) o.q u c.tn N with hcd
    have hqR : (0 : ℝ) < o.q := by exact_mod_cast (show 0 < o.q by omega)
    have htnR : (0 : ℝ) < c.tn := by exact_mod_cast (show 0 < c.tn by omega)
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hBDpos : (0 : ℝ) < (cd.2.2 : ℝ) := by
      have e : (cd.2.2 : ℝ) = 2 * (((((o.a : ℤ) - o.b : ℤ) : ℝ) - o.q) ^ 2 * (u : ℝ) ^ 2
          + (c.tn : ℝ) ^ 2 * (o.q : ℝ) ^ 2) * ((ArbEcon.OrderK.Lbeta : ℝ) * ((o.q : ℝ) * u * N) ^ (2 * K - 1)) := by
        simp only [hcd, corrDataG]; push_cast; ring
      rw [e]
      have hL : (0 : ℝ) < (ArbEcon.OrderK.Lbeta : ℝ) := by norm_num [ArbEcon.OrderK.Lbeta]
      positivity
    set B := emCorr K (sOfG σ t) N with hB
    have hBre : B.re = (cd.1 : ℝ) / cd.2.2 := by rw [← hcre]; exact (emCorr_re_im K σ t N).1
    have hBim : B.im = (cd.2.1 : ℝ) / cd.2.2 := by rw [← hcim]; exact (emCorr_re_im K σ t N).2
    have hW : ∀ k, Wk K N (sOfG σ t) k = psumK σ t k (N - 1) + (psumK σ t k N - psumK σ t k (N - 1)) * B :=
      fun k => Wk_eq_psumK K N (by omega) σ t k
    simp only [hW, octX_eq_octXv]
    set α := ArgHoriz.octA kk with hα
    set β := ArgHoriz.octB kk with hβ
    set S : ℝ := 2 ^ c.P * cd.2.2 with hS
    have hP : (0 : ℝ) < 2 ^ c.P := by positivity
    have hSpos : 0 < S := by positivity
    -- the k = 0 ball
    have hb0 := wball_sound c.P (psumK σ t 0 (N - 1)) (psumK σ t 0 N) x1 x2 hx1 hx2 cd.1 cd.2.1 cd.2.2
      hBDpos B hBre hBim
    set d0 := wData cd.1 cd.2.1 cd.2.2 x1 x2 with hd0
    set W0 := psumK σ t 0 (N - 1) + (psumK σ t 0 N - psumK σ t 0 (N - 1)) * B with hW0
    have hre0 : |W0.re * S - (d0.1 : ℝ)| ≤ (d0.2.2.1 : ℝ) := by rw [hS, ← mul_assoc]; exact hb0.1
    have him0 : |W0.im * S - (d0.2.1 : ℝ)| ≤ (d0.2.2.2 : ℝ) := by rw [hS, ← mul_assoc]; exact hb0.2
    have hlo0 := (oct_ball α β W0 S hSpos d0 hre0 him0).1
    -- the k ≥ 1 sum
    have hsum := sumOct_sound c.P (fun k => psumK σ t k (N - 1)) (fun k => psumK σ t k N) B α β cd.1
      cd.2.1 cd.2.2 hBDpos hBre hBim rn rd p p 1 ys1 ys2 hl1' hl2' hy1 hy2
    rw [show 1 + p = p + 1 by ring] at hsum
    set Msum : ℝ := (sumOct α β cd.1 cd.2.1 cd.2.2 rn rd p 1 ys1 ys2 : ℝ) with hMsum
    set T : ℝ := (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) * FD with hT
    have hrdR : (0 : ℝ) < rd := by exact_mod_cast (show 0 < rd by omega)
    have hFDR : (0 : ℝ) < FD := by exact_mod_cast (show 0 < FD by omega)
    have hpf : (0 : ℝ) < ((p ! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos p
    have hTpos : 0 < T := by positivity
    set AB : ℝ := |(α : ℝ)| + |(β : ℝ)| with hAB
    have hRHScast : ((octRHS c o K N p kk ys1 ys2 rn rd FN FD : ℤ) : ℝ)
        = Msum * FD + AB * (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) := by
      simp only [octRHS, hMsum, hS, hAB, hcd, hudef, hα, hβ]
      push_cast [natAbs_cast]
      ring
    have hLHScast : ((octLHS c o K N p kk x1 x2 rd FD : ℤ) : ℝ) = (octLo α β d0 : ℝ) * T := by
      simp only [octLHS, hT, hd0, hcd, hudef, hα, hβ]
      push_cast
      ring
    have hmainR : Msum * FD + AB * (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ)
        < (octLo α β d0 : ℝ) * T := by
      rw [← hRHScast, ← hLHScast]; exact_mod_cast hmainZ
    have h2' := mul_le_mul_of_nonneg_right hlo0 hTpos.le
    have h1' := mul_le_mul_of_nonneg_right hsum hFDR.le
    have hkey : (∑ j ∈ Finset.Ico 1 (p + 1),
          |octXv α β (psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B)| * S
            * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ))) * FD
        + AB * (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) < octXv α β W0 * S * T := by
      have : (∑ j ∈ Finset.Ico 1 (p + 1),
          |octXv α β (psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B)| * (2 ^ c.P * cd.2.2)
            * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ))) * FD ≤ Msum * FD := h1'
      rw [← hS] at this
      linarith
    have hterm : ∀ j ∈ Finset.Ico 1 (p + 1),
        |octXv α β (psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B)| * S
          * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ)) * FD
        = (|octXv α β (psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B)|
            * ((rn : ℝ) / rd) ^ j / (j ! : ℝ)) * (S * T) := by
      intro j hj
      have hjp : j ≤ p := by have := Finset.mem_Ico.mp hj; omega
      have hdvd : j ! ∣ p ! := Nat.factorial_dvd_factorial hjp
      have hjf : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
      have hcast : ((p ! / j ! : ℕ) : ℝ) = ((p ! : ℕ) : ℝ) / (j ! : ℝ) := Nat.cast_div hdvd (ne_of_gt hjf)
      have hpow : (rd : ℝ) ^ p = (rd : ℝ) ^ (p - j) * (rd : ℝ) ^ j := by
        rw [← pow_add]; congr 1; omega
      rw [hcast, hT, hpow, div_pow]
      field_simp
    rw [Finset.sum_mul] at hkey
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul] at hkey
    have hST : 0 < S * T := by positivity
    have e3 : AB * (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) = AB * ((FN : ℝ) / FD) * (S * T) := by
      rw [hT]; field_simp
    rw [e3, ← add_mul, show octXv α β W0 * S * T = octXv α β W0 * (S * T) by ring] at hkey
    exact lt_of_mul_lt_mul_right hkey hST.le
