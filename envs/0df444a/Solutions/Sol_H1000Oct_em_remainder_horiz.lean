-- Prove2me | solution 1 for H1000Oct.em_remainder_horiz
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:15:58.569782+00:00
-- url     : https://prove2.me/submissions/3174aed5-5884-4ef1-8c0d-190ced03d8e9

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
import Theorems.Thm_H1000Oct_pochNormSq_mono_abs
import Theorems.Thm_ZetaReflection_EMOff_em_zeta_orderK_enclosure_odd_ext
namespace ArbEcon
end ArbEcon
namespace ArbEcon.Off
end ArbEcon.Off
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  EMZetaHigh.lean -- the GENERAL-ORDER Euler-Maclaurin representation of ζ with an explicit,
    PROVED remainder bound (lane emhigh, memo ANDURIL_ARB_DISCHARGE_2026-09-23 section 3 / step 2
    node `AND_em_zeta_orderK`).

    The island's order-3 chain (`EMZetaTail.em_zeta_strip3`) stops at the saw-3 remainder.  This
    file raises the order to ANY `m ≥ 1` by induction, so the finite part carries every Bernoulli
    correction `B_2, B_4, …, B_{2K}` and the remainder decays like `N^{-(Re s + 2K - 1)}`:

      M1.  `poch`, `emC`            -- rising factorial `s(s+1)…(s+k-1)` and the k-th x-derivative
                                       coefficient `(-1)^k (s)_k` of `x^{-s}`.
      M2.  `em_tail_step`           -- ONE saw-order-raising step on the tail `[N, ∞)`, any k ≥ 1
                                       (generalises `EMZetaTail.em_tail2_step` / `em_tail3_step`).
      M3.  `emTail_unroll`          -- the induction: the saw-1 tail equals the explicit Bernoulli
                                       sum plus `(-1)^(m-1) emTail m / m!`.
      M4.  `em_zeta_order`          -- the general-order identity for `riemannZeta` on `Re s > 0`.
      M5.  `emTail_norm_le`         -- remainder bound from any sup bound of the order-m saw.
      M6.  `abs_sawBernoulli_even_le` -- `|B̃_{2K}(x)| ≤ |B_{2K}|` for every K ≥ 1 (Mathlib's
                                       Fourier cosine series of the Bernoulli polynomials).
      M6'. `abs_sawBernoulli_odd_le`  -- `|B̃_{2K+1}(x)| ≤ 2(2K+1)!/(2π)^{2K+1} (1 + (π²/6−1)/2^{2K−1})`
                                       (Fourier sine series + `ζ(p) ≤ 1 + (π²/6−1)/2^{p−2}`).
      M7.  `em_zeta_orderK_enclosure` -- THE THEOREM (general K), even-saw remainder:
             ‖ζ(s) − emFinite K s N‖ ≤ |B_{2K}|/(2K)! · ‖(s)_{2K}‖ · N^{-(σ+2K-1)}/(σ+2K-1),
           and `em_zeta_orderK_enclosure_odd`, the same finite part with the saw-(2K+1) remainder
             ‖ζ(s) − emFinite K s N‖ ≤ 2(1+(π²/6−1)/2^{2K−1})/(2π)^{2K+1} · ‖(s)_{2K+1}‖ · N^{-(σ+2K)}/(σ+2K)
           (smaller by about `|s+2K|/(2πN)`), with the evaluator-facing Dirichlet form
           `emFinite = Σ_{n<N} n^{-s} + N^{-s}·emCorr`; `em_line_remainder_le` / `_odd_le` are the
           critical-line forms with a rational majorant `Q` of the Pochhammer norm and `r ≤ √N`.
      M8.  exact Bernoulli numbers `B_2 … B_12` (the K ≤ 6 constants).

    conjecture1_proved = False.  A classical analysis lemma (Euler-Maclaurin), not a proof of RH.
-/



open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real Nat

namespace ZetaReflection

namespace EMHigh

/-! ## M1. Rising factorial and the derivative coefficients of `x^{-s}`. -/





lemma poch_succ (s : ℂ) (k : ℕ) : poch s (k + 1) = poch s k * (s + k) := rfl

lemma norm_poch_succ (s : ℂ) (k : ℕ) : ‖poch s (k + 1)‖ = ‖poch s k‖ * ‖s + k‖ := by
  rw [poch_succ, norm_mul]











/-! ## M2. The general saw-order-raising step on the tail `[N, ∞)`. -/









/-! ## M3. The induction: unrolling the saw-1 tail to any order. -/





/-! ## M4. The general-order identity for `riemannZeta`. -/





/-! ## M5. The remainder bound from a sup bound of the order-m saw. -/



/-! ## M6. The sup bound `|B̃_{2K}(x)| ≤ |B_{2K}|` (general K ≥ 1). -/





/-! ## M6'. The odd sup bound `|B̃_{2K+1}(x)| ≤ 2 (2K+1)! ζ(2K+1) / (2π)^{2K+1}` (general K ≥ 1),
    with the elementary majorant `ζ(p) ≤ 1 + (π²/6 − 1)/2^(p−2)`. -/







/-! ## M7. THE THEOREM: general-K enclosure, evaluator (Dirichlet) form. -/













/-! ## M7'. The critical line: rational remainder and real/imaginary parts of the correction. -/



theorem norm_poch_sq (σ t : ℝ) (k : ℕ) :
    ‖poch ((σ : ℂ) + (t : ℂ) * I) k‖ ^ 2 = pochNormSq σ t k := by
  induction k with
  | zero => simp [pochNormSq, poch]
  | succ k ih =>
    rw [norm_poch_succ, mul_pow, ih, pochNormSq, Complex.sq_norm, Complex.normSq_apply]
    congr 1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.natCast_re, Complex.add_im, Complex.mul_im, Complex.natCast_im]
    ring

theorem norm_poch_le (σ t : ℝ) (k : ℕ) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ : pochNormSq σ t k ≤ Q ^ 2) :
    ‖poch ((σ : ℂ) + (t : ℂ) * I) k‖ ≤ Q := by
  rw [← norm_poch_sq] at hQ
  have h0 := norm_nonneg (poch ((σ : ℂ) + (t : ℂ) * I) k)
  nlinarith [hQ]





/-! ## M7''. Real and imaginary parts of the correction factor on a vertical line. -/













/-! ## M8. The exact Bernoulli numbers `B_2 … B_12` (the constants of K ≤ 6). -/






















end EMHigh

end ZetaReflection


/-  EMZetaOfflineSlab.lean -- lane offline: zero-free cells OFF the critical line by a Taylor model
    of the Euler-Maclaurin finite part (the analysis behind a `SlabClear` certificate).

    For a center `c = σc + i tc` (`σc ≥ 0`) and a point `s = c + h`, `‖h‖ ≤ r`:

      T1.  `exp_taylor_le`        -- `‖e^w - Σ_{k≤p} w^k/k!‖ ≤ ‖w‖^(p+1) (p+2)/((p+1)!(p+1))`, `‖w‖ ≤ 1`;
      T2.  `natCpow_neg_add`      -- `n^(-(c+h)) = n^(-c) e^(-h log n)`;
      T3.  `norm_poch_sub_le`     -- `‖(c+h)_k - (c)_k‖ ≤ (U+r)^k - U^k` when every `‖c + j‖ ≤ U`;
      T4.  `emCorr_sub_le`        -- the correction factor moves by at most
                                     `δ = N r / a² + Σ_{i<2K-1} |B_{i+2}|/(i+2)! ((U+r)^(i+1) - U^(i+1)) / N^(i+1)`
                                     (`a ≤ Im c`, `a ≤ Im s`);
      T5.  `emFinite_taylor_le`   -- THE TAYLOR MODEL:
                                     `‖emFinite K (c+h) N - Σ_{k≤p} h^k (-1)^k/k! · W_k‖ ≤ Err`, where
                                     `W_k = Σ_{n<N} (log n)^k n^(-c) + (log N)^k N^(-c) emCorr(c)` and
                                     `Err = C_p (r L)^(p+1) ((N-1) + ‖emCorr(c)‖) + 3 δ`, `L ≥ log N`;
      T6.  `em_remainder_region`  -- the order-(2K+1) remainder uniformly on `1/2 ≤ Re s ≤ 1`,
                                     `0 ≤ Im s ≤ B`;
      T7.  `zeta_ne_zero_of_cell` -- a zero at `s` would force `‖Σ_k h^k …‖ ≤ Err + E`; so
                                     `‖W_0‖ > Σ_{k=1}^p ‖W_k‖ r^k / k! + Err + E` rules it out.

    conjecture1_proved = False.  A finite, local nonvanishing argument; nothing about RH.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

/-! ## T1. The complex exponential Taylor remainder. -/







/-! ## T2. Shifting the exponent. -/





/-! ## T3. The Pochhammer symbol moves slowly. -/



/-! ## T4. The correction factor moves slowly. -/





/-! ## T5. The Taylor model of the finite part. -/









/-! ## T6. The order-(2K+1) remainder uniformly on a region. -/



theorem CK_nonneg (K : ℕ) : 0 ≤ CK K := by
  unfold CK
  have : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_three]
  positivity







/-! ## T7. A zero-free cell. -/





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

section
namespace H1000Oct
end H1000Oct
open H1000Oct

open ArbEcon ArbEcon.Off

/-! ## A1. The correction factor, with `a ≤ ‖c - 1‖`. -/





/-! ## A2. The Taylor model for any real part of the center. -/



/-! ## B. The remainder along a horizontal segment, and the `G` certificate. -/




theorem solution (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) (t : ℝ) (ht : t ≠ 0)
    (xlo xhi σs : ℝ) (hpos : 0 < xlo + 2 * K) (hs1 : xhi ≤ σs) (hs2 : -xlo ≤ σs)
    (Qr : ℝ) (hQr0 : 0 ≤ Qr) (hQ : pochNormSq σs t (2 * K + 1) ≤ Qr ^ 2)
    (R : ℝ) (hR : (N : ℝ) ^ (-xlo) ≤ R) :
    ∀ x : ℝ, xlo ≤ x → x ≤ xhi →
      ‖riemannZeta (sOfG x t) - emFinite K (sOfG x t) N‖
        ≤ CK K * Qr * R / (N : ℝ) ^ (2 * K) / (xlo + 2 * K) := by
  intro x hx0 hx1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs1' : sOfG x t ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [sOfG] at this
    exact ht this
  have hsre : (sOfG x t).re = x := by simp [sOfG]
  have henc := EMOff.em_zeta_orderK_enclosure_odd_ext K hK (s := sOfG x t)
    (by rw [hsre]; push_cast; linarith) hs1' hN
  rw [hsre] at henc
  refine le_trans henc ?_
  -- the Pochhammer factor
  have hmono := pochNormSq_mono_abs x t σs |t|
    (by rw [abs_le]; constructor <;> linarith) le_rfl (2 * K + 1)
  have hpq : pochNormSq σs |t| (2 * K + 1) = pochNormSq σs t (2 * K + 1) := by
    have : ∀ k, pochNormSq σs |t| k = pochNormSq σs t k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simp only [pochNormSq, ih, sq_abs]
    exact this _
  rw [hpq] at hmono
  have hpoch : ‖poch (sOfG x t) (2 * K + 1)‖ ≤ Qr := norm_poch_le x t (2 * K + 1) Qr hQr0 (le_trans hmono hQ)
  -- the power of N
  have hpow : (N : ℝ) ^ (-(x + ((2 * K + 1 : ℕ) : ℝ) - 1)) ≤ R / (N : ℝ) ^ (2 * K) := by
    have e : -(x + ((2 * K + 1 : ℕ) : ℝ) - 1) = -x + (-(((2 * K : ℕ) : ℝ))) := by push_cast; ring
    have hk : (N : ℝ) ^ (-(((2 * K : ℕ) : ℝ))) = ((N : ℝ) ^ (2 * K))⁻¹ := by
      rw [Real.rpow_neg hNR.le, Real.rpow_natCast]
    rw [e, Real.rpow_add hNR, hk, div_eq_mul_inv R]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    refine le_trans ?_ hR
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hden : xlo + 2 * K ≤ x + ((2 * K + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hCK := CK_nonneg K
  have hpn0 : 0 ≤ (N : ℝ) ^ (-(x + ((2 * K + 1 : ℕ) : ℝ) - 1)) := by positivity
  change CK K * ‖poch (sOfG x t) (2 * K + 1)‖ * (N : ℝ) ^ (-(x + ((2 * K + 1 : ℕ) : ℝ) - 1))
      / (x + ((2 * K + 1 : ℕ) : ℝ) - 1) ≤ _
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  calc CK K * ‖poch (sOfG x t) (2 * K + 1)‖ * (N : ℝ) ^ (-(x + ((2 * K + 1 : ℕ) : ℝ) - 1))
        / (x + ((2 * K + 1 : ℕ) : ℝ) - 1)
      ≤ CK K * Qr * (R / (N : ℝ) ^ (2 * K)) / (xlo + 2 * K) := by
        gcongr
    _ = CK K * Qr * R / (N : ℝ) ^ (2 * K) / (xlo + 2 * K) := by ring
