-- Prove2me | solution 1 for H1000Oct.piece_octX_pos
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:08:37.379904+00:00
-- url     : https://prove2.me/submissions/76e67d05-f397-47b3-8431-4533e4029518

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
import Theorems.Thm_H1000Oct_checkOct_sound
import Theorems.Thm_H1000Oct_emFinite_taylor_le_G
import Theorems.Thm_H1000Oct_norm_add_nat_le_abs
import Theorems.Thm_H1000Oct_norm_emCorr_le_norm
namespace ArbEcon
end ArbEcon
namespace ArbEcon.Off
end ArbEcon.Off
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
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



theorem Cp_nonneg (p : ℕ) : 0 ≤ Cp p := by unfold Cp; positivity



/-! ## T2. Shifting the exponent. -/





/-! ## T3. The Pochhammer symbol moves slowly. -/



/-! ## T4. The correction factor moves slowly. -/





/-! ## T5. The Taylor model of the finite part. -/









/-! ## T6. The order-(2K+1) remainder uniformly on a region. -/











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

namespace H1000Oct

open ArbEcon ArbEcon.Off

/-! ## A1. The correction factor, with `a ≤ ‖c - 1‖`. -/





/-! ## A2. The Taylor model for any real part of the center. -/



/-! ## B. The remainder along a horizontal segment, and the `G` certificate. -/









/-! ## C. The kernel check of a piece. -/



theorem octX_eq_octXv (kk : ℤ) (w : ℂ) :
    ArgHoriz.octX kk w = octXv (ArgHoriz.octA kk) (ArgHoriz.octB kk) w := rfl

/-- `|α Re w + β Im w| ≤ (|α| + |β|) ‖w‖`. -/
theorem abs_octXv_le (α β : ℤ) (w : ℂ) : |octXv α β w| ≤ (|(α : ℝ)| + |(β : ℝ)|) * ‖w‖ := by
  unfold octXv
  have h1 := Complex.abs_re_le_norm w
  have h2 := Complex.abs_im_le_norm w
  calc |(α : ℝ) * w.re + (β : ℝ) * w.im| ≤ |(α : ℝ) * w.re| + |(β : ℝ) * w.im| := abs_add_le _ _
    _ = |(α : ℝ)| * |w.re| + |(β : ℝ)| * |w.im| := by rw [abs_mul, abs_mul]
    _ ≤ |(α : ℝ)| * ‖w‖ + |(β : ℝ)| * ‖w‖ := by gcongr
    _ = (|(α : ℝ)| + |(β : ℝ)|) * ‖w‖ := by ring

/-- The projection is additive. -/
theorem octXv_add (α β : ℤ) (v w : ℂ) : octXv α β (v + w) = octXv α β v + octXv α β w := by
  unfold octXv; simp only [Complex.add_re, Complex.add_im]; ring



theorem octXv_sum (α β : ℤ) (s : Finset ℕ) (f : ℕ → ℝ) (W : ℕ → ℂ) :
    octXv α β (∑ k ∈ s, (f k : ℂ) * W k) = ∑ k ∈ s, f k * octXv α β (W k) := by
  unfold octXv
  rw [Complex.re_sum, Complex.im_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]; ring





















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

































/-! ## D. The piece. -/




theorem solution (c : Cfg) (o : OCfg) (σc tc : ℝ) (hσ : σc = ((o.a : ℝ) - o.b) / o.q)
    (ht : tc = (c.tn : ℝ) / 2 ^ c.tq) (K N p : ℕ) (hN : 2 ≤ N) (s1 s2 : StO)
    (h1 : InvO c σc tc (N - 1) s1) (h2 : InvO c σc tc N s2) (rn rd FN FD : ℕ) (kk : ℤ)
    (hchk : checkOct c o K N p s1.acc s2.acc rn rd FN FD kk = true)
    (R L a U G E : ℝ) (hrR : (rn : ℝ) / rd ≤ R) (hL : (s2.lhi : ℝ) ≤ L * 2 ^ c.P) (hRL : R * L ≤ 1)
    (ha : 0 < a) (hA : (a + R) ^ 2 ≤ (σc - 1) ^ 2 + tc ^ 2)
    (hU0 : 0 ≤ U) (hU : (|σc| + (2 * K - 1 : ℝ)) ^ 2 + tc ^ 2 ≤ U ^ 2)
    (hG : ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖(n : ℂ) ^ (-sOfG σc tc)‖ ≤ G)
    (hE : ∀ x : ℝ, |x - σc| ≤ (rn : ℝ) / rd →
      ‖riemannZeta (sOfG x tc) - emFinite K (sOfG x tc) N‖ ≤ E)
    (hbudget : G * (Cp p * (R * L) ^ (p + 1) * (((N : ℝ) - 1) + emcB K N a U)
        + 3 * corrVar K N R a U) + E ≤ (FN : ℝ) / FD) :
    ∀ x : ℝ, |x - σc| ≤ (rn : ℝ) / rd →
      0 < ArgHoriz.octX kk (riemannZeta ((x : ℂ) + (tc : ℂ) * I)) := by
  intro x hx
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hmain := checkOct_sound c o σc tc hσ ht K N p s1.acc s2.acc rn rd FN FD kk h1.2.2.2.2
    h2.2.2.2.2 hchk
  -- log N ≤ L
  have hlogN : Real.log N ≤ L := by
    have h2l := h2.2.2.2.1
    have : Real.log N * 2 ^ c.P ≤ L * 2 ^ c.P := le_trans h2l hL
    exact le_of_mul_le_mul_right this hP
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL0 : 0 ≤ L := le_trans (Real.log_nonneg hN1) hlogN
  set cc : ℂ := sOfG σc tc with hcc
  set h : ℂ := ((x - σc : ℝ) : ℂ) with hh
  have hs : cc + h = (x : ℂ) + (tc : ℂ) * I := by
    rw [hcc, hh]; simp only [sOfG]; push_cast; ring
  have hr0 : (0 : ℝ) ≤ (rn : ℝ) / rd := le_trans (abs_nonneg _) hx
  have hR0 : 0 ≤ R := le_trans hr0 hrR
  have hr : ‖h‖ ≤ R := by
    rw [hh, Complex.norm_real, Real.norm_eq_abs]; exact le_trans hx hrR
  -- a + R ≤ ‖c - 1‖
  have hc1sq : ‖cc - 1‖ ^ 2 = (σc - 1) ^ 2 + tc ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hcc]
    simp only [sOfG, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.one_re, Complex.one_im]
    ring
  have hc1 : a + R ≤ ‖cc - 1‖ :=
    le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _) (by rw [hc1sq]; exact hA)
  have hnc : a ≤ ‖cc - 1‖ := by linarith
  have hns : a ≤ ‖cc + h - 1‖ := by
    have : ‖cc - 1‖ ≤ ‖cc + h - 1‖ + ‖h‖ := by
      calc ‖cc - 1‖ = ‖(cc + h - 1) + (-h)‖ := by congr 1; ring
        _ ≤ ‖cc + h - 1‖ + ‖-h‖ := norm_add_le _ _
        _ = ‖cc + h - 1‖ + ‖h‖ := by rw [norm_neg]
    linarith
  have hUj := norm_add_nat_le_abs K σc tc U hU0 hU
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) (hG 1 le_rfl (by omega))
  -- the Taylor model at radius R
  have hT := emFinite_taylor_le_G K N p (by omega) cc h R L a U G hG hr hlogN hRL ha hnc hns hU0 hUj
  rw [hs] at hT
  have hemc := norm_emCorr_le_norm K N (by omega) cc a U ha hnc hU0 hUj
  have hTe : G * taylorErr K N p cc R L a U
      ≤ G * (Cp p * (R * L) ^ (p + 1) * (((N : ℝ) - 1) + emcB K N a U) + 3 * corrVar K N R a U) := by
    apply mul_le_mul_of_nonneg_left _ hG0
    unfold taylorErr
    have hcp := Cp_nonneg p
    have hRL0 : 0 ≤ R * L := mul_nonneg hR0 hL0
    have : Cp p * (R * L) ^ (p + 1) * (((N : ℝ) - 1) + ‖emCorr K cc N‖)
        ≤ Cp p * (R * L) ^ (p + 1) * (((N : ℝ) - 1) + emcB K N a U) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith
  have hEx := hE x hx
  have hsx : sOfG x tc = (x : ℂ) + (tc : ℂ) * I := rfl
  rw [hsx] at hEx
  set Pp := ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N cc k) with hPp
  have herr : ‖riemannZeta ((x : ℂ) + (tc : ℂ) * I) - Pp‖ ≤ (FN : ℝ) / FD := by
    have := norm_sub_le_norm_sub_add_norm_sub (riemannZeta ((x : ℂ) + (tc : ℂ) * I))
      (emFinite K ((x : ℂ) + (tc : ℂ) * I) N) Pp
    linarith
  -- the octant projection of the Taylor polynomial (h is real)
  set α := ArgHoriz.octA kk with hα
  set β := ArgHoriz.octB kk with hβ
  have hPpv : Pp = ∑ k ∈ Finset.range (p + 1),
      ((((x - σc) ^ k * ((-1) ^ k / (k ! : ℝ)) : ℝ)) : ℂ) * Wk K N cc k := by
    rw [hPp]
    apply Finset.sum_congr rfl
    intro k _
    rw [hh]; push_cast; ring
  have hoctP : octXv α β Pp = ∑ k ∈ Finset.range (p + 1),
      ((x - σc) ^ k * ((-1) ^ k / (k ! : ℝ))) * octXv α β (Wk K N cc k) := by
    rw [hPpv, octXv_sum]
  have hlow : octXv α β (Wk K N cc 0)
      - ∑ k ∈ Finset.Ico 1 (p + 1), |octXv α β (Wk K N cc k)| * ((rn : ℝ) / rd) ^ k / (k ! : ℝ)
      ≤ octXv α β Pp := by
    rw [hoctP, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p + 1)]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    have hrest : -(∑ k ∈ Finset.Ico 1 (p + 1), |octXv α β (Wk K N cc k)| * ((rn : ℝ) / rd) ^ k
          / (k ! : ℝ))
        ≤ ∑ k ∈ Finset.Ico 1 (p + 1), (x - σc) ^ k * ((-1) ^ k / (k ! : ℝ)) * octXv α β (Wk K N cc k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro k _
      have hF : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have habs : |(x - σc) ^ k * ((-1) ^ k / (k ! : ℝ)) * octXv α β (Wk K N cc k)|
          ≤ |octXv α β (Wk K N cc k)| * ((rn : ℝ) / rd) ^ k / (k ! : ℝ) := by
        rw [abs_mul, abs_mul, abs_div, abs_pow, abs_pow, abs_neg, abs_one, one_pow,
          abs_of_pos hF]
        have hpk : |x - σc| ^ k ≤ ((rn : ℝ) / rd) ^ k := pow_le_pow_left₀ (abs_nonneg _) hx k
        calc |x - σc| ^ k * (1 / (k ! : ℝ)) * |octXv α β (Wk K N cc k)|
            ≤ ((rn : ℝ) / rd) ^ k * (1 / (k ! : ℝ)) * |octXv α β (Wk K N cc k)| := by gcongr
          _ = |octXv α β (Wk K N cc k)| * ((rn : ℝ) / rd) ^ k / (k ! : ℝ) := by ring
      have := neg_abs_le ((x - σc) ^ k * ((-1) ^ k / (k ! : ℝ)) * octXv α β (Wk K N cc k))
      linarith
    linarith
  -- combine
  have hsplit : octXv α β (riemannZeta ((x : ℂ) + (tc : ℂ) * I))
      = octXv α β Pp + octXv α β (riemannZeta ((x : ℂ) + (tc : ℂ) * I) - Pp) := by
    rw [← octXv_add]; congr 1; ring
  have hproj := abs_octXv_le α β (riemannZeta ((x : ℂ) + (tc : ℂ) * I) - Pp)
  have hAB0 : 0 ≤ |(α : ℝ)| + |(β : ℝ)| := by positivity
  have hprojF : |octXv α β (riemannZeta ((x : ℂ) + (tc : ℂ) * I) - Pp)|
      ≤ (|(α : ℝ)| + |(β : ℝ)|) * ((FN : ℝ) / FD) :=
    le_trans hproj (mul_le_mul_of_nonneg_left herr hAB0)
  have hmain' : ∑ k ∈ Finset.Ico 1 (p + 1), |octXv α β (Wk K N cc k)| * ((rn : ℝ) / rd) ^ k
        / (k ! : ℝ) + (|(α : ℝ)| + |(β : ℝ)|) * ((FN : ℝ) / FD) < octXv α β (Wk K N cc 0) := by
    simpa only [octX_eq_octXv] using hmain
  rw [octX_eq_octXv, hsplit]
  have := neg_abs_le (octXv α β (riemannZeta ((x : ℂ) + (tc : ℂ) * I) - Pp))
  linarith
