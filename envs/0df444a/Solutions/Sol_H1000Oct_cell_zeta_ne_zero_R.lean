-- Prove2me | solution 1 for H1000Oct.cell_zeta_ne_zero_R
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:20:38.011422+00:00
-- url     : https://prove2.me/submissions/cf7711ce-a46e-44a5-b6c1-4376fccebb0e

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
import Theorems.Thm_ArbEcon_Off_cell_zeta_ne_zero
import Theorems.Thm_H1000Oct_corrVar_mono
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

































/-! ## D. The piece. -/





/-! ## E. Helpers for the generated certificates. -/





/-- **Budget monotonicity** (slab cells): the error budget of `ArbEcon.Off.cell_zeta_ne_zero` at
    radius `r` is at most the budget at any `R ≥ r`. -/
theorem budget_mono (K N p : ℕ) (r R L a U X E : ℝ) (hr0 : 0 ≤ r) (hrR : r ≤ R) (hL0 : 0 ≤ L)
    (hU0 : 0 ≤ U) (hX : 0 ≤ X) :
    Cp p * (r * L) ^ (p + 1) * X + 3 * corrVar K N r a U + E
      ≤ Cp p * (R * L) ^ (p + 1) * X + 3 * corrVar K N R a U + E := by
  have hcp := Cp_nonneg p
  have h1 : (r * L) ^ (p + 1) ≤ (R * L) ^ (p + 1) :=
    pow_le_pow_left₀ (mul_nonneg hr0 hL0) (mul_le_mul_of_nonneg_right hrR hL0) _
  have h2 := corrVar_mono K N r R a U hr0 hrR hU0
  have h3 : Cp p * (r * L) ^ (p + 1) * X ≤ Cp p * (R * L) ^ (p + 1) * X := by gcongr
  linarith

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





/-! ## E. Helpers for the generated certificates. -/







/-! ## F. Closed forms for the generated budgets (K ≤ 6), and the slab-cell wrapper. -/










theorem solution (c : Cfg) (o : OCfg) (σc tc : ℝ) (hσ : σc = ((o.a : ℝ) - o.b) / o.q)
    (ht : tc = (c.tn : ℝ) / 2 ^ c.tq) (K N p : ℕ) (hK : 1 ≤ K) (hN : 2 ≤ N) (s1 s2 : StO)
    (h1 : InvO c σc tc (N - 1) s1) (h2 : InvO c σc tc N s2) (rn rd FN FD : ℕ)
    (hchk : checkCell c o K N p s1.acc s2.acc rn rd FN FD = true)
    (R L a U B Qr : ℝ) (r0 : ℕ) (hrR : (rn : ℝ) / rd ≤ R) (hL : (s2.lhi : ℝ) ≤ L * 2 ^ c.P)
    (hRL : R * L ≤ 1) (ha : 0 < a) (hta : a ≤ tc) (hσc : 0 ≤ σc) (hU0 : 0 ≤ U)
    (hU : (σc + (2 * K - 1 : ℝ)) ^ 2 + tc ^ 2 ≤ U ^ 2) (hQr0 : 0 ≤ Qr)
    (hQ : pochNormSq 1 B (2 * K + 1) ≤ Qr ^ 2) (hr0 : 0 < r0) (hr0N : r0 ^ 2 ≤ N)
    (hbudget : Cp p * (R * L) ^ (p + 1) * (((N : ℝ) - 1) + emcB K N a U)
        + 3 * corrVar K N R a U
        + CK K * Qr / ((N : ℝ) ^ (2 * K) * r0) / (((2 * K : ℕ) : ℝ) + 1 / 2) ≤ (FN : ℝ) / FD) :
    ∀ s : ℂ, ‖s - sOfG σc tc‖ ≤ (rn : ℝ) / rd → a ≤ s.im → s.im ≤ B → 1 / 2 ≤ s.re → s.re ≤ 1 →
      riemannZeta s ≠ 0 := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : Real.log N ≤ L := by
    have h2l := h2.2.2.2.1
    have : Real.log N * 2 ^ c.P ≤ L * 2 ^ c.P := le_trans h2l hL
    exact le_of_mul_le_mul_right this hP
  have hL0 : 0 ≤ L := le_trans (Real.log_nonneg hN1) hlogN
  have hr0' : (0 : ℝ) ≤ (rn : ℝ) / rd := by positivity
  have hrL : (rn : ℝ) / rd * L ≤ 1 := le_trans (mul_le_mul_of_nonneg_right hrR hL0) hRL
  have hX : 0 ≤ ((N : ℝ) - 1) + emcB K N a U := by
    unfold emcB
    have hsum : 0 ≤ ∑ i ∈ Finset.range (2 * K - 1), |(bernoulli (i + 2) : ℝ)| / ((i + 2)! : ℝ)
        * U ^ (i + 1) / (N : ℝ) ^ (i + 1) := by
      apply Finset.sum_nonneg; intro i _; positivity
    have : (0 : ℝ) ≤ (N : ℝ) / a := by positivity
    linarith
  have hb := budget_mono K N p ((rn : ℝ) / rd) R L a U (((N : ℝ) - 1) + emcB K N a U)
    (CK K * Qr / ((N : ℝ) ^ (2 * K) * r0) / (((2 * K : ℕ) : ℝ) + 1 / 2)) hr0' hrR hL0 hU0 hX
  exact cell_zeta_ne_zero c o σc tc hσ ht K N p hK hN s1 s2 h1 h2 rn rd FN FD hchk L a U B Qr r0 hL hrL
    ha hta hσc hU0 hU hQr0 hQ hr0 hr0N (le_trans hb hbudget)
