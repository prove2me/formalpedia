-- Prove2me | solution 1 for MasulloRH.logDeriv_analytic_verified_region
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-22T14:38:02.873811+00:00
-- url     : https://prove2.me/submissions/8bb3a816-d8ca-4574-a8e0-e27cfd51b621

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e2_1e3
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e3_1e4
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e4_1e5
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

set_option autoImplicit false

open MasulloRH TaoFivePrimes
open scoped ComplexConjugate

private theorem nonzero_upper_band (s : ℂ) (hr : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 0 ≤ s.im) (hmax : s.im ≤ 100000) : riemannZeta s ≠ 0 := by
  have h0 : 0 < s.re := by linarith
  by_cases h6 : s.im ≤ 6
  · exact ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six h0 h1
      (by rwa [abs_of_nonneg him])
  by_cases h14 : s.im ≤ 14
  · exact zeta_ne_zero_strip_im_two_to_fourteen s h0 h1 (by linarith) h14
  intro hz
  apply hr.ne'
  by_cases h100 : s.im ≤ 10 ^ 2
  · exact rh_verified_block_14_1e2 s hz h0 h1 (le_of_not_ge h14) h100
  by_cases h1000 : s.im ≤ 10 ^ 3
  · exact rh_verified_block_1e2_1e3 s hz h0 h1 (le_of_not_ge h100) h1000
  by_cases h10000 : s.im ≤ 10 ^ 4
  · exact rh_verified_block_1e3_1e4 s hz h0 h1 (le_of_not_ge h1000) h10000
  exact rh_verified_block_1e4_1e5 s hz h0 h1 (le_of_not_ge h10000) (by norm_num; exact hmax)

theorem solution (s : ℂ) (hr : 1 / 2 < s.re) (hpole : s ≠ 1)
    (hregion : |s.im| ≤ 100000 ∨ 1 ≤ s.re) : AnalyticAt ℂ zetaLogDeriv s := by
  have ha := analyticOn_riemannZeta s hpole
  apply ha.deriv.div ha
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  have hheight := hregion.resolve_right h1
  rcases le_or_gt 0 s.im with him | him
  · exact nonzero_upper_band s hr (lt_of_not_ge h1) him ((le_abs_self _).trans hheight)
  intro hz
  have hc : riemannZeta (conj s) ≠ 0 :=
    nonzero_upper_band (conj s) hr (lt_of_not_ge h1)
      (by simpa using neg_nonneg.mpr him.le)
      (by simpa [abs_of_neg him] using hheight)
  exact hc (by rw [riemannZeta_conj, hz, map_zero])
